from __future__ import annotations

import ast
from dataclasses import asdict
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, TypeAlias

from pydantic import ValidationError
from urm_domain_digest import DigestDomainTools
from urm_domain_paper import PaperDomainTools
from urm_runtime.capability_policy import authorize_action
from urm_runtime.domain_registry import DomainToolRegistry
from urm_runtime.errors import URMError
from urm_runtime.events_tools import replay_events, validate_events
from urm_runtime.hashing import canonical_json, sha256_canonical_json
from urm_runtime.models import NormalizedEvent

DOMAIN_CONFORMANCE_SCHEMA = "domain_conformance@1"
URM_CONFORMANCE_REPORT_INVALID_CODE = "URM_CONFORMANCE_REPORT_INVALID"
URM_CONFORMANCE_RUNTIME_IMPORT_AUDIT_FAILED_CODE = "URM_CONFORMANCE_RUNTIME_IMPORT_AUDIT_FAILED"
_FIXED_TS = datetime(2026, 1, 1, 0, 0, 0, tzinfo=timezone.utc)
_RUNTIME_SOURCE_VERSION = "0.0.0"
_FORBIDDEN_IMPORT_PREFIXES: tuple[str, ...] = ("urm_domain_",)
DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELDS = frozenset(
    {
        "domain_conformance_hash",
        "hash_excluded_fields",
        "generated_at",
        "runtime_root_path",
        "missing_runtime_root_path",
        "operator_note",
    }
)
DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELD_LIST = tuple(
    sorted(DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELDS)
)
ToolRun: TypeAlias = tuple[str, dict[str, Any], dict[str, Any]]
DomainPack: TypeAlias = PaperDomainTools | DigestDomainTools
DomainRun: TypeAlias = tuple[str, str, DomainPack, list[ToolRun]]


class DomainConformanceError(ValueError):
    """Raised when domain conformance payloads fail deterministic validation."""

    def __init__(
        self,
        message: str,
        *,
        code: str = URM_CONFORMANCE_REPORT_INVALID_CODE,
    ) -> None:
        super().__init__(message)
        self.code = code


def _issue(
    *,
    code: str,
    message: str,
    context: dict[str, Any] | None = None,
    urm_code: str | None = None,
) -> dict[str, Any]:
    payload: dict[str, Any] = {"code": code, "message": message, "context": dict(context or {})}
    if urm_code is not None:
        payload["urm_code"] = urm_code
    return payload


def _default_runtime_root() -> Path:
    return Path(__file__).resolve().parents[4] / "packages" / "urm_runtime" / "src" / "urm_runtime"


def _resolve_runtime_root(*, runtime_root: Path | None) -> Path:
    if runtime_root is None:
        return _default_runtime_root().resolve()
    return runtime_root.resolve()


def _issue_sort_key(issue: dict[str, Any]) -> tuple[str, str, str]:
    raw_context = issue.get("context")
    if isinstance(raw_context, dict):
        context_payload: dict[str, Any] = dict(raw_context)
    else:
        context_payload = {}
    return (
        str(issue.get("code") or ""),
        canonical_json(context_payload),
        str(issue.get("message") or ""),
    )


def _sort_issues(issues: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return sorted(issues, key=_issue_sort_key)


def strip_nonsemantic_domain_conformance_fields(value: Any) -> Any:
    if isinstance(value, dict):
        normalized: dict[str, Any] = {}
        for raw_key, raw_value in sorted(value.items(), key=lambda item: str(item[0])):
            key = str(raw_key)
            if key in DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELDS:
                continue
            normalized[key] = strip_nonsemantic_domain_conformance_fields(raw_value)
        return normalized
    if isinstance(value, list):
        return [strip_nonsemantic_domain_conformance_fields(item) for item in value]
    return value


def domain_conformance_hash(payload: dict[str, Any]) -> str:
    semantic_payload = strip_nonsemantic_domain_conformance_fields(payload)
    return sha256_canonical_json(semantic_payload)


def validate_domain_conformance_report(payload: dict[str, Any]) -> None:
    if payload.get("schema") != DOMAIN_CONFORMANCE_SCHEMA:
        raise DomainConformanceError("payload schema must be domain_conformance@1")

    hash_excluded_fields = payload.get("hash_excluded_fields")
    if hash_excluded_fields is not None and hash_excluded_fields != list(
        DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELD_LIST
    ):
        raise DomainConformanceError("hash_excluded_fields does not match frozen exclusion set")

    domains = payload.get("domains")
    if not isinstance(domains, list):
        raise DomainConformanceError("domains must be an array")
    parsed_domains = [item for item in domains if isinstance(item, dict)]
    if len(parsed_domains) != len(domains):
        raise DomainConformanceError("domains must be objects")
    domain_order = [str(item.get("domain") or "") for item in parsed_domains]
    if domain_order != sorted(domain_order):
        raise DomainConformanceError("domains must be sorted by canonical domain key")

    issues = payload.get("issues")
    if not isinstance(issues, list):
        raise DomainConformanceError("issues must be an array")
    parsed_issues = [item for item in issues if isinstance(item, dict)]
    if len(parsed_issues) != len(issues):
        raise DomainConformanceError("issues must be objects")
    if parsed_issues != _sort_issues(parsed_issues):
        raise DomainConformanceError("issues must be canonical-sorted")

    embedded_hash = payload.get("domain_conformance_hash")
    if embedded_hash is not None:
        expected_hash = domain_conformance_hash(payload)
        if not isinstance(embedded_hash, str) or embedded_hash != expected_hash:
            raise DomainConformanceError("domain_conformance_hash mismatch")


def _event(
    *,
    seq: int,
    event_name: str,
    stream_id: str,
    tool_name: str,
    endpoint: str,
    run_id: str,
    error_code: str | None = None,
) -> NormalizedEvent:
    detail: dict[str, Any] = {"tool_name": tool_name}
    if error_code is not None:
        detail["error_code"] = error_code
    return NormalizedEvent(
        event=event_name,
        stream_id=stream_id,
        seq=seq,
        ts=_FIXED_TS + timedelta(seconds=seq),
        source={
            "component": "domain_conformance",
            "version": _RUNTIME_SOURCE_VERSION,
            "provider": "codex",
        },
        context={
            "run_id": run_id,
            "role": "copilot",
            "endpoint": endpoint,
        },
        detail=detail,
        event_kind=event_name,
        payload=detail,
    )


def _events_to_ndjson_lines(events: list[NormalizedEvent]) -> list[str]:
    lines: list[str] = []
    for event in events:
        payload = event.model_dump(mode="json", by_alias=True)
        lines.append(canonical_json(payload))
    return lines


def _run_paper_flow(pack: PaperDomainTools) -> list[tuple[str, dict[str, Any], dict[str, Any]]]:
    source_text = (
        "Portable runtimes need deterministic event streams. "
        "Policy traces improve auditability. "
        "This sentence is intentionally trimmed by extraction."
    )
    ingest_args = {"title": "Paper Fixture", "source_text": source_text}
    ingest, _ = pack.call_tool(tool_name="paper.ingest_text", arguments=ingest_args)
    extract, _ = pack.call_tool(
        tool_name="paper.extract_abstract_candidate",
        arguments={"source_text": source_text},
    )
    abstract_text = extract["abstract_text"]
    check, _ = pack.call_tool(
        tool_name="paper.check_constraints",
        arguments={"abstract_text": abstract_text, "min_words": 5, "max_words": 80},
    )
    emit, _ = pack.call_tool(
        tool_name="paper.emit_artifact",
        arguments={
            "title": "Paper Fixture",
            "abstract_text": abstract_text,
            "checks": check["checks"],
        },
    )
    return [
        ("paper.ingest_text", ingest_args, ingest),
        ("paper.extract_abstract_candidate", {"source_text": source_text}, extract),
        (
            "paper.check_constraints",
            {"abstract_text": abstract_text, "min_words": 5, "max_words": 80},
            check,
        ),
        (
            "paper.emit_artifact",
            {
                "title": "Paper Fixture",
                "abstract_text": abstract_text,
                "checks": check["checks"],
            },
            emit,
        ),
    ]


def _run_digest_flow(pack: DigestDomainTools) -> list[tuple[str, dict[str, Any], dict[str, Any]]]:
    source_text = (
        "Closed-world digest processing keeps conformance runs offline. "
        "Deterministic checks make replay reliable. "
        "Extra context can be ignored by sentence caps."
    )
    ingest_args = {"title": "Digest Fixture", "source_text": source_text}
    ingest, _ = pack.call_tool(tool_name="digest.ingest_text", arguments=ingest_args)
    extract_args = {"source_text": source_text, "max_sentences": 2, "max_words": 40}
    extract, _ = pack.call_tool(
        tool_name="digest.extract_digest_candidate",
        arguments=extract_args,
    )
    digest_text = extract["digest_text"]
    check_args = {
        "digest_text": digest_text,
        "min_words": 5,
        "max_words": 80,
        "max_sentences": 3,
    }
    check, _ = pack.call_tool(
        tool_name="digest.check_constraints",
        arguments=check_args,
    )
    emit_args = {
        "title": "Digest Fixture",
        "input_hash": ingest["input_hash"],
        "digest_text": digest_text,
        "policy_hash": "policy:conformance.v1",
        "checks": check["checks"],
        "evidence_refs": [{"kind": "event", "ref": "event:fixture#1"}],
    }
    emit, _ = pack.call_tool(
        tool_name="digest.emit_artifact",
        arguments=emit_args,
    )
    return [
        ("digest.ingest_text", ingest_args, ingest),
        ("digest.extract_digest_candidate", extract_args, extract),
        ("digest.check_constraints", check_args, check),
        ("digest.emit_artifact", emit_args, emit),
    ]


def _domain_event_checks(
    *,
    domain: str,
    tool_runs: list[ToolRun],
    events_dir: Path,
) -> dict[str, Any]:
    stream_id = f"conformance:{domain}"
    run_id = f"conformance-run:{domain}"
    endpoint = "urm.tool.call"
    events: list[NormalizedEvent] = []
    seq = 1
    for tool_name, _args, _result in tool_runs:
        events.append(
            _event(
                seq=seq,
                event_name="TOOL_CALL_START",
                stream_id=stream_id,
                tool_name=tool_name,
                endpoint=endpoint,
                run_id=run_id,
            )
        )
        seq += 1
        events.append(
            _event(
                seq=seq,
                event_name="TOOL_CALL_PASS",
                stream_id=stream_id,
                tool_name=tool_name,
                endpoint=endpoint,
                run_id=run_id,
            )
        )
        seq += 1

    lines = _events_to_ndjson_lines(events)
    events_path = events_dir / f"{domain}.ndjson"
    events_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    validation = validate_events(events_path, strict=True)
    replay_first = replay_events(events_path)
    replay_second = replay_events(events_path)
    return {
        "event_envelope": {
            "valid": validation["valid"] is True,
            "event_count": validation["event_count"],
            "stream_count": validation["stream_count"],
            "issue_count": len(validation["issues"]),
        },
        "replay_determinism": {
            "valid": replay_first == replay_second == lines,
            "line_count": len(lines),
        },
    }


def _policy_gating_checks(tool_names: list[str]) -> dict[str, Any]:
    allow_failures: list[str] = []
    deny_failures: list[str] = []
    for tool_name in tool_names:
        try:
            authorize_action(
                role="copilot",
                action=tool_name,
                writes_allowed=False,
                approval_provided=False,
                session_active=True,
            )
        except URMError:
            allow_failures.append(tool_name)

        try:
            authorize_action(
                role="pipeline_worker",
                action=tool_name,
                writes_allowed=False,
                approval_provided=False,
                session_active=True,
            )
            deny_failures.append(tool_name)
        except URMError as exc:
            if exc.detail.code != "URM_POLICY_DENIED":
                deny_failures.append(tool_name)
    return {
        "allow_valid": allow_failures == [],
        "deny_valid": deny_failures == [],
        "allow_failures": allow_failures,
        "deny_failures": deny_failures,
    }


def _error_taxonomy_checks(
    *,
    domain: str,
    ingest_tool: str,
    tool_pack: PaperDomainTools | DigestDomainTools,
) -> dict[str, Any]:
    unknown_code = ""
    policy_denied_code = ""
    invalid_argument_kind = ""

    try:
        tool_pack.call_tool(tool_name=f"{domain}.unknown_tool", arguments={})
    except URMError as exc:
        unknown_code = exc.detail.code

    try:
        authorize_action(
            role="pipeline_worker",
            action=ingest_tool,
            writes_allowed=False,
            approval_provided=False,
            session_active=True,
        )
    except URMError as exc:
        policy_denied_code = exc.detail.code

    try:
        tool_pack.call_tool(tool_name=ingest_tool, arguments={})
    except ValidationError:
        invalid_argument_kind = "ValidationError"
    except URMError as exc:
        invalid_argument_kind = exc.detail.code

    valid = (
        unknown_code == "URM_POLICY_DENIED"
        and policy_denied_code == "URM_POLICY_DENIED"
        and invalid_argument_kind == "ValidationError"
    )
    return {
        "valid": valid,
        "unknown_tool": {"code": unknown_code or "missing"},
        "policy_denied": {"code": policy_denied_code or "missing"},
        "invalid_argument": {"kind": invalid_argument_kind or "missing"},
    }


def _import_audit(*, runtime_root: Path | None = None) -> dict[str, Any]:
    resolved_runtime_root = _resolve_runtime_root(runtime_root=runtime_root)
    if not resolved_runtime_root.exists():
        return {
            "valid": False,
            "runtime_root_path": str(resolved_runtime_root),
            "missing_runtime_root_path": str(resolved_runtime_root),
            "offenders": [
                {
                    "module": "__runtime_root__",
                    "import": "missing_runtime_root",
                }
            ],
        }
    offenders: list[dict[str, str]] = []
    for path in sorted(resolved_runtime_root.rglob("*.py")):
        module_rel = path.relative_to(resolved_runtime_root).as_posix()
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name.startswith(_FORBIDDEN_IMPORT_PREFIXES):
                        offenders.append({"module": module_rel, "import": alias.name})
            elif isinstance(node, ast.ImportFrom):
                module = node.module or ""
                if module.startswith(_FORBIDDEN_IMPORT_PREFIXES):
                    offenders.append({"module": module_rel, "import": module})
    offenders = sorted(offenders, key=lambda item: (item["module"], item["import"]))
    return {
        "valid": offenders == [],
        "runtime_root_path": str(resolved_runtime_root),
        "offenders": offenders,
    }


def _registry_determinism() -> dict[str, Any]:
    digest = DigestDomainTools()
    paper = PaperDomainTools()

    forward = DomainToolRegistry.build(tool_packs=[paper, digest])
    reverse = DomainToolRegistry.build(tool_packs=[digest, paper])

    forward_payload = {
        "pack_metadata": [asdict(item) for item in forward.list_pack_metadata()],
        "tool_metadata": [asdict(item) for item in forward.list_tool_metadata()],
    }
    reverse_payload = {
        "pack_metadata": [asdict(item) for item in reverse.list_pack_metadata()],
        "tool_metadata": [asdict(item) for item in reverse.list_tool_metadata()],
    }

    return {
        "valid": canonical_json(forward_payload) == canonical_json(reverse_payload),
        "pack_count": len(forward_payload["pack_metadata"]),
        "tool_count": len(forward_payload["tool_metadata"]),
        "pack_order": [item["domain_pack_id"] for item in forward_payload["pack_metadata"]],
        "tool_order": [item["tool_name"] for item in forward_payload["tool_metadata"]],
    }


def build_domain_conformance(*, events_dir: Path, runtime_root: Path | None = None) -> dict[str, Any]:
    events_dir.mkdir(parents=True, exist_ok=True)
    registry = _registry_determinism()
    import_audit = _import_audit(runtime_root=runtime_root)

    domain_reports: list[dict[str, Any]] = []
    issues: list[dict[str, Any]] = []

    digest_pack = DigestDomainTools()
    paper_pack = PaperDomainTools()
    domain_runs: list[DomainRun] = [
        (
            "digest",
            "digest.ingest_text",
            digest_pack,
            _run_digest_flow(digest_pack),
        ),
        (
            "paper",
            "paper.ingest_text",
            paper_pack,
            _run_paper_flow(paper_pack),
        ),
    ]

    for domain, ingest_tool, pack, tool_runs in sorted(domain_runs, key=lambda item: item[0]):
        tool_names = [item[0] for item in tool_runs]
        event_checks = _domain_event_checks(
            domain=domain,
            tool_runs=tool_runs,
            events_dir=events_dir,
        )
        policy_checks = _policy_gating_checks(tool_names)
        error_checks = _error_taxonomy_checks(
            domain=domain,
            ingest_tool=ingest_tool,
            tool_pack=pack,
        )

        domain_valid = (
            event_checks["event_envelope"]["valid"]
            and event_checks["replay_determinism"]["valid"]
            and policy_checks["allow_valid"]
            and policy_checks["deny_valid"]
            and error_checks["valid"]
        )
        if not domain_valid:
            issues.append(
                _issue(
                    code="DOMAIN_CHECK_FAILED",
                    message="domain conformance checks failed",
                    context={"domain": domain},
                    urm_code=URM_CONFORMANCE_REPORT_INVALID_CODE,
                )
            )

        domain_reports.append(
            {
                "domain": domain,
                "tool_names": tool_names,
                "event_envelope": event_checks["event_envelope"],
                "replay_determinism": event_checks["replay_determinism"],
                "policy_gating": policy_checks,
                "error_taxonomy": error_checks,
                "valid": domain_valid,
            }
        )

    if not registry["valid"]:
        issues.append(
            _issue(
                code="REGISTRY_ORDER_NONDETERMINISTIC",
                message="domain tool registry metadata differs across registration permutations",
                urm_code=URM_CONFORMANCE_REPORT_INVALID_CODE,
            )
        )
    if not import_audit["valid"]:
        issues.append(
            _issue(
                code="RUNTIME_IMPORT_AUDIT_FAILED",
                message="urm_runtime imports domain-pack modules",
                context={"offender_count": len(import_audit["offenders"])},
                urm_code=URM_CONFORMANCE_RUNTIME_IMPORT_AUDIT_FAILED_CODE,
            )
        )

    report: dict[str, Any] = {
        "schema": DOMAIN_CONFORMANCE_SCHEMA,
        "valid": registry["valid"] and import_audit["valid"] and all(
            item["valid"] for item in domain_reports
        ),
        "registry_order_determinism": registry,
        "import_audit": import_audit,
        "domains": domain_reports,
        "issues": _sort_issues(issues),
        "hash_excluded_fields": list(DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELD_LIST),
    }
    report["domain_conformance_hash"] = domain_conformance_hash(report)
    validate_domain_conformance_report(report)
    return report
