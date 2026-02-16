from __future__ import annotations

import ast
import json
from dataclasses import asdict
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, TypeAlias

from adeu_explain import (
    EXPLAIN_DIFF_SCHEMA,
    ExplainDiffError,
    strip_nonsemantic_explain_fields,
    validate_explain_diff_packet,
)
from adeu_kernel import PROOF_EVIDENCE_SCHEMA, strip_nonsemantic_proof_fields
from adeu_semantic_depth import (
    SEMANTIC_DEPTH_SCHEMA,
    SemanticDepthError,
    strip_nonsemantic_semantic_depth_fields,
    validate_semantic_depth_report,
)
from pydantic import ValidationError
from urm_domain_digest import DigestDomainTools
from urm_domain_paper import PaperDomainTools
from urm_runtime.capability_policy import authorize_action
from urm_runtime.domain_registry import DomainToolRegistry
from urm_runtime.errors import URMError
from urm_runtime.events_tools import replay_events, validate_events
from urm_runtime.hashing import canonical_json, sha256_canonical_json
from urm_runtime.models import NormalizedEvent
from urm_runtime.policy_tools import (
    POLICY_LINEAGE_SCHEMA,
    strip_nonsemantic_policy_lineage_fields,
)

DOMAIN_CONFORMANCE_SCHEMA = "domain_conformance@1"
ARTIFACT_PARITY_FIXTURES_SCHEMA = "domain_conformance.artifact_parity_fixtures@1"
VNEXT_PLUS11_MANIFEST_SCHEMA = "stop_gate.vnext_plus11_manifest@1"
URM_CONFORMANCE_REPORT_INVALID_CODE = "URM_CONFORMANCE_REPORT_INVALID"
URM_CONFORMANCE_RUNTIME_IMPORT_AUDIT_FAILED_CODE = "URM_CONFORMANCE_RUNTIME_IMPORT_AUDIT_FAILED"
URM_CONFORMANCE_ARTIFACT_PARITY_MISMATCH_CODE = "URM_CONFORMANCE_ARTIFACT_PARITY_MISMATCH"
URM_CONFORMANCE_ARTIFACT_REF_INVALID_CODE = "URM_CONFORMANCE_ARTIFACT_REF_INVALID"
URM_CONFORMANCE_PROJECTION_UNSUPPORTED_CODE = "URM_CONFORMANCE_PROJECTION_UNSUPPORTED"
URM_CONFORMANCE_MANIFEST_HASH_MISMATCH_CODE = "URM_CONFORMANCE_MANIFEST_HASH_MISMATCH"
URM_CONFORMANCE_FIXTURE_INVALID_CODE = "URM_CONFORMANCE_FIXTURE_INVALID"
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
ArtifactParityFixture: TypeAlias = dict[str, str]
CoverageEntry: TypeAlias = dict[str, Any]


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


def _discover_repo_root(anchor: Path) -> Path | None:
    resolved = anchor.resolve()
    for parent in [resolved, *resolved.parents]:
        if (parent / ".git").exists():
            return parent
    return None


def _default_artifact_parity_fixtures_path() -> Path | None:
    repo_root = _discover_repo_root(Path(__file__).resolve())
    if repo_root is None:
        return None
    candidate = (
        repo_root
        / "apps"
        / "api"
        / "fixtures"
        / "stop_gate"
        / "vnext_plus11_artifact_parity_fixtures.json"
    )
    return candidate if candidate.exists() else None


def _default_vnext_plus11_manifest_path() -> Path | None:
    repo_root = _discover_repo_root(Path(__file__).resolve())
    if repo_root is None:
        return None
    candidate = (
        repo_root
        / "apps"
        / "api"
        / "fixtures"
        / "stop_gate"
        / "vnext_plus11_manifest.json"
    )
    return candidate if candidate.exists() else None


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


def _legacy_issue_code_for_urm(*, urm_code: str) -> str:
    mapping = {
        URM_CONFORMANCE_ARTIFACT_PARITY_MISMATCH_CODE: "ARTIFACT_PARITY_MISMATCH",
        URM_CONFORMANCE_ARTIFACT_REF_INVALID_CODE: "ARTIFACT_PARITY_REF_INVALID",
        URM_CONFORMANCE_PROJECTION_UNSUPPORTED_CODE: "ARTIFACT_PARITY_PROJECTION_UNSUPPORTED",
        URM_CONFORMANCE_MANIFEST_HASH_MISMATCH_CODE: "CONFORMANCE_MANIFEST_HASH_MISMATCH",
        URM_CONFORMANCE_FIXTURE_INVALID_CODE: "ARTIFACT_PARITY_FIXTURE_INVALID",
        URM_CONFORMANCE_RUNTIME_IMPORT_AUDIT_FAILED_CODE: "RUNTIME_IMPORT_AUDIT_FAILED",
        URM_CONFORMANCE_REPORT_INVALID_CODE: "CONFORMANCE_REPORT_INVALID",
    }
    return mapping.get(urm_code, "CONFORMANCE_CHECK_FAILED")


def _read_json_object(path: Path, *, description: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise DomainConformanceError(
            f"{description} is not readable",
            code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
        ) from exc
    except json.JSONDecodeError as exc:
        raise DomainConformanceError(
            f"{description} is invalid JSON",
            code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
        ) from exc
    if not isinstance(payload, dict):
        raise DomainConformanceError(
            f"{description} must be a JSON object",
            code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
        )
    return payload


def _load_artifact_parity_fixtures(
    *,
    fixtures_path: Path,
) -> list[ArtifactParityFixture]:
    payload = _read_json_object(fixtures_path, description="artifact parity fixtures")
    if payload.get("schema") != ARTIFACT_PARITY_FIXTURES_SCHEMA:
        raise DomainConformanceError(
            "artifact parity fixtures has unsupported schema",
            code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
        )
    raw_fixtures = payload.get("fixtures")
    if not isinstance(raw_fixtures, list):
        raise DomainConformanceError(
            "artifact parity fixtures must include fixtures[]",
            code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
        )

    fixtures: list[ArtifactParityFixture] = []
    seen_fixture_ids: set[str] = set()
    for idx, candidate in enumerate(raw_fixtures):
        if not isinstance(candidate, dict):
            raise DomainConformanceError(
                f"artifact parity fixtures[{idx}] must be an object",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        fixture_id = str(candidate.get("fixture_id") or "").strip()
        artifact_schema = str(candidate.get("artifact_schema") or "").strip()
        left_ref = str(candidate.get("left_ref") or "").strip()
        right_ref = str(candidate.get("right_ref") or "").strip()
        if not fixture_id or not artifact_schema or not left_ref or not right_ref:
            raise DomainConformanceError(
                f"artifact parity fixtures[{idx}] is missing required fields",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        if fixture_id in seen_fixture_ids:
            raise DomainConformanceError(
                f"artifact parity fixture_id must be unique: {fixture_id}",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        seen_fixture_ids.add(fixture_id)
        fixture: ArtifactParityFixture = {
            "fixture_id": fixture_id,
            "artifact_schema": artifact_schema,
            "left_ref": left_ref,
            "right_ref": right_ref,
        }
        notes = candidate.get("notes")
        if isinstance(notes, str) and notes.strip():
            fixture["notes"] = notes.strip()
        fixtures.append(fixture)
    return sorted(fixtures, key=lambda item: item["fixture_id"])


def _resolve_parity_fixture_ref_path(
    *,
    raw_ref: str,
    fixtures_path: Path,
    artifact_fixture_root: Path | None,
) -> Path:
    ref = str(raw_ref).strip()
    if not ref:
        raise DomainConformanceError(
            "artifact parity fixture ref must not be empty",
            code=URM_CONFORMANCE_ARTIFACT_REF_INVALID_CODE,
        )
    if ref.startswith("event:"):
        raise DomainConformanceError(
            "event refs are unsupported for artifact parity fixture payloads",
            code=URM_CONFORMANCE_ARTIFACT_REF_INVALID_CODE,
        )
    if ref.startswith("artifact:"):
        artifact_id = ref.removeprefix("artifact:")
        candidate_roots: list[Path] = [fixtures_path.parent.resolve()]
        if artifact_fixture_root is not None:
            candidate_roots.insert(0, artifact_fixture_root.resolve())
        for root in candidate_roots:
            for candidate in (root / artifact_id, root / f"{artifact_id}.json"):
                if candidate.exists() and candidate.is_file():
                    return candidate.resolve()
        raise DomainConformanceError(
            f"unresolved artifact fixture ref: {ref}",
            code=URM_CONFORMANCE_ARTIFACT_REF_INVALID_CODE,
        )

    path = Path(ref)
    if not path.is_absolute():
        path = (fixtures_path.parent / path).resolve()
    if not path.exists() or not path.is_file():
        raise DomainConformanceError(
            f"artifact parity fixture path not found: {ref}",
            code=URM_CONFORMANCE_ARTIFACT_REF_INVALID_CODE,
        )
    return path


def _semantic_projection_for_artifact_schema(
    *,
    artifact_schema: str,
    payload: dict[str, Any],
) -> Any:
    if artifact_schema == POLICY_LINEAGE_SCHEMA:
        if payload.get("schema") != POLICY_LINEAGE_SCHEMA:
            raise DomainConformanceError(
                "policy_lineage parity fixture has mismatched schema",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        return strip_nonsemantic_policy_lineage_fields(payload)
    if artifact_schema == PROOF_EVIDENCE_SCHEMA:
        if payload.get("schema") != PROOF_EVIDENCE_SCHEMA:
            raise DomainConformanceError(
                "proof_evidence parity fixture has mismatched schema",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        return strip_nonsemantic_proof_fields(payload)
    if artifact_schema == EXPLAIN_DIFF_SCHEMA:
        if payload.get("schema") != EXPLAIN_DIFF_SCHEMA:
            raise DomainConformanceError(
                "explain_diff parity fixture has mismatched schema",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        try:
            validate_explain_diff_packet(payload)
        except ExplainDiffError as exc:
            raise DomainConformanceError(
                "explain_diff parity fixture failed validation",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            ) from exc
        return strip_nonsemantic_explain_fields(payload)
    if artifact_schema == SEMANTIC_DEPTH_SCHEMA:
        if payload.get("schema") != SEMANTIC_DEPTH_SCHEMA:
            raise DomainConformanceError(
                "semantic_depth_report parity fixture has mismatched schema",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        try:
            validate_semantic_depth_report(payload)
        except SemanticDepthError as exc:
            raise DomainConformanceError(
                "semantic_depth_report parity fixture failed validation",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            ) from exc
        return strip_nonsemantic_semantic_depth_fields(payload)

    raise DomainConformanceError(
        f"artifact parity projection unsupported for schema: {artifact_schema}",
        code=URM_CONFORMANCE_PROJECTION_UNSUPPORTED_CODE,
    )


def _build_artifact_parity_checks(
    *,
    fixtures_path: Path,
    artifact_fixture_root: Path | None,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    fixtures = _load_artifact_parity_fixtures(fixtures_path=fixtures_path)
    issues: list[dict[str, Any]] = []
    fixture_results: list[dict[str, Any]] = []
    for fixture in fixtures:
        fixture_id = fixture["fixture_id"]
        artifact_schema = fixture["artifact_schema"]
        left_ref = fixture["left_ref"]
        right_ref = fixture["right_ref"]
        result: dict[str, Any] = {
            "fixture_id": fixture_id,
            "artifact_schema": artifact_schema,
            "left_ref": left_ref,
            "right_ref": right_ref,
        }
        notes = fixture.get("notes")
        if notes is not None:
            result["notes"] = notes
        try:
            left_path = _resolve_parity_fixture_ref_path(
                raw_ref=left_ref,
                fixtures_path=fixtures_path,
                artifact_fixture_root=artifact_fixture_root,
            )
            right_path = _resolve_parity_fixture_ref_path(
                raw_ref=right_ref,
                fixtures_path=fixtures_path,
                artifact_fixture_root=artifact_fixture_root,
            )
            left_payload = _read_json_object(
                left_path,
                description=f"artifact parity left payload ({fixture_id})",
            )
            right_payload = _read_json_object(
                right_path,
                description=f"artifact parity right payload ({fixture_id})",
            )
            left_projection = _semantic_projection_for_artifact_schema(
                artifact_schema=artifact_schema,
                payload=left_payload,
            )
            right_projection = _semantic_projection_for_artifact_schema(
                artifact_schema=artifact_schema,
                payload=right_payload,
            )
            left_hash = sha256_canonical_json(left_projection)
            right_hash = sha256_canonical_json(right_projection)
            result["semantic_hash_left"] = left_hash
            result["semantic_hash_right"] = right_hash
            result["valid"] = left_hash == right_hash
            if result["valid"] is not True:
                issues.append(
                    _issue(
                        code=_legacy_issue_code_for_urm(
                            urm_code=URM_CONFORMANCE_ARTIFACT_PARITY_MISMATCH_CODE
                        ),
                        message="artifact parity semantic projection mismatch",
                        context={
                            "artifact_schema": artifact_schema,
                            "fixture_id": fixture_id,
                            "left_ref": left_ref,
                            "right_ref": right_ref,
                        },
                        urm_code=URM_CONFORMANCE_ARTIFACT_PARITY_MISMATCH_CODE,
                    )
                )
        except DomainConformanceError as exc:
            result["valid"] = False
            result["error_code"] = exc.code
            issues.append(
                _issue(
                    code=_legacy_issue_code_for_urm(urm_code=exc.code),
                    message=str(exc),
                    context={
                        "artifact_schema": artifact_schema,
                        "fixture_id": fixture_id,
                        "left_ref": left_ref,
                        "right_ref": right_ref,
                    },
                    urm_code=exc.code,
                )
            )
        fixture_results.append(result)

    report = {
        "valid": all(item.get("valid") is True for item in fixture_results),
        "fixture_count": len(fixtures),
        "evaluated_count": len(fixture_results),
        "fixtures": fixture_results,
    }
    return report, issues


def _pct(passed: int, total: int) -> float:
    if total <= 0:
        return 0.0
    return round((float(passed) * 100.0) / float(total), 6)


def _load_vnext_plus11_coverage_manifest(
    *,
    manifest_path: Path,
) -> tuple[list[CoverageEntry], str]:
    payload = _read_json_object(manifest_path, description="vnext+11 coverage manifest")
    if payload.get("schema") != VNEXT_PLUS11_MANIFEST_SCHEMA:
        raise DomainConformanceError(
            "vnext+11 coverage manifest has unsupported schema",
            code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
        )
    raw_coverage = payload.get("coverage")
    if not isinstance(raw_coverage, list):
        raise DomainConformanceError(
            "vnext+11 coverage manifest must include coverage[]",
            code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
        )
    coverage_entries: list[CoverageEntry] = []
    seen_surface_ids: set[str] = set()
    for idx, candidate in enumerate(raw_coverage):
        if not isinstance(candidate, dict):
            raise DomainConformanceError(
                f"vnext+11 coverage[{idx}] must be an object",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        surface_id = str(candidate.get("surface_id") or "").strip()
        if not surface_id:
            raise DomainConformanceError(
                f"vnext+11 coverage[{idx}] surface_id must be non-empty",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        if surface_id in seen_surface_ids:
            raise DomainConformanceError(
                f"vnext+11 coverage surface_id must be unique: {surface_id}",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        seen_surface_ids.add(surface_id)
        raw_fixture_ids = candidate.get("fixture_ids")
        if not isinstance(raw_fixture_ids, list) or not raw_fixture_ids:
            raise DomainConformanceError(
                f"vnext+11 coverage[{idx}] fixture_ids must be a non-empty array",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        fixture_ids = [str(item).strip() for item in raw_fixture_ids if str(item).strip()]
        if len(fixture_ids) != len(raw_fixture_ids):
            raise DomainConformanceError(
                f"vnext+11 coverage[{idx}] fixture_ids must be non-empty strings",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        if fixture_ids != sorted(fixture_ids):
            raise DomainConformanceError(
                f"vnext+11 coverage[{idx}] fixture_ids must be sorted",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )
        if len(set(fixture_ids)) != len(fixture_ids):
            raise DomainConformanceError(
                f"vnext+11 coverage[{idx}] fixture_ids must be unique",
                code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
            )

        entry: CoverageEntry = {"surface_id": surface_id, "fixture_ids": fixture_ids}
        raw_pressure_test = candidate.get("pressure_test")
        if raw_pressure_test is not None:
            if not isinstance(raw_pressure_test, bool):
                raise DomainConformanceError(
                    f"vnext+11 coverage[{idx}] pressure_test must be boolean when present",
                    code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
                )
            if raw_pressure_test:
                entry["pressure_test"] = True
        coverage_entries.append(entry)

    coverage_entries = sorted(coverage_entries, key=lambda item: str(item["surface_id"]))

    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise DomainConformanceError(
            "vnext+11 coverage manifest missing manifest_hash",
            code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
        )
    hash_basis = dict(payload)
    hash_basis.pop("manifest_hash", None)
    recomputed_manifest_hash = sha256_canonical_json(hash_basis)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise DomainConformanceError(
            "vnext+11 coverage manifest_hash mismatch",
            code=URM_CONFORMANCE_MANIFEST_HASH_MISMATCH_CODE,
        )

    return coverage_entries, recomputed_manifest_hash


def _build_surface_fixture_statuses(
    *,
    registry: dict[str, Any],
    import_audit: dict[str, Any],
    domain_reports: list[dict[str, Any]],
    artifact_parity: dict[str, Any] | None,
) -> dict[str, dict[str, bool]]:
    statuses: dict[str, dict[str, bool]] = {
        "runtime.import_audit": {
            "runtime.import_audit": bool(import_audit.get("valid") is True),
        },
        "runtime.registry_order_determinism": {
            "runtime.registry_order_determinism": bool(registry.get("valid") is True),
        },
    }

    for domain_report in domain_reports:
        domain = str(domain_report.get("domain") or "").strip()
        if not domain:
            continue
        fixture_id = f"domain.{domain}"
        event_envelope = domain_report.get("event_envelope")
        replay_determinism = domain_report.get("replay_determinism")
        policy_gating = domain_report.get("policy_gating")
        error_taxonomy = domain_report.get("error_taxonomy")
        statuses[f"domain.{domain}.event_envelope"] = {
            fixture_id: isinstance(event_envelope, dict) and event_envelope.get("valid") is True
        }
        statuses[f"domain.{domain}.replay_determinism"] = {
            fixture_id: isinstance(replay_determinism, dict)
            and replay_determinism.get("valid") is True
        }
        statuses[f"domain.{domain}.policy_gating"] = {
            fixture_id: isinstance(policy_gating, dict)
            and policy_gating.get("allow_valid") is True
            and policy_gating.get("deny_valid") is True
        }
        statuses[f"domain.{domain}.error_taxonomy"] = {
            fixture_id: isinstance(error_taxonomy, dict) and error_taxonomy.get("valid") is True
        }

    if isinstance(artifact_parity, dict):
        parity_fixtures = artifact_parity.get("fixtures")
        if isinstance(parity_fixtures, list):
            parity_statuses: dict[str, bool] = {}
            for item in parity_fixtures:
                if not isinstance(item, dict):
                    continue
                fixture_id = str(item.get("fixture_id") or "").strip()
                if not fixture_id:
                    continue
                parity_statuses[fixture_id] = item.get("valid") is True
            if parity_statuses:
                statuses["conformance.artifact_parity"] = dict(
                    sorted(parity_statuses.items(), key=lambda item: item[0])
                )
    return statuses


def _build_coverage_checks(
    *,
    manifest_path: Path,
    registry: dict[str, Any],
    import_audit: dict[str, Any],
    domain_reports: list[dict[str, Any]],
    artifact_parity: dict[str, Any] | None,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    coverage_entries, manifest_hash = _load_vnext_plus11_coverage_manifest(
        manifest_path=manifest_path
    )
    available_statuses = _build_surface_fixture_statuses(
        registry=registry,
        import_audit=import_audit,
        domain_reports=domain_reports,
        artifact_parity=artifact_parity,
    )
    issues: list[dict[str, Any]] = []
    entry_reports: list[dict[str, Any]] = []
    for entry in coverage_entries:
        surface_id = str(entry["surface_id"])
        fixture_ids = [str(item) for item in entry["fixture_ids"]]
        entry_report: dict[str, Any] = {
            "surface_id": surface_id,
            "fixture_ids": fixture_ids,
        }
        if entry.get("pressure_test") is True:
            entry_report["pressure_test"] = True

        surface_status = available_statuses.get(surface_id)
        if surface_status is None:
            entry_report["valid"] = False
            entry_report["error_code"] = URM_CONFORMANCE_FIXTURE_INVALID_CODE
            issues.append(
                _issue(
                    code=_legacy_issue_code_for_urm(urm_code=URM_CONFORMANCE_FIXTURE_INVALID_CODE),
                    message="coverage surface is not available in domain conformance report",
                    context={"surface_id": surface_id},
                    urm_code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
                )
            )
            entry_reports.append(entry_report)
            continue

        missing_fixture_ids = sorted(
            fixture_id for fixture_id in fixture_ids if fixture_id not in surface_status
        )
        if missing_fixture_ids:
            entry_report["valid"] = False
            entry_report["error_code"] = URM_CONFORMANCE_FIXTURE_INVALID_CODE
            entry_report["missing_fixture_ids"] = missing_fixture_ids
            issues.append(
                _issue(
                    code=_legacy_issue_code_for_urm(urm_code=URM_CONFORMANCE_FIXTURE_INVALID_CODE),
                    message="coverage fixture_ids are unresolved for surface",
                    context={
                        "surface_id": surface_id,
                        "missing_fixture_ids": missing_fixture_ids,
                    },
                    urm_code=URM_CONFORMANCE_FIXTURE_INVALID_CODE,
                )
            )
            entry_reports.append(entry_report)
            continue

        entry_report["valid"] = all(surface_status[fixture_id] for fixture_id in fixture_ids)
        if entry_report["valid"] is not True:
            issues.append(
                _issue(
                    code="CONFORMANCE_COVERAGE_FAILED",
                    message="coverage entry did not satisfy fixture checks",
                    context={"surface_id": surface_id, "fixture_ids": fixture_ids},
                    urm_code=URM_CONFORMANCE_REPORT_INVALID_CODE,
                )
            )
        entry_reports.append(entry_report)

    covered_surface_count = sum(1 for entry in entry_reports if entry.get("valid") is True)
    coverage_report = {
        "manifest_schema": VNEXT_PLUS11_MANIFEST_SCHEMA,
        "manifest_hash": manifest_hash,
        "valid": all(entry.get("valid") is True for entry in entry_reports),
        "surface_count": len(entry_reports),
        "covered_surface_count": covered_surface_count,
        "coverage_pct": _pct(covered_surface_count, len(entry_reports)),
        "entries": entry_reports,
    }
    return coverage_report, issues


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
    for idx in range(len(parsed_domains) - 1):
        current_domain = str(parsed_domains[idx].get("domain") or "")
        next_domain = str(parsed_domains[idx + 1].get("domain") or "")
        if current_domain > next_domain:
            raise DomainConformanceError("domains must be sorted by canonical domain key")

    artifact_parity = payload.get("artifact_parity")
    if artifact_parity is not None:
        if not isinstance(artifact_parity, dict):
            raise DomainConformanceError("artifact_parity must be an object")
        if not isinstance(artifact_parity.get("valid"), bool):
            raise DomainConformanceError("artifact_parity.valid must be boolean")
        if not isinstance(artifact_parity.get("fixture_count"), int):
            raise DomainConformanceError("artifact_parity.fixture_count must be integer")
        if not isinstance(artifact_parity.get("evaluated_count"), int):
            raise DomainConformanceError("artifact_parity.evaluated_count must be integer")
        if artifact_parity["fixture_count"] < 0:
            raise DomainConformanceError("artifact_parity.fixture_count must be non-negative")
        if artifact_parity["evaluated_count"] < 0:
            raise DomainConformanceError("artifact_parity.evaluated_count must be non-negative")

        raw_fixtures = artifact_parity.get("fixtures")
        if not isinstance(raw_fixtures, list):
            raise DomainConformanceError("artifact_parity.fixtures must be an array")
        parsed_fixtures = [item for item in raw_fixtures if isinstance(item, dict)]
        if len(parsed_fixtures) != len(raw_fixtures):
            raise DomainConformanceError("artifact_parity.fixtures entries must be objects")
        if artifact_parity["fixture_count"] != len(parsed_fixtures):
            raise DomainConformanceError(
                "artifact_parity.fixture_count must match fixtures length"
            )
        if artifact_parity["evaluated_count"] != len(parsed_fixtures):
            raise DomainConformanceError(
                "artifact_parity.evaluated_count must match fixtures length"
            )
        fixture_ids = [str(item.get("fixture_id") or "") for item in parsed_fixtures]
        if any(not fixture_id for fixture_id in fixture_ids):
            raise DomainConformanceError("artifact_parity.fixtures fixture_id must be non-empty")
        if fixture_ids != sorted(fixture_ids):
            raise DomainConformanceError("artifact_parity.fixtures must be sorted by fixture_id")
        if len(set(fixture_ids)) != len(fixture_ids):
            raise DomainConformanceError("artifact_parity.fixtures fixture_id must be unique")

    coverage = payload.get("coverage")
    if coverage is not None:
        if not isinstance(coverage, dict):
            raise DomainConformanceError("coverage must be an object")
        if coverage.get("manifest_schema") != VNEXT_PLUS11_MANIFEST_SCHEMA:
            raise DomainConformanceError("coverage.manifest_schema must match vnext+11 schema")
        manifest_hash = coverage.get("manifest_hash")
        if not isinstance(manifest_hash, str) or not manifest_hash:
            raise DomainConformanceError("coverage.manifest_hash must be a non-empty string")
        if not isinstance(coverage.get("valid"), bool):
            raise DomainConformanceError("coverage.valid must be boolean")
        if not isinstance(coverage.get("surface_count"), int):
            raise DomainConformanceError("coverage.surface_count must be integer")
        if not isinstance(coverage.get("covered_surface_count"), int):
            raise DomainConformanceError("coverage.covered_surface_count must be integer")
        if not isinstance(coverage.get("coverage_pct"), (float, int)):
            raise DomainConformanceError("coverage.coverage_pct must be numeric")
        if coverage["surface_count"] < 0:
            raise DomainConformanceError("coverage.surface_count must be non-negative")
        if coverage["covered_surface_count"] < 0:
            raise DomainConformanceError("coverage.covered_surface_count must be non-negative")
        if coverage["covered_surface_count"] > coverage["surface_count"]:
            raise DomainConformanceError(
                "coverage.covered_surface_count cannot exceed coverage.surface_count"
            )

        raw_entries = coverage.get("entries")
        if not isinstance(raw_entries, list):
            raise DomainConformanceError("coverage.entries must be an array")
        parsed_entries = [item for item in raw_entries if isinstance(item, dict)]
        if len(parsed_entries) != len(raw_entries):
            raise DomainConformanceError("coverage.entries must contain objects")
        if coverage["surface_count"] != len(parsed_entries):
            raise DomainConformanceError("coverage.surface_count must match entries length")
        surface_ids = [str(item.get("surface_id") or "") for item in parsed_entries]
        if any(not surface_id for surface_id in surface_ids):
            raise DomainConformanceError("coverage.entries surface_id must be non-empty")
        if surface_ids != sorted(surface_ids):
            raise DomainConformanceError("coverage.entries must be sorted by surface_id")
        if len(set(surface_ids)) != len(surface_ids):
            raise DomainConformanceError("coverage.entries surface_id must be unique")
        for entry in parsed_entries:
            fixture_ids = entry.get("fixture_ids")
            if not isinstance(fixture_ids, list) or not fixture_ids:
                raise DomainConformanceError(
                    "coverage.entries fixture_ids must be a non-empty array"
                )
            normalized_fixture_ids = [
                str(item).strip() for item in fixture_ids if str(item).strip()
            ]
            if len(normalized_fixture_ids) != len(fixture_ids):
                raise DomainConformanceError(
                    "coverage.entries fixture_ids must contain non-empty strings"
                )
            if normalized_fixture_ids != sorted(normalized_fixture_ids):
                raise DomainConformanceError("coverage.entries fixture_ids must be sorted")
            if len(set(normalized_fixture_ids)) != len(normalized_fixture_ids):
                raise DomainConformanceError("coverage.entries fixture_ids must be unique")
            if not isinstance(entry.get("valid"), bool):
                raise DomainConformanceError("coverage.entries valid must be boolean")
            if "pressure_test" in entry and not isinstance(entry.get("pressure_test"), bool):
                raise DomainConformanceError("coverage.entries pressure_test must be boolean")
        expected_covered_surface_count = sum(
            1 for item in parsed_entries if item.get("valid") is True
        )
        if coverage["covered_surface_count"] != expected_covered_surface_count:
            raise DomainConformanceError(
                "coverage.covered_surface_count must match valid coverage entries"
            )
        expected_coverage_pct = _pct(expected_covered_surface_count, len(parsed_entries))
        if round(float(coverage["coverage_pct"]), 6) != expected_coverage_pct:
            raise DomainConformanceError("coverage.coverage_pct is inconsistent with entries")

    issues = payload.get("issues")
    if not isinstance(issues, list):
        raise DomainConformanceError("issues must be an array")
    parsed_issues = [item for item in issues if isinstance(item, dict)]
    if len(parsed_issues) != len(issues):
        raise DomainConformanceError("issues must be objects")
    for idx in range(len(parsed_issues) - 1):
        if _issue_sort_key(parsed_issues[idx]) > _issue_sort_key(parsed_issues[idx + 1]):
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


def build_domain_conformance(
    *,
    events_dir: Path,
    runtime_root: Path | None = None,
    artifact_parity_fixtures_path: Path | None = None,
    artifact_fixture_root: Path | None = None,
    coverage_manifest_path: Path | None = None,
) -> dict[str, Any]:
    events_dir.mkdir(parents=True, exist_ok=True)
    registry = _registry_determinism()
    import_audit = _import_audit(runtime_root=runtime_root)
    resolved_parity_fixtures_path = (
        artifact_parity_fixtures_path.resolve()
        if artifact_parity_fixtures_path is not None
        else _default_artifact_parity_fixtures_path()
    )
    resolved_coverage_manifest_path = (
        coverage_manifest_path.resolve()
        if coverage_manifest_path is not None
        else _default_vnext_plus11_manifest_path()
    )

    domain_reports: list[dict[str, Any]] = []
    issues: list[dict[str, Any]] = []
    artifact_parity: dict[str, Any] | None = None
    coverage: dict[str, Any] | None = None

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
    if resolved_parity_fixtures_path is not None:
        try:
            artifact_parity, parity_issues = _build_artifact_parity_checks(
                fixtures_path=resolved_parity_fixtures_path,
                artifact_fixture_root=artifact_fixture_root,
            )
            issues.extend(parity_issues)
        except DomainConformanceError as exc:
            artifact_parity = {
                "valid": False,
                "fixture_count": 0,
                "evaluated_count": 0,
                "fixtures": [],
            }
            issues.append(
                _issue(
                    code=_legacy_issue_code_for_urm(urm_code=exc.code),
                    message=str(exc),
                    context={"fixtures_path": str(resolved_parity_fixtures_path)},
                    urm_code=exc.code,
                )
            )
    if resolved_coverage_manifest_path is not None:
        try:
            coverage, coverage_issues = _build_coverage_checks(
                manifest_path=resolved_coverage_manifest_path,
                registry=registry,
                import_audit=import_audit,
                domain_reports=domain_reports,
                artifact_parity=artifact_parity,
            )
            issues.extend(coverage_issues)
        except DomainConformanceError as exc:
            coverage = {
                "manifest_schema": VNEXT_PLUS11_MANIFEST_SCHEMA,
                "manifest_hash": "0" * 64,
                "valid": False,
                "surface_count": 0,
                "covered_surface_count": 0,
                "coverage_pct": 0.0,
                "entries": [],
            }
            issues.append(
                _issue(
                    code=_legacy_issue_code_for_urm(urm_code=exc.code),
                    message=str(exc),
                    context={"manifest_path": str(resolved_coverage_manifest_path)},
                    urm_code=exc.code,
                )
            )

    report: dict[str, Any] = {
        "schema": DOMAIN_CONFORMANCE_SCHEMA,
        "valid": registry["valid"] and import_audit["valid"] and all(
            item["valid"] for item in domain_reports
        )
        and (artifact_parity is None or artifact_parity["valid"] is True)
        and (coverage is None or coverage["valid"] is True),
        "registry_order_determinism": registry,
        "import_audit": import_audit,
        "domains": domain_reports,
        "issues": _sort_issues(issues),
        "hash_excluded_fields": list(DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELD_LIST),
    }
    if artifact_parity is not None:
        report["artifact_parity"] = artifact_parity
    if coverage is not None:
        report["coverage"] = coverage
    report["domain_conformance_hash"] = domain_conformance_hash(report)
    validate_domain_conformance_report(report)
    return report
