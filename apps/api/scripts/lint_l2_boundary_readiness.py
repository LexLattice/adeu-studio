from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json

LINT_SCHEMA = "l2_boundary_readiness_lint@1"
READINESS_SCHEMA = "l2_boundary_readiness_assertion@1"
BLOCKER_REGISTRY_SCHEMA = "l2_boundary_blocker_registry@1"
READINESS_HEADING = "## L2 Boundary Readiness Assertions (Machine-Checkable)"

TARGETS: tuple[str, ...] = ("V31-F", "V31-G")
ALLOWED_SOURCE_OF_TRUTH: tuple[str, ...] = (
    "capability_policy_authority",
    "persisted_store_only",
)
EXPECTED_DETERMINISTIC_FIELDS: tuple[str, ...] = ("code", "reason", "context")
EXPECTED_EXCLUDED_FIELDS: tuple[str, ...] = (
    "created_at",
    "timestamp",
    "generated_at",
    "request_id",
    "trace_id",
    "hostname",
    "pid",
    "meta.captured_at",
)
SENTINEL_COMMIT = "fd9a48de8ab7852d371080659c9fc15aa24b8b70"

NO_TOUCH_RUNTIME_FILES: tuple[str, ...] = (
    "apps/api/src/adeu_api/urm_routes.py",
    "packages/urm_runtime/src/urm_runtime/capability_policy.py",
    "apps/api/src/adeu_api/main.py",
    "apps/api/src/adeu_api/storage.py",
)

RUN_SENTINEL_FIXTURE = "v35_worker_run_response_v34_baseline.json"
CANCEL_SENTINEL_FIXTURE = "v35_worker_cancel_response_v34_baseline.json"

TARGET_RE = re.compile(r"^V31-[FG]$")
BLOCKER_ID_RE = re.compile(r"^[A-Z][A-Z0-9_]*$")
PATH_SYMBOL_RE = re.compile(r"^[^#\s]+#[A-Za-z_][A-Za-z0-9_]*$")

EXCLUDED_KEY_NAMES = {
    "created_at",
    "timestamp",
    "generated_at",
    "request_id",
    "trace_id",
    "hostname",
    "pid",
}
EXCLUDED_DOTTED_PATHS = {"meta.captured_at"}

EXIT_BY_CATEGORY: dict[str, int] = {
    "schema": 2,
    "no_touch": 3,
    "sentinel": 4,
    "base_ref": 5,
}


@dataclass
class LintResult:
    lock_doc: str
    base_ref: str
    sentinel_dir: str
    failures: list[dict[str, Any]] = field(default_factory=list)

    def add_failure(self, *, category: str, code: str, details: dict[str, Any]) -> None:
        self.failures.append(
            {
                "category": category,
                "code": code,
                "details": details,
            }
        )

    def to_payload(self) -> dict[str, Any]:
        failures = sorted(
            self.failures,
            key=lambda row: (
                str(row["category"]),
                str(row["code"]),
                canonical_json(row["details"]),
            ),
        )
        return {
            "schema": LINT_SCHEMA,
            "lock_doc": self.lock_doc,
            "base_ref": self.base_ref,
            "sentinel_dir": self.sentinel_dir,
            "failures": failures,
        }

    def exit_code(self) -> int:
        categories = {row["category"] for row in self.failures}
        if "base_ref" in categories:
            return EXIT_BY_CATEGORY["base_ref"]
        if "schema" in categories:
            return EXIT_BY_CATEGORY["schema"]
        if "no_touch" in categories:
            return EXIT_BY_CATEGORY["no_touch"]
        if "sentinel" in categories:
            return EXIT_BY_CATEGORY["sentinel"]
        return 0


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Lint v35 L2 boundary-readiness assertions and anti-release guards with deterministic "
            "exit semantics."
        ),
    )
    parser.add_argument("--lock-doc", type=Path, required=True)
    parser.add_argument("--base-ref", required=True)
    parser.add_argument("--sentinel-dir", type=Path, required=True)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=None,
        help="Repository root override. Defaults to discovery from script location.",
    )
    return parser.parse_args(argv)


def _repo_root_from_script() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        if (parent / ".git").is_dir():
            return parent
    raise FileNotFoundError("repository root not found from script location")


def _resolve_repo_path(*, repo_root: Path, value: Path) -> Path:
    return value if value.is_absolute() else (repo_root / value)


def _extract_json_blocks(text: str) -> list[str]:
    lines = text.splitlines()
    blocks: list[str] = []
    index = 0
    while index < len(lines):
        if lines[index].strip() != "```json":
            index += 1
            continue
        index += 1
        block_lines: list[str] = []
        while index < len(lines) and lines[index].strip() != "```":
            block_lines.append(lines[index])
            index += 1
        if index >= len(lines):
            blocks.append("")
            break
        blocks.append("\n".join(block_lines).strip())
        index += 1
    return blocks


def _extract_json_blocks_under_heading(*, text: str, heading: str) -> list[str]:
    lines = text.splitlines()
    in_section = False
    section_lines: list[str] = []
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("## "):
            if stripped == heading:
                in_section = True
                continue
            if in_section:
                break
        if in_section:
            section_lines.append(line)
    return _extract_json_blocks("\n".join(section_lines))


def _parse_json_object(*, block_text: str, result: LintResult, code: str) -> dict[str, Any] | None:
    if not block_text:
        result.add_failure(category="schema", code=code, details={"reason": "empty_json_block"})
        return None
    try:
        payload = json.loads(block_text)
    except json.JSONDecodeError as exc:
        result.add_failure(
            category="schema",
            code=code,
            details={"reason": "json_decode_error", "message": str(exc)},
        )
        return None
    if not isinstance(payload, dict):
        result.add_failure(
            category="schema",
            code=code,
            details={"reason": "payload_not_object"},
        )
        return None
    return payload


def _is_sorted_unique_strings(values: list[str]) -> bool:
    return values == sorted(values) and len(values) == len(set(values))


def _is_non_empty_sorted_unique_strings(values: Any) -> bool:
    if not isinstance(values, list) or not values:
        return False
    if not all(isinstance(item, str) for item in values):
        return False
    return _is_sorted_unique_strings(values)


def _validate_blocker_registry(
    *,
    payload: dict[str, Any],
    result: LintResult,
) -> set[str]:
    required_keys = {"schema", "blockers"}
    if set(payload.keys()) != required_keys:
        result.add_failure(
            category="schema",
            code="BLOCKER_REGISTRY_INVALID",
            details={"reason": "keyset_mismatch"},
        )
        return set()
    if payload.get("schema") != BLOCKER_REGISTRY_SCHEMA:
        result.add_failure(
            category="schema",
            code="BLOCKER_REGISTRY_INVALID",
            details={"reason": "schema_mismatch", "expected_schema": BLOCKER_REGISTRY_SCHEMA},
        )
        return set()
    blockers = payload.get("blockers")
    if not isinstance(blockers, list) or not blockers:
        result.add_failure(
            category="schema",
            code="BLOCKER_REGISTRY_INVALID",
            details={"reason": "blockers_not_non_empty_list"},
        )
        return set()

    blocker_ids: list[str] = []
    for index, blocker in enumerate(blockers):
        if not isinstance(blocker, dict):
            result.add_failure(
                category="schema",
                code="BLOCKER_REGISTRY_INVALID",
                details={"reason": "blocker_not_object", "index": index},
            )
            continue
        if set(blocker.keys()) != {"id", "evidence_ref_type", "evidence_ref"}:
            result.add_failure(
                category="schema",
                code="BLOCKER_REGISTRY_INVALID",
                details={"reason": "blocker_keyset_mismatch", "index": index},
            )
            continue
        blocker_id = blocker.get("id")
        evidence_ref_type = blocker.get("evidence_ref_type")
        evidence_ref = blocker.get("evidence_ref")
        if not isinstance(blocker_id, str) or not BLOCKER_ID_RE.match(blocker_id):
            result.add_failure(
                category="schema",
                code="BLOCKER_REGISTRY_INVALID",
                details={"reason": "invalid_blocker_id", "index": index},
            )
            continue
        if evidence_ref_type not in {"DOC", "CHECK"}:
            result.add_failure(
                category="schema",
                code="BLOCKER_REGISTRY_INVALID",
                details={"reason": "invalid_evidence_ref_type", "index": index},
            )
            continue
        if not isinstance(evidence_ref, str) or not evidence_ref:
            result.add_failure(
                category="schema",
                code="BLOCKER_REGISTRY_INVALID",
                details={"reason": "invalid_evidence_ref", "index": index},
            )
            continue
        blocker_ids.append(blocker_id)

    if blocker_ids and not _is_sorted_unique_strings(blocker_ids):
        result.add_failure(
            category="schema",
            code="BLOCKER_REGISTRY_INVALID",
            details={"reason": "blocker_ids_not_sorted_unique"},
        )
    return set(blocker_ids)


def _validate_readiness_payload(
    *,
    payload: dict[str, Any],
    blocker_ids: set[str],
    result: LintResult,
) -> str | None:
    required_keys = {
        "schema",
        "target",
        "candidate_surfaces",
        "source_of_truth",
        "denial_semantics",
        "rollback_semantics",
        "release_blockers",
    }
    if set(payload.keys()) != required_keys:
        result.add_failure(
            category="schema",
            code="READINESS_SCHEMA_INVALID",
            details={"reason": "keyset_mismatch"},
        )
        return None
    if payload.get("schema") != READINESS_SCHEMA:
        result.add_failure(
            category="schema",
            code="READINESS_SCHEMA_INVALID",
            details={"reason": "schema_mismatch", "expected_schema": READINESS_SCHEMA},
        )
        return None

    target = payload.get("target")
    if not isinstance(target, str) or not TARGET_RE.match(target):
        result.add_failure(
            category="schema",
            code="READINESS_SCHEMA_INVALID",
            details={"reason": "invalid_target"},
        )
        target = None

    candidate_surfaces = payload.get("candidate_surfaces")
    if not _is_non_empty_sorted_unique_strings(candidate_surfaces):
        result.add_failure(
            category="schema",
            code="READINESS_SCHEMA_INVALID",
            details={"reason": "candidate_surfaces_not_sorted_unique_non_empty"},
        )
    elif not all(PATH_SYMBOL_RE.match(item) for item in candidate_surfaces):
        result.add_failure(
            category="schema",
            code="READINESS_SCHEMA_INVALID",
            details={"reason": "candidate_surfaces_invalid_path_symbol"},
        )

    source_of_truth = payload.get("source_of_truth")
    if source_of_truth not in ALLOWED_SOURCE_OF_TRUTH:
        result.add_failure(
            category="schema",
            code="READINESS_SCHEMA_INVALID",
            details={"reason": "invalid_source_of_truth"},
        )

    denial = payload.get("denial_semantics")
    if not isinstance(denial, dict) or set(denial.keys()) != {
        "mode",
        "deterministic_fields",
        "nondeterministic_fields_excluded",
    }:
        result.add_failure(
            category="schema",
            code="READINESS_SCHEMA_INVALID",
            details={"reason": "denial_semantics_keyset_mismatch"},
        )
    else:
        deterministic_fields = denial.get("deterministic_fields")
        if (
            not isinstance(deterministic_fields, list)
            or [item for item in deterministic_fields if isinstance(item, str)]
            != list(EXPECTED_DETERMINISTIC_FIELDS)
        ):
            result.add_failure(
                category="schema",
                code="READINESS_SCHEMA_INVALID",
                details={"reason": "deterministic_fields_mismatch"},
            )
        excluded_fields = denial.get("nondeterministic_fields_excluded")
        if not _is_non_empty_sorted_unique_strings(excluded_fields):
            result.add_failure(
                category="schema",
                code="READINESS_SCHEMA_INVALID",
                details={"reason": "nondeterministic_fields_excluded_not_sorted_unique_non_empty"},
            )

    rollback = payload.get("rollback_semantics")
    if not isinstance(rollback, dict) or set(rollback.keys()) != {
        "mode",
        "requires_explicit_lock_update",
        "partial_enablement_forbidden",
        "migration_down_contract",
    }:
        result.add_failure(
            category="schema",
            code="READINESS_SCHEMA_INVALID",
            details={"reason": "rollback_semantics_keyset_mismatch"},
        )
    else:
        if rollback.get("requires_explicit_lock_update") is not True:
            result.add_failure(
                category="schema",
                code="READINESS_SCHEMA_INVALID",
                details={"reason": "requires_explicit_lock_update_not_true"},
            )
        if rollback.get("partial_enablement_forbidden") is not True:
            result.add_failure(
                category="schema",
                code="READINESS_SCHEMA_INVALID",
                details={"reason": "partial_enablement_forbidden_not_true"},
            )
        migration_down_contract = rollback.get("migration_down_contract")
        if not isinstance(migration_down_contract, str) or not migration_down_contract:
            result.add_failure(
                category="schema",
                code="READINESS_SCHEMA_INVALID",
                details={"reason": "migration_down_contract_invalid"},
            )

    release_blockers = payload.get("release_blockers")
    if not _is_non_empty_sorted_unique_strings(release_blockers):
        result.add_failure(
            category="schema",
            code="READINESS_SCHEMA_INVALID",
            details={"reason": "release_blockers_not_sorted_unique_non_empty"},
        )
    else:
        invalid_ids = [item for item in release_blockers if not BLOCKER_ID_RE.match(item)]
        if invalid_ids:
            result.add_failure(
                category="schema",
                code="READINESS_SCHEMA_INVALID",
                details={"reason": "release_blockers_invalid_ids", "invalid_ids": invalid_ids},
            )
        missing_ids = sorted(set(release_blockers) - blocker_ids)
        if missing_ids:
            result.add_failure(
                category="schema",
                code="BLOCKER_MEMBERSHIP_INVALID",
                details={"target": target, "missing_blockers": missing_ids},
            )
    return target if isinstance(target, str) else None


def _validate_lock_doc(
    *,
    lock_doc_path: Path,
    result: LintResult,
) -> None:
    if not lock_doc_path.is_file():
        result.add_failure(
            category="schema",
            code="LOCK_DOC_NOT_FOUND",
            details={"path": str(lock_doc_path)},
        )
        return
    text = lock_doc_path.read_text(encoding="utf-8")

    section_blocks = _extract_json_blocks_under_heading(text=text, heading=READINESS_HEADING)
    section_payloads: list[dict[str, Any]] = []
    for block_text in section_blocks:
        payload = _parse_json_object(
            block_text=block_text,
            result=result,
            code="READINESS_BLOCK_INVALID",
        )
        if payload is not None:
            section_payloads.append(payload)

    section_readiness_payloads = [
        payload for payload in section_payloads if payload.get("schema") == READINESS_SCHEMA
    ]
    if len(section_readiness_payloads) != 2:
        result.add_failure(
            category="schema",
            code="READINESS_BLOCK_COUNT_INVALID",
            details={"expected_count": 2, "actual_count": len(section_readiness_payloads)},
        )

    all_blocks = _extract_json_blocks(text)
    parsed_blocks: list[dict[str, Any]] = []
    for block_text in all_blocks:
        payload = _parse_json_object(
            block_text=block_text,
            result=result,
            code="JSON_BLOCK_INVALID",
        )
        if payload is not None:
            parsed_blocks.append(payload)

    registry_blocks = [
        payload for payload in parsed_blocks if payload.get("schema") == BLOCKER_REGISTRY_SCHEMA
    ]
    if len(registry_blocks) != 1:
        result.add_failure(
            category="schema",
            code="BLOCKER_REGISTRY_COUNT_INVALID",
            details={"expected_count": 1, "actual_count": len(registry_blocks)},
        )
        blocker_ids: set[str] = set()
    else:
        blocker_ids = _validate_blocker_registry(payload=registry_blocks[0], result=result)

    readiness_blocks_all = [
        payload for payload in parsed_blocks if payload.get("schema") == READINESS_SCHEMA
    ]
    if len(readiness_blocks_all) != 2:
        result.add_failure(
            category="schema",
            code="READINESS_BLOCK_GLOBAL_COUNT_INVALID",
            details={"expected_count": 2, "actual_count": len(readiness_blocks_all)},
        )

    targets_seen: list[str] = []
    for payload in section_readiness_payloads:
        target = _validate_readiness_payload(
            payload=payload,
            blocker_ids=blocker_ids,
            result=result,
        )
        if target is not None:
            targets_seen.append(target)
    if sorted(targets_seen) != sorted(TARGETS):
        result.add_failure(
            category="schema",
            code="READINESS_TARGET_SET_INVALID",
            details={
                "expected_targets": list(TARGETS),
                "actual_targets": sorted(set(targets_seen)),
            },
        )
    if len(targets_seen) != len(set(targets_seen)):
        result.add_failure(
            category="schema",
            code="READINESS_TARGET_SET_INVALID",
            details={"reason": "duplicate_target"},
        )


def _run_git(*, repo_root: Path, args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
    )


def _collect_changed_files(*, repo_root: Path, base_ref: str, result: LintResult) -> set[str]:
    verify = _run_git(
        repo_root=repo_root,
        args=["rev-parse", "--verify", "--quiet", f"{base_ref}^{{commit}}"],
    )
    if verify.returncode != 0:
        result.add_failure(
            category="base_ref",
            code="BASE_REF_UNAVAILABLE",
            details={"base_ref": base_ref},
        )
        return set()

    merge_base = _run_git(repo_root=repo_root, args=["merge-base", base_ref, "HEAD"])
    if merge_base.returncode != 0:
        result.add_failure(
            category="base_ref",
            code="BASE_REF_UNAVAILABLE",
            details={"base_ref": base_ref},
        )
        return set()
    merge_base_sha = merge_base.stdout.strip()
    if not merge_base_sha:
        result.add_failure(
            category="base_ref",
            code="BASE_REF_UNAVAILABLE",
            details={"base_ref": base_ref},
        )
        return set()

    changed = _run_git(
        repo_root=repo_root,
        args=[
            "diff",
            "--name-only",
            "--diff-filter=ACDMRTUXB",
            f"{merge_base_sha}..HEAD",
        ],
    )
    if changed.returncode != 0:
        result.add_failure(
            category="base_ref",
            code="BASE_REF_UNAVAILABLE",
            details={"base_ref": base_ref},
        )
        return set()
    return {line.strip() for line in changed.stdout.splitlines() if line.strip()}


def _no_touch_violations(changed_paths: set[str]) -> list[str]:
    return sorted(path for path in NO_TOUCH_RUNTIME_FILES if path in changed_paths)


class _AuthorizeActionCalled(RuntimeError):
    pass


def _capture_current_worker_endpoint_responses() -> dict[str, dict[str, Any]]:
    import adeu_api.urm_routes as urm_routes
    from urm_runtime.models import (
        WorkerCancelRequest,
        WorkerCancelResponse,
        WorkerRunRequest,
        WorkerRunResult,
    )

    run_body = {
        "worker_id": "worker-v34-baseline",
        "status": "ok",
        "exit_code": 0,
        "evidence_id": "evidence-v34-baseline",
        "raw_jsonl_path": "evidence/codex/worker-v34-baseline/codex_raw.ndjson",
        "urm_events_path": "evidence/codex/worker-v34-baseline/urm_events.ndjson",
        "normalized_event_count": 2,
        "artifact_candidate": {"artifact": {"kind": "demo", "value": 1}},
        "parse_degraded": False,
        "invalid_schema": False,
        "schema_validation_errors": [],
        "error": None,
        "idempotent_replay": False,
    }
    cancel_body = {
        "worker_id": "worker-v34-baseline",
        "status": "cancelled",
        "idempotent_replay": False,
        "error": None,
    }
    run_request = {
        "provider": "codex",
        "role": "pipeline_worker",
        "client_request_id": "v35-boundary-sentinel-run",
        "prompt": "boundary sentinel",
        "template_id": "adeu.workflow.pipeline_worker.v0",
        "template_version": "v0",
        "schema_version": "urm.workflow.v0",
        "domain_pack_id": "urm_domain_adeu",
        "domain_pack_version": "0.0.0",
    }

    class _StubRunner:
        def run(self, request: WorkerRunRequest) -> WorkerRunResult:
            del request
            return WorkerRunResult.model_validate(run_body)

        def cancel(self, *, worker_id: str) -> WorkerCancelResponse:
            payload = dict(cancel_body)
            payload["worker_id"] = worker_id
            return WorkerCancelResponse.model_validate(payload)

    original_get_worker_runner = urm_routes._get_worker_runner
    original_authorize_action = urm_routes.authorize_action

    def _forbid_authorize_action(*args: Any, **kwargs: Any) -> Any:
        del args, kwargs
        raise _AuthorizeActionCalled("authorize_action invoked in worker route path")

    try:
        urm_routes._get_worker_runner = lambda: _StubRunner()
        urm_routes.authorize_action = _forbid_authorize_action
        run_response = urm_routes.urm_worker_run_endpoint(
            WorkerRunRequest.model_validate(run_request)
        )
        cancel_response = urm_routes.urm_worker_cancel_endpoint(
            "worker-v34-baseline",
            WorkerCancelRequest(provider="codex"),
        )
    finally:
        urm_routes._get_worker_runner = original_get_worker_runner
        urm_routes.authorize_action = original_authorize_action

    return {
        RUN_SENTINEL_FIXTURE: {
            "status_code": 200,
            "body": run_response.model_dump(mode="json"),
        },
        CANCEL_SENTINEL_FIXTURE: {
            "status_code": 200,
            "body": cancel_response.model_dump(mode="json"),
        },
    }


def _normalize_for_comparison(value: Any, *, path: tuple[str, ...] = ()) -> Any:
    if isinstance(value, dict):
        normalized: dict[str, Any] = {}
        for key in sorted(value.keys()):
            if key in EXCLUDED_KEY_NAMES:
                continue
            dotted = ".".join((*path, key))
            if dotted in EXCLUDED_DOTTED_PATHS:
                continue
            normalized[key] = _normalize_for_comparison(value[key], path=(*path, key))
        return normalized
    if isinstance(value, list):
        return [_normalize_for_comparison(item, path=path) for item in value]
    return value


def _load_sentinel_fixture(*, path: Path, result: LintResult) -> dict[str, Any] | None:
    if not path.is_file():
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "missing_fixture"},
        )
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "json_decode_error"},
        )
        return None
    if not isinstance(payload, dict):
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "payload_not_object"},
        )
        return None
    if set(payload.keys()) != {"meta", "response"}:
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "top_level_keyset_mismatch"},
        )
        return None

    meta = payload.get("meta")
    response = payload.get("response")
    if not isinstance(meta, dict) or set(meta.keys()) != {
        "captured_from_commit",
        "captured_by_script",
        "captured_at",
    }:
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "meta_keyset_mismatch"},
        )
        return None
    if meta.get("captured_from_commit") != SENTINEL_COMMIT:
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "captured_from_commit_mismatch"},
        )
        return None
    if not isinstance(meta.get("captured_by_script"), str) or not meta["captured_by_script"]:
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "captured_by_script_invalid"},
        )
        return None
    if not isinstance(meta.get("captured_at"), str) or not meta["captured_at"]:
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "captured_at_invalid"},
        )
        return None
    if not isinstance(response, dict):
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "response_not_object"},
        )
        return None
    if set(response.keys()) != {"status_code", "body"}:
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "response_keyset_mismatch"},
        )
        return None
    if not isinstance(response.get("status_code"), int):
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "status_code_not_int"},
        )
        return None
    if not isinstance(response.get("body"), dict):
        result.add_failure(
            category="sentinel",
            code="SENTINEL_INVALID",
            details={"path": str(path), "reason": "body_not_object"},
        )
        return None
    return payload


def _validate_sentinels(*, sentinel_dir: Path, result: LintResult) -> None:
    current = _capture_current_worker_endpoint_responses()

    fixture_map = {
        RUN_SENTINEL_FIXTURE: sentinel_dir / RUN_SENTINEL_FIXTURE,
        CANCEL_SENTINEL_FIXTURE: sentinel_dir / CANCEL_SENTINEL_FIXTURE,
    }
    for fixture_name, fixture_path in fixture_map.items():
        fixture_payload = _load_sentinel_fixture(path=fixture_path, result=result)
        if fixture_payload is None:
            continue
        expected_response = fixture_payload["response"]
        actual_response = current[fixture_name]
        normalized_expected = _normalize_for_comparison(expected_response)
        normalized_actual = _normalize_for_comparison(actual_response)
        if canonical_json(normalized_expected) != canonical_json(normalized_actual):
            result.add_failure(
                category="sentinel",
                code="SENTINEL_DRIFT",
                details={"fixture": fixture_name},
            )


def lint_l2_boundary_readiness(
    *,
    repo_root: Path,
    lock_doc: Path,
    base_ref: str,
    sentinel_dir: Path,
) -> tuple[dict[str, Any], int]:
    result = LintResult(
        lock_doc=str(lock_doc),
        base_ref=base_ref,
        sentinel_dir=str(sentinel_dir),
    )

    _validate_lock_doc(lock_doc_path=lock_doc, result=result)

    changed_paths = _collect_changed_files(repo_root=repo_root, base_ref=base_ref, result=result)
    if any(failure["category"] == "base_ref" for failure in result.failures):
        payload = result.to_payload()
        return payload, result.exit_code()

    no_touch = _no_touch_violations(changed_paths)
    if no_touch:
        result.add_failure(
            category="no_touch",
            code="NO_TOUCH_DIFF_VIOLATION",
            details={"touched_files": no_touch},
        )

    try:
        _validate_sentinels(sentinel_dir=sentinel_dir, result=result)
    except _AuthorizeActionCalled:
        result.add_failure(
            category="no_touch",
            code="NO_AUTHORIZE_ACTION_CALLS_VIOLATION",
            details={"routes": ["/urm/worker/run", "/urm/worker/{worker_id}/cancel"]},
        )

    payload = result.to_payload()
    return payload, result.exit_code()


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = args.repo_root.resolve() if args.repo_root is not None else _repo_root_from_script()
    lock_doc = _resolve_repo_path(repo_root=repo_root, value=args.lock_doc).resolve()
    sentinel_dir = _resolve_repo_path(repo_root=repo_root, value=args.sentinel_dir).resolve()

    payload, exit_code = lint_l2_boundary_readiness(
        repo_root=repo_root.resolve(),
        lock_doc=lock_doc,
        base_ref=args.base_ref,
        sentinel_dir=sentinel_dir,
    )
    sys.stdout.write(canonical_json(payload) + "\n")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
