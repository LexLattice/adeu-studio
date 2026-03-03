from __future__ import annotations

import argparse
import ast
import fnmatch
import json
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from fastapi import HTTPException
from urm_runtime.hashing import canonical_json

LINT_SCHEMA = "v31g_persistence_release_lint@1"
CONSUMPTION_SCHEMA = "l2_boundary_release_consumption@1"
SOURCE_OF_TRUTH_SCHEMA = "v31g_persistence_source_of_truth_assertion@1"
RECORD_CONTRACT_SCHEMA = "v31g_idempotency_record_contract@1"
HASH_PROJECTION_SCHEMA = "v31g_idempotency_hash_projection_assertion@1"

EXPECTED_CONSUMPTION_KEYSET = {
    "schema",
    "source_lock_doc",
    "source_assertion_schema",
    "target",
    "authorized_surfaces",
    "required_blockers",
}
EXPECTED_AUTHORIZED_SURFACES = {
    "apps/api/src/adeu_api/main.py#_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY",
    "apps/api/src/adeu_api/main.py#urm_core_ir_propose_endpoint",
    "apps/api/src/adeu_api/storage.py#transaction",
}
EXPECTED_REQUIRED_BLOCKERS = {
    "BOUNDARY_LOCK_APPROVED",
    "PERSISTENCE_SOURCE_OF_TRUTH_FROZEN",
    "REPLAY_CONFLICT_REGRESSION_GUARDS_GREEN",
}

EXPECTED_SOURCE_OF_TRUTH_PAYLOAD = {
    "schema": SOURCE_OF_TRUTH_SCHEMA,
    "runtime_module_path": "apps/api/src/adeu_api/main.py",
    "runtime_surface_symbol": "urm_core_ir_propose_endpoint",
    "deferred_cache_symbol": "_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY",
    "storage_module_path": "apps/api/src/adeu_api/storage.py",
    "storage_entrypoint_symbol": "transaction",
    "source_of_truth": "persisted_store_only",
    "dual_write_allowed": False,
}
EXPECTED_RECORD_CONTRACT_PAYLOAD = {
    "schema": RECORD_CONTRACT_SCHEMA,
    "idempotency_key": "client_request_id",
    "uniqueness_constraint": "unique(client_request_id)",
    "required_fields": [
        "client_request_id",
        "provider",
        "request_payload_hash",
        "response_payload",
        "created_at",
    ],
    "determinism_authority_fields": [
        "client_request_id",
        "provider",
        "request_payload_hash",
        "response_payload",
    ],
    "nondeterministic_metadata_fields_excluded": ["created_at"],
}
EXPECTED_HASH_PROJECTION_PAYLOAD = {
    "schema": HASH_PROJECTION_SCHEMA,
    "builder_symbol": "CoreIRProposerRequest.idempotency_payload",
    "hash_function": "sha256_canonical_json",
    "canonicalization_profile": "frozen_canonical_json_v1",
    "projection_mode": "closed_world",
    "additional_fields_forbidden": True,
    "included_fields": [
        "provider",
        "source_text_hash",
        "surface_id",
    ],
    "excluded_fields": [
        "client_request_id",
        "source_text",
    ],
}

REQUIRED_MISMATCH_CONTEXT_FIELDS = {
    "client_request_id",
    "provider_expected",
    "provider_observed",
    "request_payload_hash_expected",
    "request_payload_hash_observed",
}

EXIT_BY_CATEGORY: dict[str, int] = {
    "schema": 2,
    "callgraph": 3,
    "determinism": 4,
    "base_ref": 5,
}


@dataclass
class LintResult:
    lock_doc: str
    base_ref: str
    repo_root: str
    failures: list[dict[str, Any]] = field(default_factory=list)
    merge_base: str | None = None

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
        payload: dict[str, Any] = {
            "schema": LINT_SCHEMA,
            "lock_doc": self.lock_doc,
            "base_ref": self.base_ref,
            "repo_root": self.repo_root,
            "failures": failures,
        }
        if self.merge_base is not None:
            payload["merge_base"] = self.merge_base
        return payload

    def exit_code(self) -> int:
        categories = {row["category"] for row in self.failures}
        if "base_ref" in categories:
            return EXIT_BY_CATEGORY["base_ref"]
        if "schema" in categories:
            return EXIT_BY_CATEGORY["schema"]
        if "callgraph" in categories:
            return EXIT_BY_CATEGORY["callgraph"]
        if "determinism" in categories:
            return EXIT_BY_CATEGORY["determinism"]
        return 0


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Lint v37 persistence release constraints with deterministic exit behavior "
            "for schema/callgraph/determinism/base-ref failures."
        )
    )
    parser.add_argument("--lock-doc", type=Path, required=True)
    parser.add_argument("--base-ref", required=True)
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
        blocks.append("\n".join(block_lines).strip())
        if index < len(lines):
            index += 1
    return blocks


def _parse_json_object(*, block_text: str, result: LintResult, code: str) -> dict[str, Any] | None:
    if not block_text:
        result.add_failure(
            category="schema",
            code=code,
            details={"reason": "empty_json_block"},
        )
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


def _validate_consumption_payload(payload: dict[str, Any], result: LintResult) -> None:
    if set(payload.keys()) != EXPECTED_CONSUMPTION_KEYSET:
        result.add_failure(
            category="schema",
            code="CONSUMPTION_SCHEMA_INVALID",
            details={"reason": "keyset_mismatch"},
        )
        return
    if payload.get("schema") != CONSUMPTION_SCHEMA:
        result.add_failure(
            category="schema",
            code="CONSUMPTION_SCHEMA_INVALID",
            details={"reason": "schema_mismatch"},
        )
    if payload.get("source_lock_doc") != "docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md":
        result.add_failure(
            category="schema",
            code="CONSUMPTION_SCHEMA_INVALID",
            details={"reason": "source_lock_doc_mismatch"},
        )
    if payload.get("source_assertion_schema") != "l2_boundary_readiness_assertion@1":
        result.add_failure(
            category="schema",
            code="CONSUMPTION_SCHEMA_INVALID",
            details={"reason": "source_assertion_schema_mismatch"},
        )
    if payload.get("target") != "V31-G":
        result.add_failure(
            category="schema",
            code="CONSUMPTION_SCHEMA_INVALID",
            details={"reason": "target_mismatch"},
        )

    authorized_surfaces = payload.get("authorized_surfaces")
    if not isinstance(authorized_surfaces, list) or not all(
        isinstance(item, str) for item in authorized_surfaces
    ):
        result.add_failure(
            category="schema",
            code="CONSUMPTION_SCHEMA_INVALID",
            details={"reason": "authorized_surfaces_invalid"},
        )
    else:
        if len(authorized_surfaces) != len(set(authorized_surfaces)):
            result.add_failure(
                category="schema",
                code="CONSUMPTION_SCHEMA_INVALID",
                details={"reason": "authorized_surfaces_not_unique"},
            )
        if set(authorized_surfaces) != EXPECTED_AUTHORIZED_SURFACES:
            result.add_failure(
                category="schema",
                code="CONSUMPTION_SCHEMA_INVALID",
                details={
                    "reason": "authorized_surfaces_set_mismatch",
                    "expected": sorted(EXPECTED_AUTHORIZED_SURFACES),
                    "observed": sorted(set(authorized_surfaces)),
                },
            )

    required_blockers = payload.get("required_blockers")
    if not isinstance(required_blockers, list) or not all(
        isinstance(item, str) for item in required_blockers
    ):
        result.add_failure(
            category="schema",
            code="CONSUMPTION_SCHEMA_INVALID",
            details={"reason": "required_blockers_invalid"},
        )
    else:
        if len(required_blockers) != len(set(required_blockers)):
            result.add_failure(
                category="schema",
                code="CONSUMPTION_SCHEMA_INVALID",
                details={"reason": "required_blockers_not_unique"},
            )
        if set(required_blockers) != EXPECTED_REQUIRED_BLOCKERS:
            result.add_failure(
                category="schema",
                code="CONSUMPTION_SCHEMA_INVALID",
                details={
                    "reason": "required_blockers_set_mismatch",
                    "expected": sorted(EXPECTED_REQUIRED_BLOCKERS),
                    "observed": sorted(set(required_blockers)),
                },
            )


def _validate_exact_payload(
    *,
    payload: dict[str, Any],
    expected_payload: dict[str, Any],
    code: str,
    result: LintResult,
) -> None:
    if payload != expected_payload:
        result.add_failure(
            category="schema",
            code=code,
            details={
                "reason": "payload_mismatch",
                "expected": expected_payload,
                "observed": payload,
            },
        )


def _validate_lock_doc_assertions(*, lock_doc: Path, result: LintResult) -> None:
    text = lock_doc.read_text(encoding="utf-8")
    blocks = _extract_json_blocks(text)
    parsed_blocks: list[dict[str, Any]] = []
    for index, block in enumerate(blocks):
        payload = _parse_json_object(
            block_text=block,
            result=result,
            code="LOCK_JSON_BLOCK_INVALID",
        )
        if payload is None:
            continue
        schema = payload.get("schema")
        if not isinstance(schema, str):
            result.add_failure(
                category="schema",
                code="LOCK_JSON_BLOCK_INVALID",
                details={"reason": "missing_schema", "index": index},
            )
            continue
        parsed_blocks.append(payload)

    payloads_by_schema: dict[str, list[dict[str, Any]]] = {}
    for payload in parsed_blocks:
        payloads_by_schema.setdefault(str(payload["schema"]), []).append(payload)

    required_schemas = (
        CONSUMPTION_SCHEMA,
        SOURCE_OF_TRUTH_SCHEMA,
        RECORD_CONTRACT_SCHEMA,
        HASH_PROJECTION_SCHEMA,
    )
    for schema in required_schemas:
        matches = payloads_by_schema.get(schema, [])
        if len(matches) != 1:
            result.add_failure(
                category="schema",
                code="ASSERTION_BLOCK_COUNT_INVALID",
                details={"schema": schema, "count": len(matches)},
            )

    consumption_matches = payloads_by_schema.get(CONSUMPTION_SCHEMA, [])
    if len(consumption_matches) == 1:
        _validate_consumption_payload(consumption_matches[0], result)

    source_matches = payloads_by_schema.get(SOURCE_OF_TRUTH_SCHEMA, [])
    if len(source_matches) == 1:
        _validate_exact_payload(
            payload=source_matches[0],
            expected_payload=EXPECTED_SOURCE_OF_TRUTH_PAYLOAD,
            code="SOURCE_OF_TRUTH_SCHEMA_INVALID",
            result=result,
        )

    record_matches = payloads_by_schema.get(RECORD_CONTRACT_SCHEMA, [])
    if len(record_matches) == 1:
        _validate_exact_payload(
            payload=record_matches[0],
            expected_payload=EXPECTED_RECORD_CONTRACT_PAYLOAD,
            code="RECORD_CONTRACT_SCHEMA_INVALID",
            result=result,
        )

    hash_matches = payloads_by_schema.get(HASH_PROJECTION_SCHEMA, [])
    if len(hash_matches) == 1:
        _validate_exact_payload(
            payload=hash_matches[0],
            expected_payload=EXPECTED_HASH_PROJECTION_PAYLOAD,
            code="HASH_PROJECTION_SCHEMA_INVALID",
            result=result,
        )


def _git_text(*args: str, repo_root: Path) -> str:
    completed = subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        stderr = completed.stderr.strip()
        raise RuntimeError(f"git {' '.join(args)} failed: {stderr}")
    return completed.stdout.strip()


def _changed_files_against_base_ref(*, base_ref: str, repo_root: Path) -> tuple[str, list[str]]:
    merge_base = _git_text("merge-base", base_ref, "HEAD", repo_root=repo_root)
    changed = _git_text(
        "diff",
        "--name-only",
        "--diff-filter=ACDMRTUXB",
        f"{merge_base}..HEAD",
        repo_root=repo_root,
    )
    changed_files = sorted({line.strip() for line in changed.splitlines() if line.strip()})
    return merge_base, changed_files


def _check_diff_guards(*, changed_files: list[str], result: LintResult) -> None:
    migration_or_sql_matches = sorted(
        path
        for path in changed_files
        if fnmatch.fnmatch(path, "apps/**/migrations/**")
        or fnmatch.fnmatch(path, "apps/**/*.sql")
    )
    if migration_or_sql_matches:
        result.add_failure(
            category="callgraph",
            code="DIFF_GUARD_MIGRATION_SQL_VIOLATION",
            details={"paths": migration_or_sql_matches},
        )


def _call_name(node: ast.expr) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return None


def _find_function(module: ast.Module, *, name: str) -> ast.FunctionDef | None:
    for node in module.body:
        if isinstance(node, ast.FunctionDef) and node.name == name:
            return node
    return None


def _target_contains_cache_subscript(target: ast.expr) -> bool:
    if isinstance(target, ast.Subscript):
        base = target.value
        return isinstance(base, ast.Name) and base.id == "_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY"
    return False


def _check_persistence_callgraph(*, repo_root: Path, result: LintResult) -> None:
    main_path = repo_root / "apps" / "api" / "src" / "adeu_api" / "main.py"
    storage_path = repo_root / "apps" / "api" / "src" / "adeu_api" / "storage.py"

    try:
        main_source = main_path.read_text(encoding="utf-8")
        storage_source = storage_path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        result.add_failure(
            category="callgraph",
            code="PERSISTENCE_CALLGRAPH_VIOLATION",
            details={"reason": "required_source_missing", "error": str(exc)},
        )
        return

    try:
        main_ast = ast.parse(main_source)
    except SyntaxError as exc:
        result.add_failure(
            category="callgraph",
            code="PERSISTENCE_CALLGRAPH_VIOLATION",
            details={"reason": "main_parse_error", "error": str(exc)},
        )
        return

    proposer_endpoint = _find_function(main_ast, name="urm_core_ir_propose_endpoint")
    if proposer_endpoint is None:
        result.add_failure(
            category="callgraph",
            code="PERSISTENCE_CALLGRAPH_VIOLATION",
            details={"reason": "missing_proposer_endpoint"},
        )
        return

    call_counts: dict[str, int] = {}
    for node in ast.walk(proposer_endpoint):
        if isinstance(node, ast.Call):
            name = _call_name(node.func)
            if name is None:
                continue
            call_counts[name] = call_counts.get(name, 0) + 1

    required_min_calls = {
        "storage_transaction": 1,
        "create_core_ir_proposer_idempotency_if_absent": 1,
        "get_core_ir_proposer_idempotency_by_client_request_id": 2,
    }
    missing_or_low_calls = {
        name: minimum
        for name, minimum in required_min_calls.items()
        if call_counts.get(name, 0) < minimum
    }
    if missing_or_low_calls:
        result.add_failure(
            category="callgraph",
            code="PERSISTENCE_CALLGRAPH_VIOLATION",
            details={
                "reason": "required_calls_missing_or_insufficient",
                "missing_or_low_calls": missing_or_low_calls,
                "observed": call_counts,
            },
        )

    cache_name_references = [
        node
        for node in ast.walk(proposer_endpoint)
        if isinstance(node, ast.Name) and node.id == "_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY"
    ]
    if cache_name_references:
        result.add_failure(
            category="callgraph",
            code="CACHE_AUTHORITY_VIOLATION",
            details={"reason": "cache_symbol_referenced_in_endpoint"},
        )

    for node in ast.walk(proposer_endpoint):
        if isinstance(node, ast.Assign):
            if any(_target_contains_cache_subscript(target) for target in node.targets):
                result.add_failure(
                    category="callgraph",
                    code="CACHE_AUTHORITY_VIOLATION",
                    details={"reason": "cache_assignment_in_endpoint"},
                )
        if isinstance(node, ast.AnnAssign) and node.target is not None:
            if _target_contains_cache_subscript(node.target):
                result.add_failure(
                    category="callgraph",
                    code="CACHE_AUTHORITY_VIOLATION",
                    details={"reason": "cache_assignment_in_endpoint"},
                )
        if isinstance(node, ast.AugAssign):
            if _target_contains_cache_subscript(node.target):
                result.add_failure(
                    category="callgraph",
                    code="CACHE_AUTHORITY_VIOLATION",
                    details={"reason": "cache_assignment_in_endpoint"},
                )

    required_storage_fragments = (
        "CREATE TABLE IF NOT EXISTS core_ir_proposer_idempotency",
        "client_request_id TEXT PRIMARY KEY",
        "ON CONFLICT(client_request_id) DO NOTHING",
    )
    missing_fragments = [
        fragment for fragment in required_storage_fragments if fragment not in storage_source
    ]
    if missing_fragments:
        result.add_failure(
            category="callgraph",
            code="PERSISTENCE_CALLGRAPH_VIOLATION",
            details={"reason": "storage_contract_fragment_missing", "missing": missing_fragments},
        )


def _normalize_cache_for_probe(api_main_module: Any) -> None:
    cache_clear = getattr(
        api_main_module._provider_parity_supported_providers_by_surface,
        "cache_clear",
        None,
    )
    if callable(cache_clear):
        cache_clear()
    api_main_module._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY.clear()


def _determinism_failure(
    *,
    result: LintResult,
    reason: str,
    details: dict[str, Any] | None = None,
) -> None:
    payload = {"reason": reason}
    if details:
        payload.update(details)
    result.add_failure(
        category="determinism",
        code="REPLAY_CONFLICT_DETERMINISM_VIOLATION",
        details=payload,
    )


def _require_mismatch_detail(
    *,
    detail: Any,
    expected_client_request_id: str,
    result: LintResult,
) -> None:
    if not isinstance(detail, dict):
        _determinism_failure(
            result=result,
            reason="http_exception_detail_not_object",
        )
        return
    if detail.get("code") != "URM_ADEU_CORE_IR_PROPOSER_REQUEST_INVALID":
        _determinism_failure(
            result=result,
            reason="unexpected_mismatch_code",
            details={"observed_code": detail.get("code")},
        )
        return
    context = detail.get("context")
    if not isinstance(context, dict):
        _determinism_failure(
            result=result,
            reason="mismatch_context_not_object",
        )
        return
    if context.get("client_request_id") != expected_client_request_id:
        _determinism_failure(
            result=result,
            reason="mismatch_client_request_id_drift",
            details={"context": context},
        )
        return

    missing_context_fields = sorted(
        field for field in REQUIRED_MISMATCH_CONTEXT_FIELDS if field not in context
    )
    if missing_context_fields:
        _determinism_failure(
            result=result,
            reason="mismatch_context_fields_missing",
            details={"missing_fields": missing_context_fields},
        )


def _primary_probe_provider(api_main_module: Any) -> str:
    supported = tuple(
        api_main_module._provider_parity_supported_providers_by_surface().get(
            api_main_module._CORE_IR_PROPOSER_SURFACE_ID,
            (),
        )
    )
    if "mock" in supported:
        return "mock"
    if supported:
        return str(supported[0])
    return "mock"


def _run_determinism_probe(*, result: LintResult) -> None:
    import adeu_api.main as api_main
    from adeu_api.hashing import sha256_canonical_json
    from adeu_api.main import CoreIRProposerRequest, urm_core_ir_propose_endpoint

    previous_db_path = os.environ.get("ADEU_API_DB_PATH")

    with tempfile.TemporaryDirectory(prefix="v31g-persistence-lint-") as tmp_dir:
        db_path = Path(tmp_dir) / "api.sqlite3"
        os.environ["ADEU_API_DB_PATH"] = str(db_path)
        try:
            _normalize_cache_for_probe(api_main)

            provider = _primary_probe_provider(api_main)
            replay_request = CoreIRProposerRequest(
                schema="adeu_core_ir_proposer_request@0.1",
                client_request_id="v31g-lint-replay-1",
                provider=provider,
                source_text="The operator must log every override decision.",
            )
            first = urm_core_ir_propose_endpoint(replay_request).model_dump(mode="json")
            second = urm_core_ir_propose_endpoint(replay_request).model_dump(mode="json")
            if second != first:
                _determinism_failure(
                    result=result,
                    reason="replay_response_drift",
                )

            conflict_request = CoreIRProposerRequest(
                schema="adeu_core_ir_proposer_request@0.1",
                client_request_id="v31g-lint-replay-1",
                provider=provider,
                source_text="The operator may skip override logs when idle.",
            )
            try:
                _ = urm_core_ir_propose_endpoint(conflict_request)
                _determinism_failure(
                    result=result,
                    reason="semantic_conflict_not_rejected",
                )
            except HTTPException as exc:
                _require_mismatch_detail(
                    detail=exc.detail,
                    expected_client_request_id=conflict_request.client_request_id,
                    result=result,
                )

            mismatch_provider = "codex" if provider != "codex" else "mock"
            provider_request = CoreIRProposerRequest(
                schema="adeu_core_ir_proposer_request@0.1",
                client_request_id="v31g-lint-replay-1",
                provider=mismatch_provider,
                source_text="The operator must log every override decision.",
            )
            try:
                _ = urm_core_ir_propose_endpoint(provider_request)
                _determinism_failure(
                    result=result,
                    reason="provider_conflict_not_rejected",
                )
            except HTTPException as exc:
                _require_mismatch_detail(
                    detail=exc.detail,
                    expected_client_request_id=provider_request.client_request_id,
                    result=result,
                )

            _normalize_cache_for_probe(api_main)
            after_cache_reset = urm_core_ir_propose_endpoint(replay_request).model_dump(mode="json")
            if after_cache_reset != first:
                _determinism_failure(
                    result=result,
                    reason="cache_reset_replay_drift",
                )

            cache_only_request = CoreIRProposerRequest(
                schema="adeu_core_ir_proposer_request@0.1",
                client_request_id="v31g-lint-cache-only-1",
                provider=provider,
                source_text="The operator must log every override decision.",
            )
            cache_only_key = (
                api_main._CORE_IR_PROPOSER_SURFACE_ID,
                cache_only_request.client_request_id,
            )
            api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY[cache_only_key] = (
                api_main._CoreIRProposerIdempotencyRecord(
                    provider=cache_only_request.provider,
                    request_payload_hash=sha256_canonical_json(
                        cache_only_request.idempotency_payload()
                    ),
                    response_payload={"schema": "invalid.schema@0"},
                )
            )
            cache_only_response = urm_core_ir_propose_endpoint(cache_only_request).model_dump(
                mode="json"
            )
            if cache_only_response.get("schema") != "adeu_core_ir_proposer_response@0.1":
                _determinism_failure(
                    result=result,
                    reason="cache_present_outcome_not_persisted_backed",
                )
        except HTTPException as exc:
            _determinism_failure(
                result=result,
                reason="unexpected_http_exception",
                details={"status_code": exc.status_code, "detail": exc.detail},
            )
        except Exception as exc:
            _determinism_failure(
                result=result,
                reason="probe_runtime_exception",
                details={"error": str(exc)},
            )
        finally:
            if previous_db_path is None:
                os.environ.pop("ADEU_API_DB_PATH", None)
            else:
                os.environ["ADEU_API_DB_PATH"] = previous_db_path


def run_lint(*, lock_doc: Path, base_ref: str, repo_root: Path) -> LintResult:
    result = LintResult(
        lock_doc=str(lock_doc),
        base_ref=base_ref,
        repo_root=str(repo_root),
    )

    if not lock_doc.exists():
        result.add_failure(
            category="schema",
            code="LOCK_DOC_MISSING",
            details={"path": str(lock_doc)},
        )
        return result

    _validate_lock_doc_assertions(lock_doc=lock_doc, result=result)

    try:
        merge_base, changed_files = _changed_files_against_base_ref(
            base_ref=base_ref,
            repo_root=repo_root,
        )
        result.merge_base = merge_base
    except RuntimeError as exc:
        result.add_failure(
            category="base_ref",
            code="BASE_REF_UNAVAILABLE",
            details={"base_ref": base_ref, "error": str(exc)},
        )
        return result

    _check_diff_guards(changed_files=changed_files, result=result)
    _check_persistence_callgraph(repo_root=repo_root, result=result)
    _run_determinism_probe(result=result)

    return result


def main(argv: list[str]) -> int:
    args = _parse_args(argv)

    try:
        repo_root = (
            _resolve_repo_path(repo_root=Path.cwd(), value=args.repo_root)
            if args.repo_root is not None
            else _repo_root_from_script()
        )
    except FileNotFoundError as exc:
        result = LintResult(
            lock_doc=str(args.lock_doc),
            base_ref=args.base_ref,
            repo_root="<unresolved>",
        )
        result.add_failure(
            category="base_ref",
            code="BASE_REF_UNAVAILABLE",
            details={"base_ref": args.base_ref, "error": str(exc)},
        )
        print(canonical_json(result.to_payload()))
        return result.exit_code()

    lock_doc = _resolve_repo_path(repo_root=repo_root, value=args.lock_doc)
    result = run_lint(lock_doc=lock_doc, base_ref=args.base_ref, repo_root=repo_root)
    print(canonical_json(result.to_payload()))
    return result.exit_code()


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
