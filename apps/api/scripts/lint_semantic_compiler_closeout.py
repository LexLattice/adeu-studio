from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import yaml
from urm_runtime.hashing import canonical_json, sha256_canonical_json

LINT_SCHEMA = "semantic_compiler_closeout_lint@1"
CONTRACT_SCHEMA = "v32e_ci_closeout_contract@1"
METRIC_KEY_CONTINUITY_SCHEMA = "metric_key_continuity_assertion@1"
RUNTIME_OBSERVABILITY_COMPARISON_SCHEMA = "runtime_observability_comparison@1"
CI_WIRING_EVIDENCE_SCHEMA = "v32e_ci_wiring_evidence@1"

EXPECTED_REQUIRED_ARTIFACT_FAMILIES: tuple[str, ...] = (
    "v41_surface_snapshot",
    "v41_surface_diff",
    "v41_evidence_manifest",
    "v41_pr_splits_markdown",
    "v41_quality_dashboard",
    "v41_stop_gate_metrics",
)

EXPECTED_REQUIRED_SEMANTIC_ARTIFACT_SCHEMAS: dict[str, str] = {
    "v41_surface_snapshot": "semantic_compiler_surface_snapshot@0.1",
    "v41_surface_diff": "semantic_compiler_surface_diff@0.1",
    "v41_evidence_manifest": "semantic_compiler_evidence_manifest@0.1",
    "v41_stop_gate_metrics": "stop_gate_metrics@1",
}

EXPECTED_REQUIRED_BLOCK_SCHEMAS: tuple[str, ...] = (
    RUNTIME_OBSERVABILITY_COMPARISON_SCHEMA,
    METRIC_KEY_CONTINUITY_SCHEMA,
    CI_WIRING_EVIDENCE_SCHEMA,
)

EXPECTED_REQUIRED_CI_CHECK_IDENTITY_TUPLE: tuple[str, ...] = (
    "lint_entrypoint",
    "run_command_normalized",
    "working_directory_or_repo_root",
    "env_overrides_subset",
)

EXPECTED_NORMALIZATION_POLICY: dict[str, Any] = {
    "trim_outer_whitespace": True,
    "line_endings": "crlf_to_lf",
    "shell_quote_normalization": "forbidden",
}

EXPECTED_REQUIRED_ERROR_POLICY: dict[str, str] = {
    "required_contract_violations": "error",
    "optional_informational_fields": "warning_allowed_non_blocking",
    "required_violation_channel": "error_only_non_zero_exit",
    "required_error_namespace_warning_channel_use": "forbidden",
}

ALLOWED_FAILURE_CODES: tuple[str, ...] = (
    "MISSING_REQUIRED_SEMANTIC_COMPILER_ARTIFACT",
    "SEMANTIC_COMPILER_ARTIFACT_SCHEMA_MISMATCH",
    "SEMANTIC_COMPILER_ARTIFACT_HASH_MISMATCH",
    "REQUIRED_CLOSEOUT_BLOCK_MISSING",
    "STOP_GATE_METRIC_KEYSET_DRIFT",
    "CI_WIRING_COVERAGE_DRIFT",
    "CI_WIRING_COVERAGE_SIGNATURE_MISMATCH",
    "CI_WIRING_COVERAGE_NON_EXECUTABLE_TEXT_MATCH",
    "CI_WIRING_REQUIRED_CHECK_CONDITIONALLY_SKIPPED",
    "CI_WIRING_REQUIRED_CHECK_IDENTITY_TUPLE_DRIFT",
    "CI_WIRING_REQUIRED_LINT_INDIRECT_INVOCATION_DETECTED",
    "CI_WIRING_REQUIRED_LINT_USES_STEP_SUBSTITUTION_DETECTED",
    "CI_WIRING_RUN_COMMAND_NORMALIZATION_DRIFT",
    "REQUIRED_LINT_MISSING_OR_NOT_EXECUTED",
    "REQUIRED_CONTRACT_VIOLATION_REPORTED_AS_WARNING",
    "REQUIRED_STRUCTURAL_VIOLATION_CAPTURED_AS_WARNING_CHANNEL",
    "NEW_REQUIRED_SEMANTIC_COMPILER_ARTIFACT_FAMILY_INTRODUCED",
    "NEW_REQUIRED_SEMANTIC_COMPILER_ARTIFACT_SCHEMA_INTRODUCED",
)


@dataclass
class LintResult:
    checked_paths: list[str]
    failures: list[dict[str, Any]]

    def add_failure(self, *, code: str, details: dict[str, Any]) -> None:
        if code not in ALLOWED_FAILURE_CODES:
            raise ValueError(f"unsupported failure code: {code}")
        self.failures.append({"code": code, "details": details})

    def finalize(
        self,
        *,
        lock_doc: str,
        decision_doc: str,
        coverage_signature_sha256: str | None,
    ) -> dict[str, Any]:
        return {
            "schema": LINT_SCHEMA,
            "lock_doc": lock_doc,
            "decision_doc": decision_doc,
            "checked_paths": sorted(set(self.checked_paths)),
            "coverage_signature_sha256": coverage_signature_sha256,
            "failures": sorted(
                self.failures,
                key=lambda row: (row["code"], canonical_json(row["details"])),
            ),
        }


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Lint V32-E semantic-compiler closeout CI/docs wiring consistency "
            "for deterministic fail-closed enforcement."
        ),
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=None,
        help="Repository root path. Defaults to discovery from script location.",
    )
    parser.add_argument(
        "--lock-doc",
        type=Path,
        default=Path("docs/LOCKED_CONTINUATION_vNEXT_PLUS42.md"),
        help="Lock document path containing v32e_ci_closeout_contract@1.",
    )
    return parser.parse_args(argv)


def _repo_root_from_script() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        git_marker = parent / ".git"
        if git_marker.is_dir() or git_marker.is_file():
            return parent
    raise FileNotFoundError("repository root not found from script location")


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> Any:
    return json.loads(_read_text(path))


def _read_json_object(path: Path) -> dict[str, Any]:
    payload = _read_json(path)
    if not isinstance(payload, dict):
        raise ValueError("json payload must be an object")
    return payload


def _is_safe_repo_relative_path(path_text: str) -> bool:
    if not path_text:
        return False
    if "\\" in path_text:
        return False
    if path_text.startswith("/"):
        return False
    if ".." in path_text.split("/"):
        return False
    return True


def _extract_json_fenced_blocks(text: str) -> list[str]:
    blocks: list[str] = []
    lines = text.splitlines()
    idx = 0
    while idx < len(lines):
        if lines[idx].strip() != "```json":
            idx += 1
            continue
        idx += 1
        block_lines: list[str] = []
        while idx < len(lines) and lines[idx].strip() != "```":
            block_lines.append(lines[idx])
            idx += 1
        if idx >= len(lines):
            break
        blocks.append("\n".join(block_lines).strip())
        idx += 1
    return blocks


def _extract_schema_blocks(text: str) -> dict[str, list[dict[str, Any]]]:
    by_schema: dict[str, list[dict[str, Any]]] = {}
    for block in _extract_json_fenced_blocks(text):
        try:
            payload = json.loads(block)
        except json.JSONDecodeError:
            continue
        if not isinstance(payload, dict):
            continue
        schema = payload.get("schema")
        if not isinstance(schema, str):
            continue
        by_schema.setdefault(schema, []).append(payload)
    return by_schema


def _require_single_schema_block(
    *,
    blocks_by_schema: dict[str, list[dict[str, Any]]],
    schema: str,
    result: LintResult,
    code: str,
    context: str,
) -> dict[str, Any] | None:
    blocks = blocks_by_schema.get(schema, [])
    if len(blocks) != 1:
        result.add_failure(
            code=code,
            details={"context": context, "schema": schema, "count": len(blocks)},
        )
        return None
    return blocks[0]


def _normalize_run_command(raw: str) -> str:
    normalized = raw.replace("\r\n", "\n").replace("\r", "\n")
    return normalized.strip()


def _collapsed_run_command(raw: str) -> str:
    normalized = _normalize_run_command(raw)
    return re.sub(r"\\\n\s*", " ", normalized)


def _normalize_condition_expression(raw: str) -> str:
    normalized = raw.strip()
    if normalized.startswith("${{") and normalized.endswith("}}"):
        normalized = normalized[3:-2].strip()
    normalized = normalized.replace('"', "'")
    return re.sub(r"\s+", " ", normalized)


def _matches_python_scope_guard(*, raw: str, expected_scope: str) -> bool:
    return _normalize_condition_expression(raw) == (
        f"steps.python_scope.outputs.scope == '{expected_scope}'"
    )


def _arc_closeout_bridge_present(*, steps: list[Any]) -> bool:
    for step in steps:
        if not isinstance(step, dict):
            continue
        run_value = step.get("run")
        if not isinstance(run_value, str):
            continue
        if not re.search(r"(^|[\n;&|])\s*make\s+arc-closeout-check(\s|$)", run_value):
            continue
        condition = step.get("if")
        if isinstance(condition, str) and _matches_python_scope_guard(
            raw=condition,
            expected_scope="arc_closeout",
        ):
            return True
    return False


def _direct_python_lint_invocation_present(*, run_command: str, lint_entrypoint: str) -> bool:
    collapsed = _collapsed_run_command(run_command)
    pattern = re.compile(
        r"(^|[\n;&|])\s*"
        r"(?:[A-Z_][A-Z0-9_]*=[^\s;&|]+\s+)*"
        r"(?:\.venv/bin/python|python3?|python)\s+"
        + re.escape(lint_entrypoint)
        + r"(?=$|[\s;&|])"
    )
    return bool(pattern.search(collapsed))


def _canonical_json_sha256_from_file(path: Path) -> str:
    payload = _read_json(path)
    if not isinstance(payload, dict):
        raise ValueError("artifact payload must be a JSON object")
    return sha256_canonical_json(payload)


def _load_lock_contract(
    *,
    repo_root: Path,
    lock_doc_path: Path,
    result: LintResult,
) -> tuple[dict[str, Any] | None, str]:
    resolved_lock_doc = (
        lock_doc_path.resolve()
        if lock_doc_path.is_absolute()
        else (repo_root / lock_doc_path).resolve()
    )
    result.checked_paths.append(str(resolved_lock_doc.relative_to(repo_root)))
    if not resolved_lock_doc.is_file():
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "lock_doc_missing", "path": str(lock_doc_path)},
        )
        return None, str(lock_doc_path)
    blocks = _extract_schema_blocks(_read_text(resolved_lock_doc))
    payload = _require_single_schema_block(
        blocks_by_schema=blocks,
        schema=CONTRACT_SCHEMA,
        result=result,
        code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
        context="lock_contract_block",
    )
    return payload, str(resolved_lock_doc.relative_to(repo_root))


def _validate_artifact_family_scope_policy(
    *,
    contract: dict[str, Any],
    result: LintResult,
) -> None:
    input_artifacts = contract.get("input_artifacts")
    if not isinstance(input_artifacts, dict):
        result.add_failure(
            code="NEW_REQUIRED_SEMANTIC_COMPILER_ARTIFACT_FAMILY_INTRODUCED",
            details={"reason": "input_artifacts_not_object"},
        )
        return

    artifact_keys = set(input_artifacts.keys())
    expected_keys = set(EXPECTED_REQUIRED_ARTIFACT_FAMILIES)
    if artifact_keys != expected_keys:
        result.add_failure(
            code="NEW_REQUIRED_SEMANTIC_COMPILER_ARTIFACT_FAMILY_INTRODUCED",
            details={"expected": sorted(expected_keys), "actual": sorted(artifact_keys)},
        )

    scope_policy = contract.get("semantic_compiler_artifact_family_scope_policy")
    if not isinstance(scope_policy, dict):
        result.add_failure(
            code="NEW_REQUIRED_SEMANTIC_COMPILER_ARTIFACT_FAMILY_INTRODUCED",
            details={"reason": "artifact_scope_policy_not_object"},
        )
        return

    verified_families = scope_policy.get("verified_required_families")
    if verified_families != list(EXPECTED_REQUIRED_ARTIFACT_FAMILIES):
        result.add_failure(
            code="NEW_REQUIRED_SEMANTIC_COMPILER_ARTIFACT_FAMILY_INTRODUCED",
            details={
                "field": "verified_required_families",
                "expected": list(EXPECTED_REQUIRED_ARTIFACT_FAMILIES),
                "actual": verified_families,
            },
        )

    if scope_policy.get("new_required_semantic_compiler_artifact_families") != "forbidden_non_v42":
        result.add_failure(
            code="NEW_REQUIRED_SEMANTIC_COMPILER_ARTIFACT_FAMILY_INTRODUCED",
            details={
                "field": "new_required_semantic_compiler_artifact_families",
                "actual": scope_policy.get("new_required_semantic_compiler_artifact_families"),
            },
        )
    if (
        scope_policy.get("new_required_semantic_compiler_artifact_schema_ids")
        != "forbidden_non_v42"
    ):
        result.add_failure(
            code="NEW_REQUIRED_SEMANTIC_COMPILER_ARTIFACT_SCHEMA_INTRODUCED",
            details={
                "field": "new_required_semantic_compiler_artifact_schema_ids",
                "actual": scope_policy.get("new_required_semantic_compiler_artifact_schema_ids"),
            },
        )


def _load_required_artifacts(
    *,
    repo_root: Path,
    contract: dict[str, Any],
    result: LintResult,
) -> tuple[dict[str, Path], dict[str, str]]:
    loaded: dict[str, Path] = {}
    canonical_hashes: dict[str, str] = {}
    input_artifacts = contract.get("input_artifacts", {})
    if not isinstance(input_artifacts, dict):
        return loaded, canonical_hashes

    for key in EXPECTED_REQUIRED_ARTIFACT_FAMILIES:
        path_text = input_artifacts.get(key)
        if not isinstance(path_text, str) or not _is_safe_repo_relative_path(path_text):
            result.add_failure(
                code="MISSING_REQUIRED_SEMANTIC_COMPILER_ARTIFACT",
                details={"artifact": key, "path": path_text},
            )
            continue
        artifact_path = repo_root / path_text
        result.checked_paths.append(path_text)
        if not artifact_path.is_file():
            result.add_failure(
                code="MISSING_REQUIRED_SEMANTIC_COMPILER_ARTIFACT",
                details={"artifact": key, "path": path_text},
            )
            continue
        loaded[key] = artifact_path

    for key, expected_schema in EXPECTED_REQUIRED_SEMANTIC_ARTIFACT_SCHEMAS.items():
        artifact_path = loaded.get(key)
        if artifact_path is None:
            continue
        try:
            payload = _read_json_object(artifact_path)
        except (json.JSONDecodeError, ValueError):
            result.add_failure(
                code="SEMANTIC_COMPILER_ARTIFACT_SCHEMA_MISMATCH",
                details={"artifact": key, "path": str(artifact_path.relative_to(repo_root))},
            )
            continue
        actual_schema = payload.get("schema")
        if actual_schema != expected_schema:
            result.add_failure(
                code="SEMANTIC_COMPILER_ARTIFACT_SCHEMA_MISMATCH",
                details={
                    "artifact": key,
                    "path": str(artifact_path.relative_to(repo_root)),
                    "expected_schema": expected_schema,
                    "actual_schema": actual_schema,
                },
            )
        try:
            canonical_hashes[key] = _canonical_json_sha256_from_file(artifact_path)
        except (json.JSONDecodeError, ValueError):
            result.add_failure(
                code="SEMANTIC_COMPILER_ARTIFACT_HASH_MISMATCH",
                details={
                    "artifact": key,
                    "path": str(artifact_path.relative_to(repo_root)),
                    "reason": "canonical_json_hash_unavailable",
                },
            )

    return loaded, canonical_hashes


def _validate_required_error_policy(*, contract: dict[str, Any], result: LintResult) -> None:
    policy = contract.get("closeout_lint_severity_policy")
    if not isinstance(policy, dict):
        result.add_failure(
            code="REQUIRED_STRUCTURAL_VIOLATION_CAPTURED_AS_WARNING_CHANNEL",
            details={"reason": "closeout_lint_severity_policy_not_object"},
        )
        return
    for key, expected in EXPECTED_REQUIRED_ERROR_POLICY.items():
        if policy.get(key) != expected:
            code = (
                "REQUIRED_CONTRACT_VIOLATION_REPORTED_AS_WARNING"
                if key == "required_contract_violations"
                else "REQUIRED_STRUCTURAL_VIOLATION_CAPTURED_AS_WARNING_CHANNEL"
            )
            result.add_failure(
                code=code,
                details={"field": key, "expected": expected, "actual": policy.get(key)},
            )


def _validate_coverage_policy_contract(*, contract: dict[str, Any], result: LintResult) -> None:
    ci_wiring = contract.get("ci_wiring")
    if not isinstance(ci_wiring, dict):
        result.add_failure(
            code="CI_WIRING_COVERAGE_DRIFT",
            details={"reason": "ci_wiring_not_object"},
        )
        return
    coverage = ci_wiring.get("coverage_signature_policy")
    if not isinstance(coverage, dict):
        result.add_failure(
            code="CI_WIRING_COVERAGE_DRIFT",
            details={"reason": "coverage_signature_policy_not_object"},
        )
        return

    identity_tuple = coverage.get("required_check_identity_tuple")
    if identity_tuple != list(EXPECTED_REQUIRED_CI_CHECK_IDENTITY_TUPLE):
        result.add_failure(
            code="CI_WIRING_REQUIRED_CHECK_IDENTITY_TUPLE_DRIFT",
            details={
                "expected": list(EXPECTED_REQUIRED_CI_CHECK_IDENTITY_TUPLE),
                "actual": identity_tuple,
            },
        )

    normalization = coverage.get("run_command_normalization")
    if normalization != EXPECTED_NORMALIZATION_POLICY:
        result.add_failure(
            code="CI_WIRING_RUN_COMMAND_NORMALIZATION_DRIFT",
            details={"expected": EXPECTED_NORMALIZATION_POLICY, "actual": normalization},
        )

    if coverage.get("uses_step_substitution_for_required_lints") != "forbidden_non_v42":
        result.add_failure(
            code="CI_WIRING_REQUIRED_LINT_USES_STEP_SUBSTITUTION_DETECTED",
            details={"actual": coverage.get("uses_step_substitution_for_required_lints")},
        )
    if coverage.get("indirect_wrapper_invocation") != "forbidden_non_v42":
        result.add_failure(
            code="CI_WIRING_REQUIRED_LINT_INDIRECT_INVOCATION_DETECTED",
            details={"actual": coverage.get("indirect_wrapper_invocation")},
        )


def _load_stop_gate_metrics(
    *,
    repo_root: Path,
    path_text: str,
    result: LintResult,
) -> dict[str, Any] | None:
    if not _is_safe_repo_relative_path(path_text):
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "metrics_path_invalid", "path": path_text},
        )
        return None
    path = repo_root / path_text
    result.checked_paths.append(path_text)
    if not path.is_file():
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "metrics_path_missing", "path": path_text},
        )
        return None
    try:
        payload = _read_json_object(path)
    except (json.JSONDecodeError, ValueError):
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "metrics_payload_invalid", "path": path_text},
        )
        return None
    if payload.get("schema") != "stop_gate_metrics@1":
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "metrics_schema_mismatch", "path": path_text},
        )
        return None
    if not isinstance(payload.get("metrics"), dict):
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "metrics_object_missing", "path": path_text},
        )
        return None
    return payload


def _validate_metric_continuity_block(
    *,
    repo_root: Path,
    block: dict[str, Any],
    contract: dict[str, Any],
    result: LintResult,
) -> tuple[dict[str, Any] | None, dict[str, Any] | None]:
    expected_keys = {
        "schema",
        "baseline_metrics_path",
        "current_metrics_path",
        "expected_relation",
    }
    if set(block.keys()) != expected_keys:
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "metric_continuity_keys_invalid"},
        )
        return None, None
    if block.get("expected_relation") != "exact_keyset_equality":
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "metric_continuity_expected_relation_invalid"},
        )
        return None, None
    baseline_path = block.get("baseline_metrics_path")
    current_path = block.get("current_metrics_path")
    if not isinstance(baseline_path, str) or not isinstance(current_path, str):
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "metric_continuity_paths_not_strings"},
        )
        return None, None

    expected_baseline = contract.get("input_artifacts", {}).get("v41_stop_gate_metrics")
    if isinstance(expected_baseline, str) and baseline_path != expected_baseline:
        result.add_failure(
            code="STOP_GATE_METRIC_KEYSET_DRIFT",
            details={
                "context": "baseline_metrics_path_drift",
                "expected": expected_baseline,
                "actual": baseline_path,
            },
        )

    baseline_payload = _load_stop_gate_metrics(
        repo_root=repo_root,
        path_text=baseline_path,
        result=result,
    )
    current_payload = _load_stop_gate_metrics(
        repo_root=repo_root,
        path_text=current_path,
        result=result,
    )
    if baseline_payload is None or current_payload is None:
        return None, None

    baseline_keys = set(baseline_payload["metrics"].keys())
    current_keys = set(current_payload["metrics"].keys())
    if baseline_keys != current_keys:
        result.add_failure(
            code="STOP_GATE_METRIC_KEYSET_DRIFT",
            details={"context": "metric_keyset_mismatch"},
        )

    expected_cardinality = (
        contract.get("stop_gate_continuity_policy", {}).get("expected_cardinality")
    )
    if isinstance(expected_cardinality, int) and len(current_keys) != expected_cardinality:
        result.add_failure(
            code="STOP_GATE_METRIC_KEYSET_DRIFT",
            details={
                "context": "metric_key_cardinality_drift",
                "expected_cardinality": expected_cardinality,
                "actual_cardinality": len(current_keys),
            },
        )

    return baseline_payload, current_payload


def _validate_runtime_observability_block(
    *,
    repo_root: Path,
    block: dict[str, Any],
    baseline_metrics: dict[str, Any] | None,
    current_metrics: dict[str, Any] | None,
    result: LintResult,
) -> None:
    required_keys = {
        "schema",
        "baseline_arc",
        "current_arc",
        "baseline_source",
        "current_source",
        "baseline_elapsed_ms",
        "current_elapsed_ms",
        "delta_ms",
        "notes",
    }
    if set(block.keys()) != required_keys:
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "runtime_observability_keys_invalid"},
        )
        return

    baseline_source = block.get("baseline_source")
    current_source = block.get("current_source")
    if not isinstance(baseline_source, str) or not isinstance(current_source, str):
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "runtime_observability_sources_not_strings"},
        )
        return
    for source_path in (baseline_source, current_source):
        if not _is_safe_repo_relative_path(source_path):
            result.add_failure(
                code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
                details={
                    "context": "runtime_observability_source_path_invalid",
                    "path": source_path,
                },
            )
            continue
        full_path = repo_root / source_path
        result.checked_paths.append(source_path)
        if not full_path.is_file():
            result.add_failure(
                code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
                details={"context": "runtime_observability_source_missing", "path": source_path},
            )

    numeric_fields = ("baseline_elapsed_ms", "current_elapsed_ms", "delta_ms")
    for field in numeric_fields:
        value = block.get(field)
        if not isinstance(value, int) or isinstance(value, bool):
            result.add_failure(
                code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
                details={"context": "runtime_observability_numeric_field_invalid", "field": field},
            )
            return

    baseline_elapsed = block["baseline_elapsed_ms"]
    current_elapsed = block["current_elapsed_ms"]
    if block["delta_ms"] != current_elapsed - baseline_elapsed:
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "runtime_observability_delta_invalid"},
        )

    if baseline_metrics is None or current_metrics is None:
        return
    baseline_runtime = baseline_metrics.get("runtime_observability", {})
    current_runtime = current_metrics.get("runtime_observability", {})
    if isinstance(baseline_runtime, dict):
        expected = baseline_runtime.get("elapsed_ms")
        if isinstance(expected, int) and expected != baseline_elapsed:
            result.add_failure(
                code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
                details={
                    "context": "runtime_observability_baseline_elapsed_mismatch",
                    "expected": expected,
                    "actual": baseline_elapsed,
                },
            )
    if isinstance(current_runtime, dict):
        expected = current_runtime.get("elapsed_ms")
        if isinstance(expected, int) and expected != current_elapsed:
            result.add_failure(
                code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
                details={
                    "context": "runtime_observability_current_elapsed_mismatch",
                    "expected": expected,
                    "actual": current_elapsed,
                },
            )


def _effective_env_for_step(*, job: dict[str, Any], step: dict[str, Any]) -> dict[str, str]:
    effective: dict[str, str] = {}
    for source in (job.get("env"), step.get("env")):
        if not isinstance(source, dict):
            continue
        for key, value in source.items():
            if isinstance(key, str) and isinstance(value, str):
                effective[key] = value
    return effective


def _working_directory_for_step(*, job: dict[str, Any], step: dict[str, Any]) -> str:
    step_value = step.get("working-directory")
    if isinstance(step_value, str) and step_value.strip() != "":
        return step_value.strip()
    defaults = job.get("defaults")
    if isinstance(defaults, dict):
        run_defaults = defaults.get("run")
        if isinstance(run_defaults, dict):
            run_value = run_defaults.get("working-directory")
            if isinstance(run_value, str) and run_value.strip() != "":
                return run_value.strip()
    return "."


def _compute_required_check_identity(
    *,
    contract: dict[str, Any],
    workflow_payload: dict[str, Any],
    result: LintResult,
) -> tuple[list[dict[str, Any]], str | None]:
    ci_wiring = contract.get("ci_wiring")
    if not isinstance(ci_wiring, dict):
        return [], None
    required_lane = ci_wiring.get("required_lane")
    required_lints = ci_wiring.get("required_lints")
    deterministic_env = ci_wiring.get("deterministic_env")

    if not isinstance(required_lane, str):
        result.add_failure(
            code="CI_WIRING_COVERAGE_DRIFT",
            details={"reason": "required_lane_invalid"},
        )
        return [], None
    if not isinstance(required_lints, list) or not all(isinstance(x, str) for x in required_lints):
        result.add_failure(
            code="CI_WIRING_COVERAGE_DRIFT",
            details={"reason": "required_lints_invalid"},
        )
        return [], None
    if not isinstance(deterministic_env, dict):
        result.add_failure(
            code="CI_WIRING_COVERAGE_DRIFT",
            details={"reason": "deterministic_env_invalid"},
        )
        return [], None

    jobs = workflow_payload.get("jobs")
    if not isinstance(jobs, dict):
        result.add_failure(
            code="CI_WIRING_COVERAGE_DRIFT",
            details={"reason": "workflow_jobs_invalid"},
        )
        return [], None
    job = jobs.get(required_lane)
    if not isinstance(job, dict):
        result.add_failure(
            code="CI_WIRING_COVERAGE_DRIFT",
            details={"reason": "required_lane_missing", "lane": required_lane},
        )
        return [], None
    steps = job.get("steps")
    if not isinstance(steps, list):
        result.add_failure(
            code="CI_WIRING_COVERAGE_DRIFT",
            details={"reason": "required_lane_steps_invalid"},
        )
        return [], None

    identity_rows: list[dict[str, Any]] = []
    for lint_entrypoint in required_lints:
        matched_step: dict[str, Any] | None = None
        non_executable_match = False
        for step in steps:
            if not isinstance(step, dict):
                continue
            run_value = step.get("run")
            if not isinstance(run_value, str):
                uses = step.get("uses")
                if isinstance(uses, str) and lint_entrypoint in uses:
                    result.add_failure(
                        code="CI_WIRING_REQUIRED_LINT_USES_STEP_SUBSTITUTION_DETECTED",
                        details={"lint_entrypoint": lint_entrypoint, "uses": uses},
                    )
                continue
            if lint_entrypoint in run_value and not _direct_python_lint_invocation_present(
                run_command=run_value,
                lint_entrypoint=lint_entrypoint,
            ):
                non_executable_match = True
                continue
            if _direct_python_lint_invocation_present(
                run_command=run_value,
                lint_entrypoint=lint_entrypoint,
            ):
                matched_step = step
                break

        if non_executable_match:
            result.add_failure(
                code="CI_WIRING_COVERAGE_NON_EXECUTABLE_TEXT_MATCH",
                details={"lint_entrypoint": lint_entrypoint},
            )

        if matched_step is None:
            for step in steps:
                if not isinstance(step, dict):
                    continue
                run_value = step.get("run")
                if isinstance(run_value, str) and re.search(
                    r"(^|[\n;&|])\s*make\s+lint(\s|$)",
                    run_value,
                ):
                    result.add_failure(
                        code="CI_WIRING_REQUIRED_LINT_INDIRECT_INVOCATION_DETECTED",
                        details={
                            "lint_entrypoint": lint_entrypoint,
                            "run": _normalize_run_command(run_value),
                        },
                    )
                    break
            result.add_failure(
                code="REQUIRED_LINT_MISSING_OR_NOT_EXECUTED",
                details={"lint_entrypoint": lint_entrypoint},
            )
            continue

        if "if" in matched_step:
            raw_if = matched_step.get("if")
            allow_docs_only_bridge = isinstance(raw_if, str) and _matches_python_scope_guard(
                raw=raw_if,
                expected_scope="full",
            ) and _arc_closeout_bridge_present(steps=steps)
            if allow_docs_only_bridge:
                raw_if = None
            if raw_if is not None:
                result.add_failure(
                    code="CI_WIRING_REQUIRED_CHECK_CONDITIONALLY_SKIPPED",
                    details={"lint_entrypoint": lint_entrypoint, "if": matched_step.get("if")},
                )

        run_value = matched_step.get("run")
        if not isinstance(run_value, str):
            continue

        effective_env = _effective_env_for_step(job=job, step=matched_step)
        env_subset: dict[str, str] = {}
        for key, expected in deterministic_env.items():
            if not isinstance(key, str) or not isinstance(expected, str):
                continue
            actual = effective_env.get(key)
            if actual != expected:
                result.add_failure(
                    code="CI_WIRING_COVERAGE_DRIFT",
                    details={
                        "context": "deterministic_env_mismatch",
                        "lint_entrypoint": lint_entrypoint,
                        "key": key,
                        "expected": expected,
                        "actual": actual,
                    },
                )
            env_subset[key] = "" if actual is None else actual

        identity_rows.append(
            {
                "lint_entrypoint": lint_entrypoint,
                "run_command_normalized": _normalize_run_command(run_value),
                "working_directory_or_repo_root": _working_directory_for_step(
                    job=job,
                    step=matched_step,
                ),
                "env_overrides_subset": env_subset,
            }
        )

    sorted_rows = sorted(identity_rows, key=lambda row: canonical_json(row))
    if not sorted_rows:
        return sorted_rows, None
    return sorted_rows, sha256_canonical_json(sorted_rows)


def _validate_closeout_decision_doc(
    *,
    repo_root: Path,
    contract: dict[str, Any],
    result: LintResult,
    canonical_hashes: dict[str, str],
) -> tuple[str | None, str | None]:
    closeout_policy = contract.get("closeout_doc_policy")
    if not isinstance(closeout_policy, dict):
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "closeout_doc_policy_not_object"},
        )
        return None, None
    decision_doc = closeout_policy.get("decision_doc")
    if not isinstance(decision_doc, str) or not _is_safe_repo_relative_path(decision_doc):
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "decision_doc_path_invalid", "decision_doc": decision_doc},
        )
        return None, None
    decision_path = repo_root / decision_doc
    result.checked_paths.append(decision_doc)
    if not decision_path.is_file():
        result.add_failure(
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            details={"context": "decision_doc_missing", "decision_doc": decision_doc},
        )
        return decision_doc, None

    blocks = _extract_schema_blocks(_read_text(decision_path))
    for schema in EXPECTED_REQUIRED_BLOCK_SCHEMAS:
        _require_single_schema_block(
            blocks_by_schema=blocks,
            schema=schema,
            result=result,
            code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
            context="required_closeout_json_blocks",
        )

    metric_block = _require_single_schema_block(
        blocks_by_schema=blocks,
        schema=METRIC_KEY_CONTINUITY_SCHEMA,
        result=result,
        code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
        context="metric_key_continuity",
    )
    runtime_block = _require_single_schema_block(
        blocks_by_schema=blocks,
        schema=RUNTIME_OBSERVABILITY_COMPARISON_SCHEMA,
        result=result,
        code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
        context="runtime_observability_comparison",
    )
    evidence_block = _require_single_schema_block(
        blocks_by_schema=blocks,
        schema=CI_WIRING_EVIDENCE_SCHEMA,
        result=result,
        code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
        context="v32e_ci_wiring_evidence",
    )

    baseline_metrics: dict[str, Any] | None = None
    current_metrics: dict[str, Any] | None = None
    if metric_block is not None:
        baseline_metrics, current_metrics = _validate_metric_continuity_block(
            repo_root=repo_root,
            block=metric_block,
            contract=contract,
            result=result,
        )
    if runtime_block is not None:
        _validate_runtime_observability_block(
            repo_root=repo_root,
            block=runtime_block,
            baseline_metrics=baseline_metrics,
            current_metrics=current_metrics,
            result=result,
        )

    coverage_signature_sha256: str | None = None
    if evidence_block is not None:
        required_keys = {
            "schema",
            "lint_entrypoint",
            "workflow_path",
            "required_lane",
            "coverage_signature_sha256",
            "required_lints",
            "closeout_doc",
            "required_blocks_present",
            "artifact_hashes_verified",
            "metric_key_cardinality",
            "metric_key_exact_set_equal_v41",
            "notes",
        }
        if set(evidence_block.keys()) != required_keys:
            result.add_failure(
                code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
                details={"context": "v32e_ci_wiring_evidence_keys_invalid"},
            )
            return decision_doc, None

        ci_wiring = contract.get("ci_wiring", {})
        for field, expected in (
            ("lint_entrypoint", ci_wiring.get("lint_entrypoint")),
            ("workflow_path", ci_wiring.get("workflow_authority")),
            ("required_lane", ci_wiring.get("required_lane")),
            ("closeout_doc", decision_doc),
        ):
            if evidence_block.get(field) != expected:
                result.add_failure(
                    code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
                    details={"context": "v32e_ci_wiring_evidence_field_mismatch", "field": field},
                )

        required_lints = ci_wiring.get("required_lints")
        if not isinstance(required_lints, list):
            result.add_failure(
                code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
                details={"context": "required_lints_contract_invalid"},
            )
        else:
            actual_required_lints = evidence_block.get("required_lints")
            if not isinstance(actual_required_lints, list):
                result.add_failure(
                    code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
                    details={"context": "required_lints_block_invalid"},
                )
            else:
                if set(actual_required_lints) != set(required_lints):
                    result.add_failure(
                        code="REQUIRED_LINT_MISSING_OR_NOT_EXECUTED",
                        details={
                            "context": "required_lints_set_mismatch",
                            "expected": sorted(required_lints),
                            "actual": sorted(actual_required_lints),
                        },
                    )

        if evidence_block.get("required_blocks_present") is not True:
            result.add_failure(
                code="REQUIRED_CLOSEOUT_BLOCK_MISSING",
                details={"context": "required_blocks_present_not_true"},
            )
        if evidence_block.get("artifact_hashes_verified") is not True:
            result.add_failure(
                code="SEMANTIC_COMPILER_ARTIFACT_HASH_MISMATCH",
                details={"context": "artifact_hashes_verified_not_true"},
            )
        for artifact_key, digest in canonical_hashes.items():
            if not re.fullmatch(r"[0-9a-f]{64}", digest):
                result.add_failure(
                    code="SEMANTIC_COMPILER_ARTIFACT_HASH_MISMATCH",
                    details={"context": "canonical_hash_invalid", "artifact": artifact_key},
                )
        expected_cardinality = contract.get(
            "stop_gate_continuity_policy",
            {},
        ).get("expected_cardinality")
        if evidence_block.get("metric_key_cardinality") != expected_cardinality:
            result.add_failure(
                code="STOP_GATE_METRIC_KEYSET_DRIFT",
                details={"context": "metric_key_cardinality_mismatch"},
            )
        if evidence_block.get("metric_key_exact_set_equal_v41") is not True:
            result.add_failure(
                code="STOP_GATE_METRIC_KEYSET_DRIFT",
                details={"context": "metric_key_exact_set_equal_v41_not_true"},
            )

        coverage_value = evidence_block.get("coverage_signature_sha256")
        if not isinstance(coverage_value, str) or not re.fullmatch(r"[0-9a-f]{64}", coverage_value):
            result.add_failure(
                code="CI_WIRING_COVERAGE_SIGNATURE_MISMATCH",
                details={"context": "coverage_signature_sha256_invalid"},
            )
        else:
            coverage_signature_sha256 = coverage_value

        workflow_path_text = ci_wiring.get("workflow_authority")
        if not isinstance(workflow_path_text, str) or not _is_safe_repo_relative_path(
            workflow_path_text
        ):
            result.add_failure(
                code="CI_WIRING_COVERAGE_DRIFT",
                details={"reason": "workflow_authority_path_invalid"},
            )
            return decision_doc, coverage_signature_sha256
        workflow_path = repo_root / workflow_path_text
        result.checked_paths.append(workflow_path_text)
        if not workflow_path.is_file():
            result.add_failure(
                code="CI_WIRING_COVERAGE_DRIFT",
                details={"reason": "workflow_authority_missing", "path": workflow_path_text},
            )
            return decision_doc, coverage_signature_sha256

        try:
            workflow_payload = yaml.safe_load(_read_text(workflow_path))
        except yaml.YAMLError:
            result.add_failure(
                code="CI_WIRING_COVERAGE_DRIFT",
                details={"reason": "workflow_yaml_invalid"},
            )
            return decision_doc, coverage_signature_sha256
        if not isinstance(workflow_payload, dict):
            result.add_failure(
                code="CI_WIRING_COVERAGE_DRIFT",
                details={"reason": "workflow_payload_not_object"},
            )
            return decision_doc, coverage_signature_sha256

        rows, computed_signature = _compute_required_check_identity(
            contract=contract,
            workflow_payload=workflow_payload,
            result=result,
        )
        if not rows:
            result.add_failure(
                code="CI_WIRING_COVERAGE_DRIFT",
                details={"reason": "required_check_identity_empty"},
            )
        if computed_signature is None:
            result.add_failure(
                code="CI_WIRING_COVERAGE_SIGNATURE_MISMATCH",
                details={"reason": "coverage_signature_unavailable"},
            )
        elif (
            coverage_signature_sha256 is not None
            and computed_signature != coverage_signature_sha256
        ):
            result.add_failure(
                code="CI_WIRING_COVERAGE_SIGNATURE_MISMATCH",
                details={"expected": coverage_signature_sha256, "actual": computed_signature},
            )
            coverage_signature_sha256 = computed_signature

    return decision_doc, coverage_signature_sha256


def lint_semantic_compiler_closeout(
    *,
    repo_root: Path,
    lock_doc: Path,
) -> dict[str, Any]:
    result = LintResult(checked_paths=[], failures=[])

    contract, lock_doc_display = _load_lock_contract(
        repo_root=repo_root,
        lock_doc_path=lock_doc,
        result=result,
    )
    coverage_signature_sha256: str | None = None
    decision_doc_display = "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS42.md"
    if contract is None:
        return result.finalize(
            lock_doc=lock_doc_display,
            decision_doc=decision_doc_display,
            coverage_signature_sha256=coverage_signature_sha256,
        )

    _validate_artifact_family_scope_policy(contract=contract, result=result)
    _validate_required_error_policy(contract=contract, result=result)
    _validate_coverage_policy_contract(contract=contract, result=result)

    required_artifacts, canonical_hashes = _load_required_artifacts(
        repo_root=repo_root,
        contract=contract,
        result=result,
    )
    if "v41_pr_splits_markdown" not in required_artifacts:
        result.add_failure(
            code="MISSING_REQUIRED_SEMANTIC_COMPILER_ARTIFACT",
            details={"artifact": "v41_pr_splits_markdown"},
        )

    decision_doc, coverage_signature_sha256 = _validate_closeout_decision_doc(
        repo_root=repo_root,
        contract=contract,
        result=result,
        canonical_hashes=canonical_hashes,
    )
    if isinstance(decision_doc, str):
        decision_doc_display = decision_doc

    return result.finalize(
        lock_doc=lock_doc_display,
        decision_doc=decision_doc_display,
        coverage_signature_sha256=coverage_signature_sha256,
    )


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = args.repo_root.resolve() if args.repo_root is not None else _repo_root_from_script()
    payload = lint_semantic_compiler_closeout(
        repo_root=repo_root,
        lock_doc=args.lock_doc,
    )
    sys.stdout.write(canonical_json(payload) + "\n")
    return 1 if payload["failures"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
