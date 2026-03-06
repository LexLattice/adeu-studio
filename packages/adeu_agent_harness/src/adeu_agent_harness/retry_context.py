from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json, sha256_canonical_json

from . import run_taskpack as runner_mod

RETRY_CONTEXT_FEEDER_RESULT_SCHEMA = "retry_context_feeder_result@1"
RETRY_CONTEXT_SANITIZATION_PROFILE_SCHEMA = "retry_context_sanitization_profile@1"
RETRY_CONTEXT_OUTPUT_SCHEMA = "retry_context_feeder_output@1"
RETRY_CONTEXT_ERROR_SCHEMA = "taskpack_retry_context_error@1"
DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT = "artifacts/agent_harness/v52/retry_context"

SHARED_FEEDER_ENGINE = "adeu_agent_harness.retry_context.generate_retry_context"
SHARED_FEEDER_ENGINE_IDENTIFIER = (
    "v34d_retry_context_feeder_engine@1:"
    "adeu_agent_harness.retry_context.generate_retry_context"
)

ISSUE_TUPLE_FIELDS = ("issue_code", "target_path", "hunk_index", "policy_source")
DETERMINISTIC_ISSUE_ORDER_POLICY = (
    "lexicographic_over_issue_code_target_path_hunk_index_policy_source"
)
TARGET_PATH_NORMALIZATION_POLICY = "repo_relative_posix"
POLICY_SOURCE_POLICY = (
    "closed_inherited_surface_from_candidate_change_plan_rejection_diagnostic_contract_no_v52_expansion"
)
ADVISORY_ONLY_POLICY = (
    "retry_context_feeder_result_is_non_authoritative_and_must_not_be_consumed_as_"
    "policy_verification_or_packaging_input"
)
OVERFLOW_POLICY = "deterministic_truncation_under_frozen_profile"
MISSING_EXCERPT_SOURCE_POLICY = (
    "unresolvable_candidate_plan_excerpt_emits_null_typed_excerpt_and_no_repo_fallback"
)
SUCCESS_PATH_EXPLICIT_REQUEST_POLICY = (
    "explicit_generation_request_without_runner_rejection_diagnostic_fails_closed"
)
VERIFICATION_PASSED_POLICY = (
    "true_means_feeder_generation_guards_and_closeout_validation_passed_not_policy_validation_"
    "packaging_validation_or_model_success"
)

MAX_ISSUE_COUNT = 12
MAX_REASON_CHARS = 240
MAX_EXCERPT_LINES_PER_ISSUE = 8
MAX_EXCERPT_CHARS_PER_ISSUE = 400
MAX_TOTAL_OUTPUT_CHARS = 2400

CONTROL_MARKER_NEUTRALIZATION = "backslash_escape_fence_and_pipe_markers"
ESCAPING_POLICY = "deterministic_json_safe_text_encoding"
WHITESPACE_POLICY = "normalize_newlines_expand_tabs_strip_trailing_whitespace"

POLICY_SOURCE_ENUM = (
    "ALLOWLIST.json",
    "COMMANDS.json",
    "FORBIDDEN.json",
    "dry_run_enforcement_policy",
)

_SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")

AHK5201_INPUT_INVALID = "AHK5201"
AHK5202_REJECTION_DIAGNOSTIC_REQUIRED = "AHK5202"
AHK5203_DUPLICATE_ISSUE_TUPLE = "AHK5203"
AHK5204_BINDING_MISMATCH = "AHK5204"
AHK5205_RESULT_INVALID = "AHK5205"
AHK5206_POLICY_SOURCE_INVALID = "AHK5206"


@dataclass(frozen=True)
class RetryContextArtifacts:
    result_path: Path
    result_hash: str
    sanitization_profile_path: Path
    sanitization_profile_hash: str


class TaskpackRetryContextError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": RETRY_CONTEXT_ERROR_SCHEMA,
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def _fail(
    *, code: str, message: str, details: dict[str, Any] | None = None
) -> TaskpackRetryContextError:
    return TaskpackRetryContextError(code=code, message=message, details=details)


def _normalize_relative_path(raw_path: str) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text or path_text.startswith("/") or path_text.startswith("../"):
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="path must be repo-relative posix",
            details={"path": raw_path},
        )
    if "/../" in f"/{path_text}":
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="path must not escape repository root",
            details={"path": raw_path},
        )
    segments = [segment for segment in path_text.split("/") if segment and segment != "."]
    if not segments:
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="path resolves to repository root",
            details={"path": raw_path},
        )
    return "/".join(segments)


def _safe_join(root: Path, rel_path: str) -> Path:
    normalized = _normalize_relative_path(rel_path)
    path = (root / normalized).resolve()
    root_resolved = root.resolve()
    try:
        path.relative_to(root_resolved)
    except ValueError as exc:
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="resolved path escapes repository root",
            details={"path": rel_path},
        ) from exc
    return path


def _resolve_repo_path(root: Path, raw_path: str | Path) -> Path:
    candidate = Path(raw_path)
    if candidate.is_absolute():
        resolved = candidate.resolve()
        root_resolved = root.resolve()
        try:
            resolved.relative_to(root_resolved)
        except ValueError as exc:
            raise _fail(
                code=AHK5201_INPUT_INVALID,
                message="absolute path escapes repository root",
                details={"path": str(raw_path)},
            ) from exc
        return resolved
    return _safe_join(root, str(raw_path))


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="required json path does not exist",
            details={"path": str(path)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="json payload must decode to an object",
            details={"path": str(path)},
        )
    return payload


def _require_schema(payload: dict[str, Any], *, expected_schema: str, path: Path) -> None:
    if payload.get("schema") != expected_schema:
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="schema mismatch",
            details={
                "path": str(path),
                "expected_schema": expected_schema,
                "observed_schema": payload.get("schema"),
            },
        )


def _require_sha256(value: Any, *, field: str, path: Path) -> str:
    if not isinstance(value, str) or _SHA256_PATTERN.fullmatch(value) is None:
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="required sha256 field is missing or invalid",
            details={"path": str(path), "field": field},
        )
    return value


def _require_string(value: Any, *, field: str, path: Path) -> str:
    if not isinstance(value, str):
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="required string field is missing or invalid",
            details={"path": str(path), "field": field},
        )
    return value


def _require_bool(value: Any, *, field: str, path: Path) -> bool:
    if not isinstance(value, bool):
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="required boolean field is missing or invalid",
            details={"path": str(path), "field": field},
        )
    return value


def _load_runner_result(path: Path) -> dict[str, Any]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=runner_mod.RUNNER_RESULT_SCHEMA, path=path)
    expected_keys = {
        "schema",
        "dry_run",
        "candidate_change_plan_hash",
        "dry_run_preview_path",
        "provenance_path",
        "provenance_hash",
        "rejection_diagnostic_path",
    }
    if set(payload.keys()) != expected_keys:
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="runner result keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )
    _require_bool(payload.get("dry_run"), field="dry_run", path=path)
    _require_sha256(
        payload.get("candidate_change_plan_hash"),
        field="candidate_change_plan_hash",
        path=path,
    )
    _require_string(payload.get("provenance_path"), field="provenance_path", path=path)
    _require_sha256(payload.get("provenance_hash"), field="provenance_hash", path=path)
    rejection_path = payload.get("rejection_diagnostic_path")
    if rejection_path is not None and not isinstance(rejection_path, str):
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="runner result rejection_diagnostic_path must be string or null",
            details={"path": str(path)},
        )
    return payload


def _load_rejection_diagnostic(path: Path) -> dict[str, Any]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=runner_mod.REJECTION_DIAGNOSTIC_SCHEMA, path=path)
    expected_keys = {"schema", "taskpack_manifest_hash", "candidate_change_plan_hash", "issues"}
    if set(payload.keys()) != expected_keys:
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="runner rejection diagnostic keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )
    _require_sha256(
        payload.get("taskpack_manifest_hash"),
        field="taskpack_manifest_hash",
        path=path,
    )
    _require_sha256(
        payload.get("candidate_change_plan_hash"),
        field="candidate_change_plan_hash",
        path=path,
    )
    issues = payload.get("issues")
    if not isinstance(issues, list) or not issues:
        raise _fail(
            code=AHK5202_REJECTION_DIAGNOSTIC_REQUIRED,
            message="retry context generation requires a non-empty runner rejection diagnostic",
            details={"path": str(path)},
        )
    return payload


def _normalize_issue_entries(issues: list[Any], *, path: Path) -> list[dict[str, Any]]:
    normalized_rows: list[dict[str, Any]] = []
    identity_rows: list[tuple[str, str, int, str]] = []
    for index, issue in enumerate(issues):
        if not isinstance(issue, dict):
            raise _fail(
                code=AHK5201_INPUT_INVALID,
                message="rejection diagnostic issue entry must be an object",
                details={"path": str(path), "index": index},
            )
        expected_keys = {
            "issue_code",
            "reason",
            "target_path",
            "hunk_index",
            "line_range",
            "policy_source",
        }
        if set(issue.keys()) != expected_keys:
            raise _fail(
                code=AHK5201_INPUT_INVALID,
                message="rejection diagnostic issue keys must match frozen grammar",
                details={"path": str(path), "index": index, "keys": sorted(issue.keys())},
            )
        issue_code = _require_string(issue.get("issue_code"), field="issue_code", path=path)
        reason = _require_string(issue.get("reason"), field="reason", path=path)
        target_path = _normalize_relative_path(
            _require_string(issue.get("target_path"), field="target_path", path=path)
        )
        hunk_index = issue.get("hunk_index")
        if not isinstance(hunk_index, int):
            raise _fail(
                code=AHK5201_INPUT_INVALID,
                message="rejection diagnostic hunk_index must be integer",
                details={"path": str(path), "index": index},
            )
        line_range = issue.get("line_range")
        if (
            not isinstance(line_range, list)
            or len(line_range) != 2
            or not isinstance(line_range[0], int)
            or not isinstance(line_range[1], int)
        ):
            raise _fail(
                code=AHK5201_INPUT_INVALID,
                message="rejection diagnostic line_range must be a two-integer array",
                details={"path": str(path), "index": index},
            )
        policy_source = _require_string(
            issue.get("policy_source"),
            field="policy_source",
            path=path,
        )
        if policy_source not in POLICY_SOURCE_ENUM:
            raise _fail(
                code=AHK5206_POLICY_SOURCE_INVALID,
                message="policy_source is outside frozen inherited surface",
                details={"path": str(path), "index": index, "policy_source": policy_source},
            )
        identity = (issue_code, target_path, hunk_index, policy_source)
        identity_rows.append(identity)
        normalized_rows.append(
            {
                "issue_code": issue_code,
                "reason": reason,
                "target_path": target_path,
                "hunk_index": hunk_index,
                "line_range": [line_range[0], line_range[1]],
                "policy_source": policy_source,
            }
        )

    if len(set(identity_rows)) != len(identity_rows):
        raise _fail(
            code=AHK5203_DUPLICATE_ISSUE_TUPLE,
            message="duplicate issue tuples after target_path normalization are forbidden",
            details={"path": str(path)},
        )

    normalized_rows.sort(
        key=lambda row: (
            row["issue_code"],
            row["target_path"],
            row["hunk_index"],
            row["policy_source"],
        )
    )
    return normalized_rows


def _build_candidate_plan_hunk_map(
    candidate_plan_path: Path,
) -> tuple[Any, dict[tuple[str, int], str]]:
    try:
        plan = runner_mod._load_candidate_change_plan(candidate_plan_path)
    except runner_mod.TaskpackRunnerError as exc:
        raise _fail(
            code=AHK5201_INPUT_INVALID,
            message="candidate change plan failed canonical parsing for retry context generation",
            details={
                "path": str(candidate_plan_path),
                "runner_error_code": exc.code,
                "runner_error": exc.message,
            },
        ) from exc

    hunk_map: dict[tuple[str, int], str] = {}
    for operation in plan.file_operations:
        for hunk_index, hunk in enumerate(operation.hunks):
            hunk_map[(operation.path, hunk_index)] = "\n".join(
                f"{tag}{text}" for tag, text in hunk.lines
            )
    return plan, hunk_map


def _neutralize_control_markers(text: str) -> str:
    replacements = (
        ("```", "`\\`\\`"),
        ("~~~", "~\\~~"),
        ("<|", "<\\|"),
        ("|>", "\\|>"),
    )
    result = text
    for source, target in replacements:
        result = result.replace(source, target)
    return result


def _normalize_text(text: str) -> str:
    normalized = text.replace("\r\n", "\n").replace("\r", "\n").replace("\t", "    ")
    return "\n".join(line.rstrip() for line in normalized.split("\n"))


def _apply_char_bound(text: str, *, max_chars: int) -> tuple[str, bool]:
    if len(text) <= max_chars:
        return text, False
    return text[:max_chars], True


def _sanitize_reason_excerpt(text: str) -> dict[str, Any]:
    normalized = _neutralize_control_markers(_normalize_text(text))
    bounded, truncated = _apply_char_bound(normalized, max_chars=MAX_REASON_CHARS)
    return {
        "text": bounded,
        "present": True,
        "truncated": truncated,
        "original_char_count": len(normalized),
    }


def _sanitize_candidate_excerpt(text: str | None) -> dict[str, Any]:
    if text is None:
        return {
            "present": False,
            "text": None,
            "truncated": False,
            "source_kind": "missing",
            "original_line_count": 0,
            "original_char_count": 0,
        }
    normalized = _neutralize_control_markers(_normalize_text(text))
    lines = normalized.split("\n") if normalized else []
    bounded_lines = lines[:MAX_EXCERPT_LINES_PER_ISSUE]
    line_truncated = len(lines) > MAX_EXCERPT_LINES_PER_ISSUE
    line_bounded_text = "\n".join(bounded_lines)
    char_bounded_text, char_truncated = _apply_char_bound(
        line_bounded_text,
        max_chars=MAX_EXCERPT_CHARS_PER_ISSUE,
    )
    return {
        "present": True,
        "text": char_bounded_text,
        "truncated": line_truncated or char_truncated,
        "source_kind": "candidate_change_plan_hunk",
        "original_line_count": len(lines),
        "original_char_count": len(normalized),
    }


def _apply_total_output_bound(items: list[dict[str, Any]]) -> int:
    remaining = MAX_TOTAL_OUTPUT_CHARS
    used = 0
    for item in items:
        for field in ("sanitized_reason_excerpt", "sanitized_candidate_plan_excerpt"):
            excerpt = item[field]
            text = excerpt.get("text")
            if text is None:
                continue
            if not isinstance(text, str):
                raise _fail(
                    code=AHK5205_RESULT_INVALID,
                    message="sanitized excerpt text must be string or null",
                    details={"field": field},
                )
            if remaining <= 0:
                excerpt["text"] = ""
                excerpt["truncated"] = True
                continue
            if len(text) > remaining:
                excerpt["text"] = text[:remaining]
                excerpt["truncated"] = True
                used += remaining
                remaining = 0
                continue
            used += len(text)
            remaining -= len(text)
    return used


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def _build_sanitization_profile(output_root: str) -> dict[str, Any]:
    profile = {
        "schema": RETRY_CONTEXT_SANITIZATION_PROFILE_SCHEMA,
        "shared_feeder_engine": SHARED_FEEDER_ENGINE,
        "shared_feeder_engine_identifier": SHARED_FEEDER_ENGINE_IDENTIFIER,
        "output_root": output_root,
        "advisory_only_non_authoritative": True,
        "automatic_retry_dispatch_forbidden": True,
        "downstream_diagnostic_aggregation_forbidden": True,
        "raw_repo_file_content_forbidden": True,
        "target_path_normalization_policy": TARGET_PATH_NORMALIZATION_POLICY,
        "policy_source_policy": POLICY_SOURCE_POLICY,
        "overflow_policy": OVERFLOW_POLICY,
        "missing_excerpt_source_policy": MISSING_EXCERPT_SOURCE_POLICY,
        "control_marker_neutralization": CONTROL_MARKER_NEUTRALIZATION,
        "escaping_policy": ESCAPING_POLICY,
        "whitespace_policy": WHITESPACE_POLICY,
        "max_issue_count": MAX_ISSUE_COUNT,
        "max_reason_chars": MAX_REASON_CHARS,
        "max_excerpt_lines_per_issue": MAX_EXCERPT_LINES_PER_ISSUE,
        "max_excerpt_chars_per_issue": MAX_EXCERPT_CHARS_PER_ISSUE,
        "max_total_output_chars": MAX_TOTAL_OUTPUT_CHARS,
    }
    profile["profile_hash"] = sha256_canonical_json(profile)
    return profile


def generate_retry_context(
    *,
    candidate_change_plan_path: str | Path,
    runner_result_path: str | Path,
    rejection_diagnostic_path: str | Path | None = None,
    retry_context_output_root: str = DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
    repo_root_path: str | Path | None = None,
) -> RetryContextArtifacts:
    root = repo_root(anchor=repo_root_path)
    output_root_rel = _normalize_relative_path(retry_context_output_root)
    candidate_plan_path = _resolve_repo_path(root, candidate_change_plan_path)
    runner_result_artifact_path = _resolve_repo_path(root, runner_result_path)
    runner_result_payload = _load_runner_result(runner_result_artifact_path)
    runner_result_hash = sha256_canonical_json(runner_result_payload)

    configured_rejection_path = runner_result_payload["rejection_diagnostic_path"]
    if rejection_diagnostic_path is None:
        if configured_rejection_path is None:
            raise _fail(
                code=AHK5202_REJECTION_DIAGNOSTIC_REQUIRED,
                message="explicit retry-context generation requires runner rejection diagnostics",
                details={
                    "runner_result_path": str(runner_result_artifact_path),
                    "policy_success_explicit_request_policy": SUCCESS_PATH_EXPLICIT_REQUEST_POLICY,
                },
            )
        rejection_artifact_path = _resolve_repo_path(root, configured_rejection_path)
    else:
        rejection_artifact_path = _resolve_repo_path(root, rejection_diagnostic_path)
        if configured_rejection_path is None:
            raise _fail(
                code=AHK5202_REJECTION_DIAGNOSTIC_REQUIRED,
                message=(
                    "explicit retry-context request without runner rejection diagnostic "
                    "fails closed"
                ),
                details={
                    "runner_result_path": str(runner_result_artifact_path),
                    "requested_rejection_diagnostic_path": str(rejection_artifact_path),
                },
            )
        configured_rejection_artifact_path = _resolve_repo_path(root, configured_rejection_path)
        if configured_rejection_artifact_path != rejection_artifact_path:
            raise _fail(
                code=AHK5204_BINDING_MISMATCH,
                message=(
                    "runner result rejection_diagnostic_path must match requested "
                    "retry-context input"
                ),
                details={
                    "runner_result_rejection_diagnostic_path": configured_rejection_path,
                    "requested_rejection_diagnostic_path": str(rejection_artifact_path),
                },
            )

    rejection_payload = _load_rejection_diagnostic(rejection_artifact_path)
    rejection_hash = sha256_canonical_json(rejection_payload)
    normalized_issues = _normalize_issue_entries(
        rejection_payload["issues"],
        path=rejection_artifact_path,
    )

    plan, hunk_map = _build_candidate_plan_hunk_map(candidate_plan_path)
    if plan.candidate_change_plan_hash != rejection_payload["candidate_change_plan_hash"]:
        raise _fail(
            code=AHK5204_BINDING_MISMATCH,
            message="candidate change plan hash does not match runner rejection diagnostic",
            details={
                "candidate_change_plan_path": str(candidate_plan_path),
                "candidate_change_plan_hash": plan.candidate_change_plan_hash,
                "rejection_diagnostic_candidate_change_plan_hash": rejection_payload[
                    "candidate_change_plan_hash"
                ],
            },
        )
    if runner_result_payload["candidate_change_plan_hash"] != plan.candidate_change_plan_hash:
        raise _fail(
            code=AHK5204_BINDING_MISMATCH,
            message=(
                "runner result candidate_change_plan_hash does not match canonical "
                "candidate plan"
            ),
            details={
                "runner_result_candidate_change_plan_hash": runner_result_payload[
                    "candidate_change_plan_hash"
                ],
                "candidate_change_plan_hash": plan.candidate_change_plan_hash,
            },
        )

    selected_issues = normalized_issues[:MAX_ISSUE_COUNT]
    issue_count_truncated = len(selected_issues) != len(normalized_issues)
    items: list[dict[str, Any]] = []
    for issue in selected_issues:
        candidate_excerpt = hunk_map.get((issue["target_path"], issue["hunk_index"]))
        items.append(
            {
                "issue_reference": {
                    "issue_code": issue["issue_code"],
                    "target_path": issue["target_path"],
                    "hunk_index": issue["hunk_index"],
                    "line_range": issue["line_range"],
                    "policy_source": issue["policy_source"],
                },
                "sanitized_reason_excerpt": _sanitize_reason_excerpt(issue["reason"]),
                "sanitized_candidate_plan_excerpt": _sanitize_candidate_excerpt(candidate_excerpt),
            }
        )

    total_output_chars_used = _apply_total_output_bound(items)
    profile = _build_sanitization_profile(output_root_rel)
    profile_hash = profile["profile_hash"]

    output_root_path = _safe_join(root, output_root_rel)
    result_path = output_root_path / (
        f"{rejection_payload['taskpack_manifest_hash']}_{plan.candidate_change_plan_hash}.json"
    )
    sanitization_profile_path = output_root_path / "retry_context_sanitization_profile.json"

    result_payload = {
        "schema": RETRY_CONTEXT_FEEDER_RESULT_SCHEMA,
        "taskpack_manifest_hash": rejection_payload["taskpack_manifest_hash"],
        "candidate_change_plan_hash": plan.candidate_change_plan_hash,
        "runner_result_hash": runner_result_hash,
        "rejection_diagnostic_hash": rejection_hash,
        "source_rejection_diagnostic_schema": runner_mod.REJECTION_DIAGNOSTIC_SCHEMA,
        "shared_feeder_engine": SHARED_FEEDER_ENGINE,
        "shared_feeder_engine_identifier": SHARED_FEEDER_ENGINE_IDENTIFIER,
        "advisory_only_non_authoritative": True,
        "automatic_retry_dispatch_forbidden": True,
        "downstream_diagnostic_aggregation_forbidden": True,
        "raw_repo_file_content_forbidden": True,
        "target_path_normalization_policy": TARGET_PATH_NORMALIZATION_POLICY,
        "policy_source_policy": POLICY_SOURCE_POLICY,
        "deterministic_issue_order_policy": DETERMINISTIC_ISSUE_ORDER_POLICY,
        "overflow_policy": OVERFLOW_POLICY,
        "missing_excerpt_source_policy": MISSING_EXCERPT_SOURCE_POLICY,
        "policy_success_absence_without_request_allowed": True,
        "sanitization_profile_path": output_root_path.joinpath(
            "retry_context_sanitization_profile.json"
        ).relative_to(root).as_posix(),
        "sanitization_profile_hash": profile_hash,
        "issue_count_input": len(normalized_issues),
        "issue_count_emitted": len(items),
        "issue_count_truncated": issue_count_truncated,
        "total_output_chars_used": total_output_chars_used,
        "items": items,
    }
    result_payload["result_hash"] = sha256_canonical_json(result_payload)

    _write_json(sanitization_profile_path, profile)
    _write_json(result_path, result_payload)

    loaded_profile = _load_json_object(sanitization_profile_path)
    _require_schema(
        loaded_profile,
        expected_schema=RETRY_CONTEXT_SANITIZATION_PROFILE_SCHEMA,
        path=sanitization_profile_path,
    )
    if loaded_profile.get("profile_hash") != profile_hash:
        raise _fail(
            code=AHK5205_RESULT_INVALID,
            message="retry context sanitization profile hash drift detected",
            details={"path": str(sanitization_profile_path)},
        )

    loaded_result = _load_json_object(result_path)
    _require_schema(
        loaded_result,
        expected_schema=RETRY_CONTEXT_FEEDER_RESULT_SCHEMA,
        path=result_path,
    )
    if loaded_result.get("result_hash") != result_payload["result_hash"]:
        raise _fail(
            code=AHK5205_RESULT_INVALID,
            message="retry context feeder result hash drift detected",
            details={"path": str(result_path)},
        )

    return RetryContextArtifacts(
        result_path=result_path,
        result_hash=result_payload["result_hash"],
        sanitization_profile_path=sanitization_profile_path,
        sanitization_profile_hash=profile_hash,
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate deterministic advisory v52 retry-context feeder artifacts from runner "
            "rejection diagnostics."
        ),
    )
    parser.add_argument(
        "--candidate-change-plan",
        required=True,
        help="Repo-relative path to candidate_change_plan@1 JSON artifact.",
    )
    parser.add_argument(
        "--runner-result",
        required=True,
        help="Repo-relative path to taskpack_runner_result@1 JSON artifact.",
    )
    parser.add_argument(
        "--rejection-diagnostic",
        default=None,
        help="Optional repo-relative path to candidate_change_plan_rejection_diagnostic@1 JSON.",
    )
    parser.add_argument(
        "--retry-context-output-root",
        default=DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
        help="Repo-relative output root for retry_context_feeder_result@1 artifacts.",
    )
    parser.add_argument(
        "--repo-root",
        default=None,
        help="Optional repository root override. Defaults to deterministic repo_root(anchor=cwd).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = generate_retry_context(
            candidate_change_plan_path=args.candidate_change_plan,
            runner_result_path=args.runner_result,
            rejection_diagnostic_path=args.rejection_diagnostic,
            retry_context_output_root=args.retry_context_output_root,
            repo_root_path=args.repo_root,
        )
    except TaskpackRetryContextError as exc:
        sys.stderr.write(str(exc) + "\n")
        return 1

    payload = {
        "schema": RETRY_CONTEXT_OUTPUT_SCHEMA,
        "retry_context_feeder_result_path": result.result_path.as_posix(),
        "retry_context_feeder_result_hash": result.result_hash,
        "sanitization_profile_path": result.sanitization_profile_path.as_posix(),
        "sanitization_profile_hash": result.sanitization_profile_hash,
    }
    sys.stdout.write(canonical_json(payload) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
