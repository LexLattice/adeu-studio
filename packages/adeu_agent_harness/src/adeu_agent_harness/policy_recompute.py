from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Collection, Protocol, Sequence

from urm_runtime.hashing import canonical_json, sha256_canonical_json

POLICY_RECOMPUTE_RESULT_SCHEMA = "policy_recompute_result@1"
DEFAULT_POLICY_RECOMPUTE_OUTPUT_ROOT = "artifacts/agent_harness/v51/recompute"

COMPARISON_SUBJECT_FIELDS = ("passed", "issues", "exit_status")
ISSUE_TUPLE_FIELDS = ("issue_code", "target_path", "hunk_index")
ISSUE_TUPLE_ORDER_POLICY = "lexicographic_over_issue_code_target_path_hunk_index"
ISSUES_REPRESENTATION_POLICY = (
    "lexicographically_sorted_unique_issue_tuple_list_with_repo_relative_posix_target_paths"
)
ALLOWED_ISSUE_CODES = (
    "allowlist_violation",
    "dry_run_subprocess_execution_detected",
    "forbidden_operation_kind",
    "forbidden_path_violation",
    "model_suggested_command_execution_detected",
)
TYPED_DIFF_SUMMARY_FIELDS = (
    "exact_match",
    "mismatch_fields",
    "runner_only_issues",
    "recompute_only_issues",
)
SHARED_RECOMPUTE_ENGINE = "adeu_agent_harness.policy_recompute.recompute_policy_validation"

POLICY_RECOMPUTE_ERROR_SCHEMA = "taskpack_policy_recompute_error@1"
AHK5101_RECOMPUTE_INPUT_INVALID = "AHK5101"
AHK5102_UNEXPECTED_ISSUE_CODE = "AHK5102"
AHK5103_DUPLICATE_ISSUE_TUPLE = "AHK5103"
AHK5104_RECOMPUTE_RESULT_INVALID = "AHK5104"


class _OperationLike(Protocol):
    path: str
    operation_kind: str
    hunks: Sequence[Any]


class _CandidateChangePlanLike(Protocol):
    file_operations: Sequence[_OperationLike]
    proposed_commands: Sequence[str]


@dataclass(frozen=True)
class PolicyRecomputeArtifact:
    result_path: Path
    result_hash: str


class TaskpackPolicyRecomputeError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": POLICY_RECOMPUTE_ERROR_SCHEMA,
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def _fail(
    *, code: str, message: str, details: dict[str, Any] | None = None
) -> TaskpackPolicyRecomputeError:
    return TaskpackPolicyRecomputeError(code=code, message=message, details=details)


def _normalize_target_path(path: str) -> str:
    normalized = path.strip().replace("\\", "/")
    if not normalized or normalized.startswith("/") or normalized.startswith("../"):
        raise _fail(
            code=AHK5101_RECOMPUTE_INPUT_INVALID,
            message="policy recompute target_path must be repo-relative posix",
            details={"target_path": path},
        )
    if "/../" in f"/{normalized}":
        raise _fail(
            code=AHK5101_RECOMPUTE_INPUT_INVALID,
            message="policy recompute target_path must not escape repository root",
            details={"target_path": path},
        )
    return "/".join(segment for segment in normalized.split("/") if segment and segment != ".")


def _validate_issue_code(issue_code: str) -> str:
    if issue_code not in ALLOWED_ISSUE_CODES:
        raise _fail(
            code=AHK5102_UNEXPECTED_ISSUE_CODE,
            message="policy recompute emitted issue_code outside frozen closed set",
            details={"issue_code": issue_code, "allowed_issue_codes": list(ALLOWED_ISSUE_CODES)},
        )
    return issue_code


def _normalize_issue_tuples(
    issues: Sequence[dict[str, Any]],
    *,
    context: str,
) -> list[dict[str, Any]]:
    tuples: list[tuple[str, str, int]] = []
    for index, issue in enumerate(issues):
        if not isinstance(issue, dict):
            raise _fail(
                code=AHK5101_RECOMPUTE_INPUT_INVALID,
                message="policy issue entry must be an object",
                details={"context": context, "index": index},
            )
        if set(issue.keys()) != set(ISSUE_TUPLE_FIELDS):
            raise _fail(
                code=AHK5101_RECOMPUTE_INPUT_INVALID,
                message="policy issue entry keys must match frozen tuple grammar",
                details={"context": context, "index": index, "keys": sorted(issue.keys())},
            )
        issue_code = issue.get("issue_code")
        target_path = issue.get("target_path")
        hunk_index = issue.get("hunk_index")
        if not isinstance(issue_code, str) or not isinstance(target_path, str) or not isinstance(
            hunk_index, int
        ):
            raise _fail(
                code=AHK5101_RECOMPUTE_INPUT_INVALID,
                message="policy issue tuple field types are invalid",
                details={"context": context, "index": index},
            )
        tuples.append(
            (
                _validate_issue_code(issue_code),
                _normalize_target_path(target_path),
                hunk_index,
            )
        )

    if len(set(tuples)) != len(tuples):
        raise _fail(
            code=AHK5103_DUPLICATE_ISSUE_TUPLE,
            message="duplicate issue tuples before canonicalization are forbidden",
            details={"context": context},
        )

    sorted_tuples = sorted(tuples)
    return [
        {
            "issue_code": issue_code,
            "target_path": target_path,
            "hunk_index": hunk_index,
        }
        for issue_code, target_path, hunk_index in sorted_tuples
    ]


def _require_canonical_issue_tuples(
    issues: Sequence[dict[str, Any]],
    *,
    context: str,
) -> list[dict[str, Any]]:
    normalized = _normalize_issue_tuples(issues, context=context)
    if list(issues) != normalized:
        raise _fail(
            code=AHK5104_RECOMPUTE_RESULT_INVALID,
            message="policy issue tuples must already be canonical in recompute result payload",
            details={"context": context},
        )
    return normalized


def recompute_policy_validation(
    *,
    plan: _CandidateChangePlanLike,
    allowlist_paths: Sequence[str],
    forbidden_paths: Sequence[str],
    forbidden_operation_kinds: Collection[str],
    allowed_command_runs: Collection[str],
    dry_run: bool,
) -> dict[str, Any]:
    raw_issues: list[dict[str, Any]] = []
    normalized_allowlist = tuple(sorted({_normalize_target_path(path) for path in allowlist_paths}))
    normalized_forbidden = tuple(sorted({_normalize_target_path(path) for path in forbidden_paths}))
    allowed_command_set = set(allowed_command_runs)
    forbidden_operation_kind_set = set(forbidden_operation_kinds)

    def _path_matches_prefix(*, path: str, prefix: str) -> bool:
        return path == prefix or path.startswith(prefix + "/")

    for operation in plan.file_operations:
        operation_path = _normalize_target_path(operation.path)
        hunk_index = 0 if getattr(operation, "hunks", ()) else -1
        if not any(
            _path_matches_prefix(path=operation_path, prefix=allow_prefix)
            for allow_prefix in normalized_allowlist
        ):
            raw_issues.append(
                {
                    "issue_code": "allowlist_violation",
                    "target_path": operation_path,
                    "hunk_index": hunk_index,
                }
            )
        if any(
            _path_matches_prefix(path=operation_path, prefix=forbidden_prefix)
            for forbidden_prefix in normalized_forbidden
        ):
            raw_issues.append(
                {
                    "issue_code": "forbidden_path_violation",
                    "target_path": operation_path,
                    "hunk_index": hunk_index,
                }
            )
        if operation.operation_kind in forbidden_operation_kind_set:
            raw_issues.append(
                {
                    "issue_code": "forbidden_operation_kind",
                    "target_path": operation_path,
                    "hunk_index": hunk_index,
                }
            )

    for command in plan.proposed_commands:
        if command not in allowed_command_set:
            raw_issues.append(
                {
                    "issue_code": "model_suggested_command_execution_detected",
                    "target_path": "COMMANDS.json",
                    "hunk_index": -1,
                }
            )
    if dry_run and plan.proposed_commands:
        raw_issues.append(
            {
                "issue_code": "dry_run_subprocess_execution_detected",
                "target_path": "COMMANDS.json",
                "hunk_index": -1,
            }
        )

    issues = _normalize_issue_tuples(raw_issues, context="recompute")
    passed = not issues
    return {
        "passed": passed,
        "issues": issues,
        "exit_status": "success" if passed else "policy_validation_failed",
    }


def project_runner_policy_outcome(runner_provenance_payload: dict[str, Any]) -> dict[str, Any]:
    policy_validation_result = runner_provenance_payload.get("policy_validation_result")
    if not isinstance(policy_validation_result, dict):
        raise _fail(
            code=AHK5101_RECOMPUTE_INPUT_INVALID,
            message="runner provenance policy_validation_result must be an object",
            details={},
        )
    passed = policy_validation_result.get("passed")
    issues = policy_validation_result.get("issues")
    exit_status = runner_provenance_payload.get("exit_status")
    if not isinstance(passed, bool) or not isinstance(issues, list) or not isinstance(
        exit_status, str
    ):
        raise _fail(
            code=AHK5101_RECOMPUTE_INPUT_INVALID,
            message="runner provenance comparison subject is malformed",
            details={},
        )
    return {
        "passed": passed,
        "issues": _normalize_issue_tuples(issues, context="runner_provenance"),
        "exit_status": exit_status,
    }


def build_policy_recompute_result_payload(
    *,
    taskpack_manifest_hash: str,
    candidate_change_plan_hash: str,
    runner_provenance_hash: str,
    dry_run: bool,
    runner_outcome: dict[str, Any],
    recompute_outcome: dict[str, Any],
) -> dict[str, Any]:
    runner_issues = _require_canonical_issue_tuples(
        runner_outcome["issues"],
        context="runner_outcome",
    )
    recompute_issues = _require_canonical_issue_tuples(
        recompute_outcome["issues"],
        context="recompute_outcome",
    )
    mismatch_fields: list[str] = []
    if bool(runner_outcome["passed"]) != bool(recompute_outcome["passed"]):
        mismatch_fields.append("passed")
    if runner_outcome["exit_status"] != recompute_outcome["exit_status"]:
        mismatch_fields.append("exit_status")
    if runner_issues != recompute_issues:
        mismatch_fields.append("issues")

    runner_issue_tuples = {
        (row["issue_code"], row["target_path"], row["hunk_index"]) for row in runner_issues
    }
    recompute_issue_tuples = {
        (row["issue_code"], row["target_path"], row["hunk_index"]) for row in recompute_issues
    }
    runner_only_issues = [
        {"issue_code": row[0], "target_path": row[1], "hunk_index": row[2]}
        for row in sorted(runner_issue_tuples.difference(recompute_issue_tuples))
    ]
    recompute_only_issues = [
        {"issue_code": row[0], "target_path": row[1], "hunk_index": row[2]}
        for row in sorted(recompute_issue_tuples.difference(runner_issue_tuples))
    ]
    exact_match = not mismatch_fields
    if exact_match and (runner_only_issues or recompute_only_issues):
        raise _fail(
            code=AHK5104_RECOMPUTE_RESULT_INVALID,
            message="exact_match=true requires empty typed diff issue deltas",
            details={},
        )

    hash_subject = {
        "taskpack_manifest_hash": taskpack_manifest_hash,
        "candidate_change_plan_hash": candidate_change_plan_hash,
        "runner_provenance_hash": runner_provenance_hash,
        "dry_run": dry_run,
        "shared_recompute_engine": SHARED_RECOMPUTE_ENGINE,
        "comparison_subject_fields": list(COMPARISON_SUBJECT_FIELDS),
        "issue_tuple_fields": list(ISSUE_TUPLE_FIELDS),
        "issue_tuple_order_policy": ISSUE_TUPLE_ORDER_POLICY,
        "issues_representation_policy": ISSUES_REPRESENTATION_POLICY,
        "allowed_issue_codes": list(ALLOWED_ISSUE_CODES),
        "typed_diff_summary_fields": list(TYPED_DIFF_SUMMARY_FIELDS),
        "runner_outcome": {
            "passed": bool(runner_outcome["passed"]),
            "issues": runner_issues,
            "exit_status": runner_outcome["exit_status"],
        },
        "recompute_outcome": {
            "passed": bool(recompute_outcome["passed"]),
            "issues": recompute_issues,
            "exit_status": recompute_outcome["exit_status"],
        },
        "typed_diff_summary": {
            "exact_match": exact_match,
            "mismatch_fields": mismatch_fields,
            "runner_only_issues": runner_only_issues,
            "recompute_only_issues": recompute_only_issues,
        },
    }
    result_hash = sha256_canonical_json(hash_subject)
    return {
        "schema": POLICY_RECOMPUTE_RESULT_SCHEMA,
        **hash_subject,
        "result_hash": result_hash,
    }


def emit_policy_recompute_result(
    *,
    output_dir: Path,
    taskpack_manifest_hash: str,
    candidate_change_plan_hash: str,
    runner_provenance_hash: str,
    dry_run: bool,
    runner_outcome: dict[str, Any],
    recompute_outcome: dict[str, Any],
) -> PolicyRecomputeArtifact:
    payload = build_policy_recompute_result_payload(
        taskpack_manifest_hash=taskpack_manifest_hash,
        candidate_change_plan_hash=candidate_change_plan_hash,
        runner_provenance_hash=runner_provenance_hash,
        dry_run=dry_run,
        runner_outcome=runner_outcome,
        recompute_outcome=recompute_outcome,
    )
    output_dir.mkdir(parents=True, exist_ok=True)
    result_path = output_dir / f"{taskpack_manifest_hash}_{candidate_change_plan_hash}.json"
    result_path.write_text(canonical_json(payload) + "\n", encoding="utf-8")
    return PolicyRecomputeArtifact(result_path=result_path, result_hash=payload["result_hash"])
