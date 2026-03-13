from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from urm_runtime.events_tools import validate_events
from urm_runtime.hashing import canonical_json

LINT_SCHEMA = "arc_bundle_lint@1"
DECISION_STATE_SCHEMA = "decision_artifact_state@1"
ASSESSMENT_STATE_SCHEMA = "assessment_artifact_state@1"
START_PHASE = "start"
CLOSEOUT_PHASE = "closeout"

ALLOWED_FAILURE_CODES: tuple[str, ...] = (
    "MISSING_FILE",
    "JSON_BLOCK_INVALID",
    "JSON_BLOCK_COUNT_INVALID",
    "STATE_FIELD_MISMATCH",
    "CONTRACT_BLOCK_COUNT_INVALID",
    "OPTIONS_TARGET_MISMATCH",
    "START_DOC_CLOSEOUT_HEADING_PRESENT",
    "CLOSEOUT_HEADING_MISSING",
    "ARTIFACT_FILE_COUNT_INVALID",
    "REFERENCED_PATH_INVALID",
    "REFERENCED_PATH_MISSING",
    "EVENT_STREAMS_MISSING",
    "EVENT_STREAM_INVALID",
)


@dataclass
class LintResult:
    checked_paths: list[str]
    failures: list[dict[str, Any]]

    def add_failure(self, *, code: str, details: dict[str, Any]) -> None:
        if code not in ALLOWED_FAILURE_CODES:
            raise ValueError(f"unsupported failure code: {code}")
        self.failures.append({"code": code, "details": details})

    def add_checked_path(self, path: str) -> None:
        self.checked_paths.append(path)

    def finalize(self, *, arc: int, phase: str) -> dict[str, Any]:
        return {
            "schema": LINT_SCHEMA,
            "arc": arc,
            "phase": phase,
            "checked_paths": sorted(set(self.checked_paths)),
            "failures": sorted(
                self.failures,
                key=lambda row: (row["code"], canonical_json(row["details"])),
            ),
        }


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Lint pre-start and closeout arc doc/artifact bundles without running "
            "the full Python test suite."
        )
    )
    parser.add_argument("--arc", type=int, required=True, help="Arc number, for example 58.")
    parser.add_argument(
        "--phase",
        choices=(START_PHASE, CLOSEOUT_PHASE),
        required=True,
        help="Bundle phase to validate.",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=None,
        help="Repository root path. Defaults to discovery from script location.",
    )
    return parser.parse_args(argv)


def _repo_root_from_script() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        if (parent / ".git").is_dir():
            return parent
    raise FileNotFoundError("repository root not found from script location")


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _read_json_object(path: Path) -> dict[str, Any]:
    payload = json.loads(_read_text(path))
    if not isinstance(payload, dict):
        raise ValueError("json payload must be an object")
    return payload


def _extract_json_blocks(text: str) -> list[str]:
    blocks: list[str] = []
    lines = text.splitlines()
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


def _extract_schema_blocks(text: str) -> dict[str, list[dict[str, Any]]]:
    by_schema: dict[str, list[dict[str, Any]]] = {}
    for block in _extract_json_blocks(text):
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


def _arc_lock_doc_path(arc: int) -> str:
    return f"docs/LOCKED_CONTINUATION_vNEXT_PLUS{arc}.md"


def _arc_decision_doc_path(arc: int) -> str:
    return f"docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS{arc}.md"


def _arc_assessment_doc_path(arc: int) -> str:
    return f"docs/ASSESSMENT_vNEXT_PLUS{arc}_EDGES.md"


def _options_doc_paths(*, repo_root: Path) -> list[str]:
    relative_paths: list[str] = []
    for path in sorted((repo_root / "docs").glob("DRAFT_NEXT_ARC_OPTIONS_v*.md")):
        relative_paths.append(str(path.relative_to(repo_root)))
    return relative_paths


def _resolve_required_file(
    *,
    repo_root: Path,
    relative_path: str,
    result: LintResult,
) -> Path | None:
    path = repo_root / relative_path
    if not path.is_file():
        result.add_failure(code="MISSING_FILE", details={"path": relative_path})
        return None
    result.add_checked_path(relative_path)
    return path


def _require_single_schema_block(
    *,
    text: str,
    schema: str,
    doc_path: str,
    result: LintResult,
) -> dict[str, Any] | None:
    blocks = _extract_schema_blocks(text).get(schema, [])
    if len(blocks) != 1:
        result.add_failure(
            code="JSON_BLOCK_COUNT_INVALID",
            details={"doc_path": doc_path, "schema": schema, "count": len(blocks)},
        )
        return None
    return blocks[0]


def _validate_state_block(
    *,
    payload: dict[str, Any],
    expected: dict[str, Any],
    doc_path: str,
    result: LintResult,
) -> None:
    for field_name, expected_value in expected.items():
        actual_value = payload.get(field_name)
        if actual_value != expected_value:
            result.add_failure(
                code="STATE_FIELD_MISMATCH",
                details={
                    "doc_path": doc_path,
                    "field": field_name,
                    "expected": expected_value,
                    "actual": actual_value,
                },
            )


def _require_single_contract_block(
    *,
    lock_text: str,
    arc: int,
    lock_doc_path: str,
    result: LintResult,
) -> dict[str, Any] | None:
    target_arc = f"vNext+{arc}"
    matching_blocks: list[dict[str, Any]] = []
    for block in _extract_json_blocks(lock_text):
        try:
            payload = json.loads(block)
        except json.JSONDecodeError:
            continue
        if not isinstance(payload, dict):
            continue
        if payload.get("target_arc") == target_arc and isinstance(payload.get("target_path"), str):
            matching_blocks.append(payload)
    if len(matching_blocks) != 1:
        result.add_failure(
            code="CONTRACT_BLOCK_COUNT_INVALID",
            details={
                "doc_path": lock_doc_path,
                "target_arc": target_arc,
                "count": len(matching_blocks),
            },
        )
        return None
    return matching_blocks[0]


def _validate_start_bundle(*, repo_root: Path, arc: int, result: LintResult) -> None:
    lock_doc_path = _arc_lock_doc_path(arc)
    decision_doc_path = _arc_decision_doc_path(arc)
    assessment_doc_path = _arc_assessment_doc_path(arc)
    options_doc_paths = _options_doc_paths(repo_root=repo_root)

    lock_doc = _resolve_required_file(
        repo_root=repo_root,
        relative_path=lock_doc_path,
        result=result,
    )
    decision_doc = _resolve_required_file(
        repo_root=repo_root,
        relative_path=decision_doc_path,
        result=result,
    )
    assessment_doc = _resolve_required_file(
        repo_root=repo_root,
        relative_path=assessment_doc_path,
        result=result,
    )
    option_docs: list[Path] = []
    if not options_doc_paths:
        result.add_failure(
            code="MISSING_FILE",
            details={"path": "docs/DRAFT_NEXT_ARC_OPTIONS_v*.md"},
        )
    else:
        for relative_path in options_doc_paths:
            resolved = _resolve_required_file(
                repo_root=repo_root,
                relative_path=relative_path,
                result=result,
            )
            if resolved is not None:
                option_docs.append(resolved)
    if lock_doc is None or decision_doc is None or assessment_doc is None or not option_docs:
        return

    lock_text = _read_text(lock_doc)
    decision_text = _read_text(decision_doc)
    assessment_text = _read_text(assessment_doc)
    options_texts = {str(path.relative_to(repo_root)): _read_text(path) for path in option_docs}

    decision_state = _require_single_schema_block(
        text=decision_text,
        schema=DECISION_STATE_SCHEMA,
        doc_path=decision_doc_path,
        result=result,
    )
    assessment_state = _require_single_schema_block(
        text=assessment_text,
        schema=ASSESSMENT_STATE_SCHEMA,
        doc_path=assessment_doc_path,
        result=result,
    )
    contract_block = _require_single_contract_block(
        lock_text=lock_text,
        arc=arc,
        lock_doc_path=lock_doc_path,
        result=result,
    )

    if decision_state is not None:
        _validate_state_block(
            payload=decision_state,
            expected={
                "artifact": decision_doc_path,
                "phase": "pre_start_scaffold",
                "authoritative": False,
                "required_in_closeout": True,
                "all_passed": False,
            },
            doc_path=decision_doc_path,
            result=result,
        )
    if assessment_state is not None:
        _validate_state_block(
            payload=assessment_state,
            expected={
                "artifact": assessment_doc_path,
                "phase": "pre_lock_assessment",
                "authoritative": False,
                "required_in_decision": True,
            },
            doc_path=assessment_doc_path,
            result=result,
        )
    if "## Metric-Key Continuity Assertion" in decision_text:
        result.add_failure(
            code="START_DOC_CLOSEOUT_HEADING_PRESENT",
            details={
                "doc_path": decision_doc_path,
                "heading": "## Metric-Key Continuity Assertion",
            },
        )
    if contract_block is not None:
        target_path = contract_block["target_path"]
        expected_phrase = f"select `{target_path}` as the next default candidate"
        if not any(expected_phrase in text for text in options_texts.values()):
            result.add_failure(
                code="OPTIONS_TARGET_MISMATCH",
                details={
                    "doc_paths": sorted(options_texts),
                    "target_path": target_path,
                    "expected_phrase": expected_phrase,
                },
            )


def _resolve_reference_path(
    *,
    repo_root: Path,
    runtime_root: Path,
    key: str,
    value: str,
) -> Path | None:
    normalized = value.split("#", 1)[0]
    if key == "contract_source":
        if not normalized.startswith("docs/"):
            return None
        return repo_root / normalized
    if key.endswith("_path") or key.endswith("_source") or key == "evidence_input_path":
        if normalized.startswith("artifacts/"):
            return repo_root / normalized
        if normalized.startswith("evidence/"):
            return runtime_root / normalized
        if normalized.startswith("docs/"):
            return repo_root / normalized
    return None


def _validate_json_path_references(
    *,
    payload: Any,
    json_path: str,
    repo_root: Path,
    runtime_root: Path,
    result: LintResult,
) -> None:
    def walk(node: Any) -> None:
        if isinstance(node, dict):
            for key, value in node.items():
                if isinstance(value, str):
                    resolved = _resolve_reference_path(
                        repo_root=repo_root,
                        runtime_root=runtime_root,
                        key=key,
                        value=value,
                    )
                    if resolved is None:
                        continue
                    if value.startswith("/"):
                        result.add_failure(
                            code="REFERENCED_PATH_INVALID",
                            details={"json_path": json_path, "field": key, "value": value},
                        )
                        continue
                    if not resolved.is_file():
                        result.add_failure(
                            code="REFERENCED_PATH_MISSING",
                            details={"json_path": json_path, "field": key, "value": value},
                        )
                        continue
                    try:
                        relative = str(resolved.relative_to(repo_root))
                    except ValueError:
                        relative = str(resolved)
                    result.add_checked_path(relative)
                else:
                    walk(value)
        elif isinstance(node, list):
            for item in node:
                walk(item)

    walk(payload)


def _validate_closeout_bundle(*, repo_root: Path, arc: int, result: LintResult) -> None:
    lock_doc_path = _arc_lock_doc_path(arc)
    decision_doc_path = _arc_decision_doc_path(arc)
    assessment_doc_path = _arc_assessment_doc_path(arc)

    lock_doc = _resolve_required_file(
        repo_root=repo_root,
        relative_path=lock_doc_path,
        result=result,
    )
    decision_doc = _resolve_required_file(
        repo_root=repo_root,
        relative_path=decision_doc_path,
        result=result,
    )
    assessment_doc = _resolve_required_file(
        repo_root=repo_root,
        relative_path=assessment_doc_path,
        result=result,
    )
    quality_dashboard_path = _resolve_required_file(
        repo_root=repo_root,
        relative_path=f"artifacts/quality_dashboard_v{arc}_closeout.json",
        result=result,
    )
    metrics_path = _resolve_required_file(
        repo_root=repo_root,
        relative_path=f"artifacts/stop_gate/metrics_v{arc}_closeout.json",
        result=result,
    )
    report_path = _resolve_required_file(
        repo_root=repo_root,
        relative_path=f"artifacts/stop_gate/report_v{arc}_closeout.md",
        result=result,
    )
    if (
        lock_doc is None
        or decision_doc is None
        or assessment_doc is None
        or quality_dashboard_path is None
        or metrics_path is None
        or report_path is None
    ):
        return

    decision_text = _read_text(decision_doc)
    assessment_text = _read_text(assessment_doc)
    decision_state = _require_single_schema_block(
        text=decision_text,
        schema=DECISION_STATE_SCHEMA,
        doc_path=decision_doc_path,
        result=result,
    )
    assessment_state = _require_single_schema_block(
        text=assessment_text,
        schema=ASSESSMENT_STATE_SCHEMA,
        doc_path=assessment_doc_path,
        result=result,
    )
    if decision_state is not None:
        _validate_state_block(
            payload=decision_state,
            expected={
                "artifact": decision_doc_path,
                "phase": "post_closeout_decision",
                "authoritative": True,
                "required_in_closeout": True,
                "all_passed": True,
            },
            doc_path=decision_doc_path,
            result=result,
        )
    if assessment_state is not None:
        _validate_state_block(
            payload=assessment_state,
            expected={
                "artifact": assessment_doc_path,
                "phase": "post_closeout_assessment",
                "authoritative": True,
                "required_in_decision": True,
            },
            doc_path=assessment_doc_path,
            result=result,
        )
    if "## Metric-Key Continuity Assertion" not in decision_text:
        result.add_failure(
            code="CLOSEOUT_HEADING_MISSING",
            details={
                "doc_path": decision_doc_path,
                "heading": "## Metric-Key Continuity Assertion",
            },
        )

    evidence_inputs_root = repo_root / "artifacts" / "agent_harness" / f"v{arc}" / "evidence_inputs"
    runtime_root = repo_root / "artifacts" / "agent_harness" / f"v{arc}" / "runtime"
    metric_key_input = evidence_inputs_root / f"metric_key_continuity_assertion_v{arc}.json"
    runtime_obs_input = evidence_inputs_root / f"runtime_observability_comparison_v{arc}.json"
    for path in (metric_key_input, runtime_obs_input):
        if not path.is_file():
            result.add_failure(
                code="MISSING_FILE",
                details={"path": str(path.relative_to(repo_root))},
            )
        else:
            result.add_checked_path(str(path.relative_to(repo_root)))

    arc_evidence_files = sorted(evidence_inputs_root.glob(f"*_evidence_v{arc}.json"))
    if len(arc_evidence_files) != 1:
        result.add_failure(
            code="ARTIFACT_FILE_COUNT_INVALID",
            details={
                "path": str(evidence_inputs_root.relative_to(repo_root)),
                "pattern": f"*_evidence_v{arc}.json",
                "count": len(arc_evidence_files),
            },
        )

    json_inputs = [
        path for path in (metric_key_input, runtime_obs_input) if path.is_file()
    ] + arc_evidence_files
    for json_input in json_inputs:
        try:
            payload = _read_json_object(json_input)
        except (json.JSONDecodeError, ValueError):
            result.add_failure(
                code="JSON_BLOCK_INVALID",
                details={"path": str(json_input.relative_to(repo_root))},
            )
            continue
        _validate_json_path_references(
            payload=payload,
            json_path=str(json_input.relative_to(repo_root)),
            repo_root=repo_root,
            runtime_root=runtime_root,
            result=result,
        )

    runtime_evidence_root = runtime_root / "evidence"
    event_paths = sorted(runtime_evidence_root.rglob("urm_events.ndjson"))
    if not event_paths:
        result.add_failure(
            code="EVENT_STREAMS_MISSING",
            details={"path": str(runtime_evidence_root.relative_to(repo_root))},
        )
        return
    for event_path in event_paths:
        result.add_checked_path(str(event_path.relative_to(repo_root)))
        validation = validate_events(event_path, strict=True)
        if validation.get("valid") is True:
            continue
        issue_codes = sorted(
            {
                str(issue.get("code"))
                for issue in validation.get("issues", [])
                if isinstance(issue, dict) and issue.get("code") is not None
            }
        )
        result.add_failure(
            code="EVENT_STREAM_INVALID",
            details={
                "path": str(event_path.relative_to(repo_root)),
                "issue_codes": issue_codes,
            },
        )


def lint_arc_bundle(*, repo_root: Path, arc: int, phase: str) -> dict[str, Any]:
    result = LintResult(checked_paths=[], failures=[])
    if phase == START_PHASE:
        _validate_start_bundle(repo_root=repo_root, arc=arc, result=result)
    elif phase == CLOSEOUT_PHASE:
        _validate_closeout_bundle(repo_root=repo_root, arc=arc, result=result)
    else:
        raise ValueError(f"unsupported phase: {phase}")
    return result.finalize(arc=arc, phase=phase)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = args.repo_root.resolve() if args.repo_root is not None else _repo_root_from_script()
    payload = lint_arc_bundle(repo_root=repo_root, arc=args.arc, phase=args.phase)
    sys.stdout.write(canonical_json(payload) + "\n")
    return 1 if payload["failures"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
