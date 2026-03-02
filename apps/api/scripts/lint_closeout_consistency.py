from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json

LINT_SCHEMA = "closeout_consistency_lint@1"
ASSERTION_SCHEMA = "metric_key_continuity_assertion@1"
EXPECTED_RELATION = "exact_keyset_equality"

REQUIRED_DOCS: tuple[str, ...] = (
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md",
)
DOC_FILE_RE = re.compile(r"^DRAFT_STOP_GATE_DECISION_vNEXT_PLUS([0-9]+)\.md$")

ALLOWED_FAILURE_CODES: tuple[str, ...] = (
    "MISSING_BLOCK",
    "MULTIPLE_BLOCKS",
    "BLOCK_SCHEMA_INVALID",
    "PATH_INVALID",
    "ARTIFACT_NOT_FOUND",
    "JSON_INVALID",
    "SCHEMA_MISMATCH",
    "METRICS_OBJECT_INVALID",
    "KEYSET_MISMATCH",
    "PROVENANCE_MISMATCH",
)

PROVENANCE_BY_REQUIRED_DOC: dict[str, dict[str, str]] = {
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md": {
        "baseline_metrics_path": "artifacts/stop_gate/metrics_v28_closeout.json",
        "current_metrics_path": "artifacts/stop_gate/metrics_v29_closeout.json",
        "quality_baseline_path": "artifacts/quality_dashboard_v28_closeout.json",
        "quality_current_path": "artifacts/quality_dashboard_v29_closeout.json",
    },
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md": {
        "baseline_metrics_path": "artifacts/stop_gate/metrics_v29_closeout.json",
        "current_metrics_path": "artifacts/stop_gate/metrics_v30_closeout.json",
        "quality_baseline_path": "artifacts/quality_dashboard_v29_closeout.json",
        "quality_current_path": "artifacts/quality_dashboard_v30_closeout.json",
    },
}


@dataclass(frozen=True)
class ContinuityAssertion:
    baseline_metrics_path: str
    current_metrics_path: str


@dataclass
class LintResult:
    checked_docs: list[str]
    failures: list[dict[str, Any]]

    def add_failure(self, *, doc_path: str, code: str, details: dict[str, Any]) -> None:
        if code not in ALLOWED_FAILURE_CODES:
            raise ValueError(f"unsupported failure code: {code}")
        self.failures.append(
            {
                "doc_path": doc_path,
                "code": code,
                "details": details,
            }
        )

    def finalize(self) -> dict[str, Any]:
        checked_docs = sorted(set(self.checked_docs))
        failures = sorted(
            self.failures,
            key=lambda row: (
                str(row["doc_path"]),
                str(row["code"]),
                canonical_json(row["details"]),
            ),
        )
        return {
            "schema": LINT_SCHEMA,
            "checked_docs": checked_docs,
            "failures": failures,
        }


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Lint closeout continuity assertions for deterministic "
            "stop-gate evidence consistency."
        ),
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


def _read_json_object(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("json payload must be an object")
    return payload


def _is_path_safe_artifact_ref(path_text: str) -> bool:
    if not path_text:
        return False
    if "\\" in path_text:
        return False
    if path_text.startswith("/"):
        return False
    if not path_text.startswith("artifacts/"):
        return False
    parts = path_text.split("/")
    if any(part == ".." for part in parts):
        return False
    return True


def _extract_assertion_blocks(doc_text: str) -> list[str]:
    heading = "## Metric-Key Continuity Assertion"
    blocks: list[str] = []
    lines = doc_text.splitlines()
    index = 0
    while index < len(lines):
        if lines[index].strip() != heading:
            index += 1
            continue
        index += 1
        while index < len(lines) and lines[index].strip() == "":
            index += 1
        if index >= len(lines) or lines[index].strip() != "```json":
            blocks.append("")
            continue
        index += 1
        block_lines: list[str] = []
        while index < len(lines) and lines[index].strip() != "```":
            block_lines.append(lines[index])
            index += 1
        if index >= len(lines):
            blocks.append("")
            continue
        blocks.append("\n".join(block_lines).strip())
        index += 1
    return blocks


def _parse_assertion_block(block_text: str) -> ContinuityAssertion:
    payload = json.loads(block_text)
    if not isinstance(payload, dict):
        raise ValueError("assertion payload must be an object")

    required_keys = {
        "schema",
        "baseline_metrics_path",
        "current_metrics_path",
        "expected_relation",
    }
    payload_keys = set(payload.keys())
    if payload_keys != required_keys:
        raise ValueError("assertion keys must match frozen grammar")
    if payload.get("schema") != ASSERTION_SCHEMA:
        raise ValueError("assertion schema mismatch")
    if payload.get("expected_relation") != EXPECTED_RELATION:
        raise ValueError("assertion relation mismatch")

    baseline = payload.get("baseline_metrics_path")
    current = payload.get("current_metrics_path")
    if not isinstance(baseline, str) or not isinstance(current, str):
        raise ValueError("assertion metrics paths must be strings")

    return ContinuityAssertion(
        baseline_metrics_path=baseline,
        current_metrics_path=current,
    )


def _load_and_validate_metrics_payload(
    *,
    repo_root: Path,
    doc_path: str,
    path_text: str,
    result: LintResult,
) -> dict[str, Any] | None:
    if not _is_path_safe_artifact_ref(path_text):
        result.add_failure(
            doc_path=doc_path,
            code="PATH_INVALID",
            details={"path": path_text},
        )
        return None

    artifact_path = repo_root / path_text
    if not artifact_path.is_file():
        result.add_failure(
            doc_path=doc_path,
            code="ARTIFACT_NOT_FOUND",
            details={"path": path_text},
        )
        return None

    try:
        payload = _read_json_object(artifact_path)
    except json.JSONDecodeError:
        result.add_failure(
            doc_path=doc_path,
            code="JSON_INVALID",
            details={"path": path_text},
        )
        return None
    except ValueError:
        result.add_failure(
            doc_path=doc_path,
            code="JSON_INVALID",
            details={"path": path_text},
        )
        return None

    if payload.get("schema") != "stop_gate_metrics@1":
        result.add_failure(
            doc_path=doc_path,
            code="SCHEMA_MISMATCH",
            details={"path": path_text, "expected_schema": "stop_gate_metrics@1"},
        )
        return None

    metrics = payload.get("metrics")
    if not isinstance(metrics, dict):
        result.add_failure(
            doc_path=doc_path,
            code="METRICS_OBJECT_INVALID",
            details={"path": path_text},
        )
        return None

    return payload


def _lint_single_doc(
    *,
    repo_root: Path,
    doc_path: str,
    required: bool,
    result: LintResult,
) -> None:
    result.checked_docs.append(doc_path)
    doc_file = repo_root / doc_path
    if not doc_file.is_file():
        result.add_failure(
            doc_path=doc_path,
            code="ARTIFACT_NOT_FOUND",
            details={"path": doc_path},
        )
        return

    doc_text = doc_file.read_text(encoding="utf-8")
    blocks = _extract_assertion_blocks(doc_text)
    if not blocks:
        if required:
            result.add_failure(doc_path=doc_path, code="MISSING_BLOCK", details={})
        return
    if len(blocks) > 1:
        result.add_failure(
            doc_path=doc_path,
            code="MULTIPLE_BLOCKS",
            details={"count": len(blocks)},
        )
        return
    if not blocks[0]:
        result.add_failure(doc_path=doc_path, code="BLOCK_SCHEMA_INVALID", details={})
        return

    try:
        assertion = _parse_assertion_block(blocks[0])
    except json.JSONDecodeError:
        result.add_failure(
            doc_path=doc_path,
            code="JSON_INVALID",
            details={"target": "assertion_block"},
        )
        return
    except ValueError as exc:
        result.add_failure(
            doc_path=doc_path,
            code="BLOCK_SCHEMA_INVALID",
            details={"message": str(exc)},
        )
        return

    baseline_payload = _load_and_validate_metrics_payload(
        repo_root=repo_root,
        doc_path=doc_path,
        path_text=assertion.baseline_metrics_path,
        result=result,
    )
    current_payload = _load_and_validate_metrics_payload(
        repo_root=repo_root,
        doc_path=doc_path,
        path_text=assertion.current_metrics_path,
        result=result,
    )
    if baseline_payload is None or current_payload is None:
        return

    baseline_metrics = baseline_payload["metrics"]
    current_metrics = current_payload["metrics"]
    baseline_keys = set(baseline_metrics.keys())
    current_keys = set(current_metrics.keys())
    if baseline_keys != current_keys:
        result.add_failure(
            doc_path=doc_path,
            code="KEYSET_MISMATCH",
            details={
                "baseline_metrics_path": assertion.baseline_metrics_path,
                "current_metrics_path": assertion.current_metrics_path,
            },
        )

    expected_provenance = PROVENANCE_BY_REQUIRED_DOC.get(doc_path)
    if expected_provenance is None:
        return

    if assertion.baseline_metrics_path != expected_provenance["baseline_metrics_path"]:
        result.add_failure(
            doc_path=doc_path,
            code="PROVENANCE_MISMATCH",
            details={
                "field": "baseline_metrics_path",
                "expected": expected_provenance["baseline_metrics_path"],
                "actual": assertion.baseline_metrics_path,
            },
        )
    if assertion.current_metrics_path != expected_provenance["current_metrics_path"]:
        result.add_failure(
            doc_path=doc_path,
            code="PROVENANCE_MISMATCH",
            details={
                "field": "current_metrics_path",
                "expected": expected_provenance["current_metrics_path"],
                "actual": assertion.current_metrics_path,
            },
        )

    current_inputs = current_payload.get("inputs")
    if not isinstance(current_inputs, dict):
        result.add_failure(
            doc_path=doc_path,
            code="PROVENANCE_MISMATCH",
            details={
                "field": "inputs",
                "expected": "object",
                "actual": type(current_inputs).__name__,
            },
        )
        return

    baseline_path_value = current_inputs.get("quality_baseline_path")
    current_path_value = current_inputs.get("quality_current_path")
    if baseline_path_value != expected_provenance["quality_baseline_path"]:
        result.add_failure(
            doc_path=doc_path,
            code="PROVENANCE_MISMATCH",
            details={
                "field": "inputs.quality_baseline_path",
                "expected": expected_provenance["quality_baseline_path"],
                "actual": baseline_path_value,
            },
        )
    if current_path_value != expected_provenance["quality_current_path"]:
        result.add_failure(
            doc_path=doc_path,
            code="PROVENANCE_MISMATCH",
            details={
                "field": "inputs.quality_current_path",
                "expected": expected_provenance["quality_current_path"],
                "actual": current_path_value,
            },
        )


def lint_closeout_consistency(*, repo_root: Path) -> dict[str, Any]:
    docs_root = repo_root / "docs"
    result = LintResult(checked_docs=[], failures=[])

    for required_doc in REQUIRED_DOCS:
        _lint_single_doc(
            repo_root=repo_root,
            doc_path=required_doc,
            required=True,
            result=result,
        )

    required_set = set(REQUIRED_DOCS)
    for candidate in sorted(docs_root.iterdir()):
        if not candidate.is_file():
            continue
        match = DOC_FILE_RE.match(candidate.name)
        if not match:
            continue
        relative_doc = f"docs/{candidate.name}"
        if relative_doc in required_set:
            continue
        doc_text = candidate.read_text(encoding="utf-8")
        if "## Metric-Key Continuity Assertion" not in doc_text:
            continue
        _lint_single_doc(
            repo_root=repo_root,
            doc_path=relative_doc,
            required=False,
            result=result,
        )

    return result.finalize()


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = args.repo_root.resolve() if args.repo_root is not None else _repo_root_from_script()
    payload = lint_closeout_consistency(repo_root=repo_root)
    sys.stdout.write(canonical_json(payload) + "\n")
    return 1 if payload["failures"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
