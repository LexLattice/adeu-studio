from __future__ import annotations

import importlib.util
import re
import shutil
import sys
from pathlib import Path
from types import ModuleType


def _repo_root() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        if (parent / ".git").is_dir():
            return parent
    raise FileNotFoundError("repository root not found")


def _script_path() -> Path:
    return _repo_root() / "apps" / "api" / "scripts" / "lint_arc_bundle.py"


def _load_script_module() -> ModuleType:
    module_name = "lint_arc_bundle_for_tests"
    spec = importlib.util.spec_from_file_location(module_name, _script_path())
    if spec is None or spec.loader is None:
        raise RuntimeError("failed to load lint_arc_bundle module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def _copy_start_bundle(*, arc: int, target_root: Path) -> None:
    repo_root = _repo_root()
    docs_root = target_root / "docs"
    docs_root.mkdir(parents=True, exist_ok=True)
    for relative_path in (
        f"docs/LOCKED_CONTINUATION_vNEXT_PLUS{arc}.md",
        f"docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS{arc}.md",
        f"docs/ASSESSMENT_vNEXT_PLUS{arc}_EDGES.md",
    ):
        source = repo_root / relative_path
        destination = target_root / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
    for source in sorted((repo_root / "docs").glob("DRAFT_NEXT_ARC_OPTIONS_v*.md")):
        destination = target_root / source.relative_to(repo_root)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)


def _copy_closeout_bundle(*, arc: int, target_root: Path) -> None:
    repo_root = _repo_root()
    for relative_path in (
        f"docs/LOCKED_CONTINUATION_vNEXT_PLUS{arc}.md",
        f"docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS{arc}.md",
        f"docs/ASSESSMENT_vNEXT_PLUS{arc}_EDGES.md",
        f"artifacts/quality_dashboard_v{arc}_closeout.json",
        f"artifacts/stop_gate/metrics_v{arc}_closeout.json",
        f"artifacts/stop_gate/report_v{arc}_closeout.md",
    ):
        source = repo_root / relative_path
        destination = target_root / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
    shutil.copytree(
        repo_root / "artifacts" / "agent_harness" / f"v{arc}",
        target_root / "artifacts" / "agent_harness" / f"v{arc}",
    )


def _rewrite_closeout_bundle_to_synthetic_start(*, arc: int, target_root: Path) -> None:
    lock_doc = target_root / f"docs/LOCKED_CONTINUATION_vNEXT_PLUS{arc}.md"
    decision_doc = target_root / f"docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS{arc}.md"
    assessment_doc = target_root / f"docs/ASSESSMENT_vNEXT_PLUS{arc}_EDGES.md"

    decision_text = decision_doc.read_text(encoding="utf-8")
    decision_text = decision_text.replace(
        '"phase": "post_closeout_decision"',
        '"phase": "pre_start_scaffold"',
    )
    decision_text = decision_text.replace('"all_passed": true', '"all_passed": false')
    decision_text = decision_text.replace('"authoritative": true', '"authoritative": false')
    decision_text = decision_text.replace(
        "## Metric-Key Continuity Assertion",
        "## Closeout Assertion Placeholder",
    )
    decision_doc.write_text(decision_text, encoding="utf-8")

    assessment_text = assessment_doc.read_text(encoding="utf-8")
    assessment_text = assessment_text.replace(
        '"phase": "post_closeout_assessment"',
        '"phase": "pre_lock_assessment"',
    )
    assessment_text = assessment_text.replace('"authoritative": true', '"authoritative": false')
    assessment_doc.write_text(assessment_text, encoding="utf-8")

    lock_text = lock_doc.read_text(encoding="utf-8")
    target_match = re.search(r'"target_path"\s*:\s*"([^"]+)"', lock_text)
    if target_match is None:
        raise AssertionError("failed to resolve target_path from synthetic start lock doc")
    target_path = target_match.group(1)
    synthetic_options = target_root / "docs" / "DRAFT_NEXT_ARC_OPTIONS_v999.md"
    synthetic_options.write_text(
        "# Synthetic Start Bundle Options\n\n"
        f"select `{target_path}` as the next default candidate\n",
        encoding="utf-8",
    )


def test_synthetic_v65_start_bundle_passes(tmp_path: Path) -> None:
    _copy_start_bundle(arc=65, target_root=tmp_path)
    _rewrite_closeout_bundle_to_synthetic_start(arc=65, target_root=tmp_path)

    module = _load_script_module()
    payload = module.lint_arc_bundle(repo_root=tmp_path, arc=65, phase="start")
    assert payload["schema"] == "arc_bundle_lint@1"
    assert payload["failures"] == []


def test_current_repo_v65_closeout_bundle_passes() -> None:
    module = _load_script_module()
    payload = module.lint_arc_bundle(repo_root=_repo_root(), arc=65, phase="closeout")
    assert payload["schema"] == "arc_bundle_lint@1"
    assert payload["failures"] == []


def test_start_bundle_fails_on_closeout_heading_and_wrong_phase(tmp_path: Path) -> None:
    _copy_start_bundle(arc=60, target_root=tmp_path)
    decision_doc = tmp_path / "docs" / "DRAFT_STOP_GATE_DECISION_vNEXT_PLUS60.md"
    text = decision_doc.read_text(encoding="utf-8")
    text = text.replace('"phase": "pre_start_scaffold"', '"phase": "post_closeout_decision"')
    text += "\n## Metric-Key Continuity Assertion\n\n```json\n{}\n```\n"
    decision_doc.write_text(text, encoding="utf-8")

    module = _load_script_module()
    payload = module.lint_arc_bundle(repo_root=tmp_path, arc=60, phase="start")

    failure_codes = {row["code"] for row in payload["failures"]}
    assert "STATE_FIELD_MISMATCH" in failure_codes
    assert "START_DOC_CLOSEOUT_HEADING_PRESENT" in failure_codes


def test_closeout_bundle_fails_on_invalid_event_stream(tmp_path: Path) -> None:
    _copy_closeout_bundle(arc=57, target_root=tmp_path)
    event_path = next(
        (tmp_path / "artifacts" / "agent_harness" / "v57" / "runtime" / "evidence").rglob(
            "urm_events.ndjson"
        )
    )
    event_path.write_text('{"schema":"urm-events@1"', encoding="utf-8")

    module = _load_script_module()
    payload = module.lint_arc_bundle(repo_root=tmp_path, arc=57, phase="closeout")

    failure_codes = {row["code"] for row in payload["failures"]}
    assert "EVENT_STREAM_INVALID" in failure_codes
