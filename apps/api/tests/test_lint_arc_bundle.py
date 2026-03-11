from __future__ import annotations

import importlib.util
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
        "docs/DRAFT_NEXT_ARC_OPTIONS_v9.md",
    ):
        source = repo_root / relative_path
        destination = target_root / relative_path
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


def test_current_repo_v58_start_bundle_passes() -> None:
    module = _load_script_module()
    payload = module.lint_arc_bundle(repo_root=_repo_root(), arc=58, phase="start")
    assert payload["schema"] == "arc_bundle_lint@1"
    assert payload["failures"] == []


def test_current_repo_v57_closeout_bundle_passes() -> None:
    module = _load_script_module()
    payload = module.lint_arc_bundle(repo_root=_repo_root(), arc=57, phase="closeout")
    assert payload["schema"] == "arc_bundle_lint@1"
    assert payload["failures"] == []


def test_start_bundle_fails_on_closeout_heading_and_wrong_phase(tmp_path: Path) -> None:
    _copy_start_bundle(arc=58, target_root=tmp_path)
    decision_doc = tmp_path / "docs" / "DRAFT_STOP_GATE_DECISION_vNEXT_PLUS58.md"
    text = decision_doc.read_text(encoding="utf-8")
    text = text.replace('"phase": "pre_start_scaffold"', '"phase": "post_closeout_decision"')
    text += "\n## Metric-Key Continuity Assertion\n\n```json\n{}\n```\n"
    decision_doc.write_text(text, encoding="utf-8")

    module = _load_script_module()
    payload = module.lint_arc_bundle(repo_root=tmp_path, arc=58, phase="start")

    failure_codes = {row["code"] for row in payload["failures"]}
    assert "STATE_FIELD_MISMATCH" in failure_codes
    assert "START_DOC_CLOSEOUT_HEADING_PRESENT" in failure_codes


def test_closeout_bundle_fails_on_invalid_event_stream(tmp_path: Path) -> None:
    _copy_closeout_bundle(arc=57, target_root=tmp_path)
    event_path = next(
        (
            tmp_path / "artifacts" / "agent_harness" / "v57" / "runtime" / "evidence"
        ).rglob("urm_events.ndjson")
    )
    event_path.write_text('{"schema":"urm-events@1"', encoding="utf-8")

    module = _load_script_module()
    payload = module.lint_arc_bundle(repo_root=tmp_path, arc=57, phase="closeout")

    failure_codes = {row["code"] for row in payload["failures"]}
    assert "EVENT_STREAM_INVALID" in failure_codes
