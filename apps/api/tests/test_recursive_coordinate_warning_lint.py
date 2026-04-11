from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path


def _repo_root() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        git_marker = parent / ".git"
        if git_marker.is_dir() or git_marker.is_file():
            return parent
    raise FileNotFoundError("repository root not found")


def _script_path() -> Path:
    return _repo_root() / "apps" / "api" / "scripts" / "lint_recursive_coordinate_warnings.py"


def _pythonpath_env() -> dict[str, str]:
    repo_root = _repo_root()
    env = os.environ.copy()
    existing = env.get("PYTHONPATH")
    paths = [
        str(repo_root / "apps" / "api" / "src"),
        str(repo_root / "packages" / "urm_runtime" / "src"),
    ]
    if existing:
        paths.append(existing)
    env["PYTHONPATH"] = os.pathsep.join(paths)
    env["TZ"] = "UTC"
    env["LC_ALL"] = "C"
    return env


def _run_lint(*, docs: list[Path] | None = None) -> subprocess.CompletedProcess[str]:
    repo_root = _repo_root()
    command = [sys.executable, str(_script_path())]
    for doc in docs or []:
        command.extend(["--doc", str(doc)])
    return subprocess.run(
        command,
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def _write_coordinate_doc(tmp_path: Path, *, payload: dict[str, object]) -> Path:
    doc_path = tmp_path / "coordinate.md"
    doc_path.write_text(
        "# Coordinate Test\n\n```json\n"
        + json.dumps(payload, indent=2, sort_keys=True)
        + "\n```\n",
        encoding="utf-8",
    )
    return doc_path


def test_recursive_coordinate_warning_lint_passes_on_current_pilot_reports() -> None:
    completed = _run_lint()
    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stderr == ""

    payload = json.loads(completed.stdout)
    assert payload["schema"] == "recursive_coordinate_warning_lint@1"
    assert payload["warning_count"] == 0
    assert payload["checked_record_count"] == 14
    assert payload["checked_docs"] == [
        "docs/DRAFT_RECURSIVE_COORDINATE_SEED_PLACEMENT_REPORT_v0.md",
        "docs/DRAFT_RECURSIVE_COORDINATE_STRESS_CELL_PLACEMENT_REPORT_v0.md",
    ]


def test_recursive_coordinate_warning_lint_emits_expected_non_blocking_warnings(
    tmp_path: Path,
) -> None:
    doc_path = _write_coordinate_doc(
        tmp_path,
        payload={
            "schema": "recursive_schema_coordinate@1",
            "placement_subject_ref": "docs/example.md",
            "coordinate": {
                "binding_depth": "meta",
                "institutional_force": "interpretive",
            },
            "force_profile": {
                "support_qualifiers": [],
            },
            "promotion_claim": "raise_to_governing",
        },
    )

    completed = _run_lint(docs=[doc_path])
    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)

    warning_codes = {row["code"] for row in payload["warnings"]}
    assert warning_codes == {
        "MISSING_PLACEMENT_BASIS",
        "MISSING_REQUIRED_COVERAGE_SCOPE",
        "PROMOTION_WITHOUT_WITNESS",
        "UNRESOLVED_DOMINANT_FORCE_BAND",
    }


def test_recursive_coordinate_warning_lint_warns_on_invalid_occupancy(tmp_path: Path) -> None:
    doc_path = _write_coordinate_doc(
        tmp_path,
        payload={
            "schema": "recursive_schema_coordinate@1",
            "placement_subject_ref": "packages/example/schema/example.v1.json",
            "placement_basis": "schema_kind_definition",
            "coordinate": {
                "binding_depth": "bounded",
                "institutional_force": "operative",
            },
            "force_profile": {
                "dominant_band": "operative",
                "support_qualifiers": [],
            },
        },
    )

    completed = _run_lint(docs=[doc_path])
    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)

    assert payload["warning_count"] == 1
    assert payload["warnings"][0]["code"] == "INVALID_OCCUPANCY"
