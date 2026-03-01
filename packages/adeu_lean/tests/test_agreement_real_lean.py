from __future__ import annotations

import os
from pathlib import Path

import pytest
from adeu_lean import build_agreement_report_from_fixture_path, validate_agreement_report

_FIXTURE_PATH = Path(__file__).resolve().parent / "fixtures" / "agreement_fixtures_v30.json"
_PROJECT_ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.skipif(
    os.environ.get("ADEU_REQUIRE_REAL_LEAN_LANE") != "1",
    reason="real Lean CI lane only",
)
def test_real_lean_agreement_report_all_agree() -> None:
    lean_bin = (os.environ.get("ADEU_LEAN_BIN") or os.environ.get("LEAN_BIN") or "lean").strip()
    lake_bin = (os.environ.get("ADEU_LAKE_BIN") or "lake").strip()

    report = build_agreement_report_from_fixture_path(
        fixture_path=_FIXTURE_PATH,
        timeout_ms=15_000,
        lean_bin=lean_bin,
        lake_bin=lake_bin,
        project_root=_PROJECT_ROOT,
    )
    validated = validate_agreement_report(report)

    assert validated["summary"]["all_agree"] is True
    assert validated["summary"]["fail_closed"] is False
    assert validated["summary"]["disagree_rows"] == 0
    assert {row["lean_observed_status"] for row in validated["fixtures"]} == {"proved"}
