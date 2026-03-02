from __future__ import annotations

import hashlib
import json
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
def test_real_lean_agreement_report_is_valid_and_deterministic() -> None:
    lean_bin = (os.environ.get("ADEU_LEAN_BIN") or os.environ.get("LEAN_BIN") or "lean").strip()
    lake_bin = (os.environ.get("ADEU_LAKE_BIN") or "lake").strip()

    reports = [
        build_agreement_report_from_fixture_path(
            fixture_path=_FIXTURE_PATH,
            timeout_ms=15_000,
            lean_bin=lean_bin,
            lake_bin=lake_bin,
            project_root=_PROJECT_ROOT,
        )
        for _ in range(3)
    ]
    validated_reports = [validate_agreement_report(report) for report in reports]
    canonical_reports = [
        json.dumps(
            validated,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        )
        for validated in validated_reports
    ]
    canonical_hashes = [
        hashlib.sha256(canonical.encode("utf-8")).hexdigest() for canonical in canonical_reports
    ]

    first = validated_reports[0]
    assert first["schema"] == "odeu_agreement.report@0.1"
    assert first["proof_semantics_version"] == "adeu.lean.core.v1"
    assert first["summary"]["total_rows"] == 6
    assert {row["lean_observed_status"] for row in first["fixtures"]} <= {"proved", "failed"}
    assert canonical_reports[0] == canonical_reports[1] == canonical_reports[2]
    assert canonical_hashes[0] == canonical_hashes[1] == canonical_hashes[2]
