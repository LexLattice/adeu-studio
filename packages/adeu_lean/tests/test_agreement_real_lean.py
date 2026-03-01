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

    report_a = build_agreement_report_from_fixture_path(
        fixture_path=_FIXTURE_PATH,
        timeout_ms=15_000,
        lean_bin=lean_bin,
        lake_bin=lake_bin,
        project_root=_PROJECT_ROOT,
    )
    report_b = build_agreement_report_from_fixture_path(
        fixture_path=_FIXTURE_PATH,
        timeout_ms=15_000,
        lean_bin=lean_bin,
        lake_bin=lake_bin,
        project_root=_PROJECT_ROOT,
    )
    validated_a = validate_agreement_report(report_a)
    validated_b = validate_agreement_report(report_b)
    canonical_a = json.dumps(
        validated_a,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    )
    canonical_b = json.dumps(
        validated_b,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    )

    assert validated_a["schema"] == "odeu_agreement.report@0.1"
    assert validated_a["proof_semantics_version"] == "adeu.lean.core.v1"
    assert validated_a["summary"]["total_rows"] == 6
    assert {row["lean_observed_status"] for row in validated_a["fixtures"]} <= {"proved", "failed"}
    assert hashlib.sha256(canonical_a.encode("utf-8")).hexdigest() == hashlib.sha256(
        canonical_b.encode("utf-8")
    ).hexdigest()
