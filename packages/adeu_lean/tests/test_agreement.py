from __future__ import annotations

import hashlib
import json
import socket
from pathlib import Path
from typing import cast

import pytest
from adeu_lean import (
    AgreementHarnessError,
    LeanRequest,
    LeanResult,
    build_agreement_report,
    build_agreement_report_from_fixture_path,
    load_agreement_fixture_bundle,
    validate_agreement_report,
)

FIXTURE_PATH = Path(__file__).resolve().parent / "fixtures" / "agreement_fixtures_v30.json"
_LOCKED_PROVED_REPORT_HASH = "8756d9b7255db1e26b2b18c5979c2f393c043e33ed8a9425ab57dfb67721070f"


def _proof_hash(seed: str) -> str:
    return hashlib.sha256(seed.encode("utf-8")).hexdigest()


def _canonical_sha256(payload: object) -> str:
    serialized = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    )
    return hashlib.sha256(
        serialized.encode("utf-8")
    ).hexdigest()


def _proved_result(theorem_id: str) -> LeanResult:
    return LeanResult(
        theorem_id=theorem_id,
        status="proved",
        proof_hash=_proof_hash(theorem_id),
        details={},
    )


def _fake_proved_run_request(request: LeanRequest) -> LeanResult:
    return _proved_result(request.theorem_id)


def test_build_agreement_report_is_deterministic_and_ordered() -> None:
    bundle = load_agreement_fixture_bundle(FIXTURE_PATH)

    left = build_agreement_report(
        fixture_bundle=bundle,
        timeout_ms=1000,
        lean_bin="/tmp/lean-not-used",
        run_request=_fake_proved_run_request,
    )
    right = build_agreement_report(
        fixture_bundle=bundle,
        timeout_ms=1000,
        lean_bin="/tmp/lean-not-used",
        run_request=_fake_proved_run_request,
    )

    assert left == right
    assert left["schema"] == "odeu_agreement.report@0.1"
    assert left["proof_semantics_version"] == bundle.proof_semantics_version
    assert left["summary"] == {
        "total_rows": 6,
        "agree_rows": 6,
        "disagree_rows": 0,
        "all_agree": True,
        "fail_closed": False,
    }

    rows = left["fixtures"]
    ordered = sorted(rows, key=lambda row: (row["fixture_id"], row["obligation_kind"]))
    assert rows == ordered
    assert {row["obligation_kind"] for row in rows} == {
        "pred_closed_world",
        "exception_gating",
        "conflict_soundness",
    }
    assert all(len(row["mapping_id"]) == 64 for row in rows)
    assert all(len(row["proof_hash"]) == 64 for row in rows)


def test_build_agreement_report_matches_locked_hash_baseline() -> None:
    bundle = load_agreement_fixture_bundle(FIXTURE_PATH)
    report = build_agreement_report(
        fixture_bundle=bundle,
        timeout_ms=1000,
        lean_bin="/tmp/lean-not-used",
        run_request=_fake_proved_run_request,
    )
    assert _canonical_sha256(report) == _LOCKED_PROVED_REPORT_HASH


def test_build_agreement_report_fail_closed_on_status_disagreement() -> None:
    bundle = load_agreement_fixture_bundle(FIXTURE_PATH)

    def fake_run_request(request: LeanRequest) -> LeanResult:
        if request.theorem_id.endswith("conflict_soundness"):
            return LeanResult(
                theorem_id=request.theorem_id,
                status="failed",
                proof_hash=_proof_hash("failed::" + request.theorem_id),
                details={},
            )
        return _proved_result(request.theorem_id)

    report = build_agreement_report(
        fixture_bundle=bundle,
        timeout_ms=1000,
        lean_bin="/tmp/lean-not-used",
        run_request=fake_run_request,
    )

    assert report["summary"] == {
        "total_rows": 6,
        "agree_rows": 4,
        "disagree_rows": 2,
        "all_agree": False,
        "fail_closed": True,
    }
    disagree_rows = [row for row in report["fixtures"] if row["agreement"] is False]
    assert len(disagree_rows) == 2


def test_build_agreement_report_marks_identity_mismatch_as_disagreement() -> None:
    bundle = load_agreement_fixture_bundle(FIXTURE_PATH)

    def fake_run_request(request: LeanRequest) -> LeanResult:
        if request.theorem_id.endswith("pred_closed_world"):
            return LeanResult(
                theorem_id=request.theorem_id + "_mismatch",
                status="proved",
                proof_hash=_proof_hash("mismatch::" + request.theorem_id),
                details={},
            )
        return _proved_result(request.theorem_id)

    report = build_agreement_report(
        fixture_bundle=bundle,
        timeout_ms=1000,
        lean_bin="/tmp/lean-not-used",
        run_request=fake_run_request,
    )

    assert report["summary"]["disagree_rows"] == 2
    assert report["summary"]["fail_closed"] is True


def test_build_agreement_report_rejects_non_positive_timeout() -> None:
    bundle = load_agreement_fixture_bundle(FIXTURE_PATH)
    with pytest.raises(AgreementHarnessError, match="timeout_ms must be positive"):
        build_agreement_report(
            fixture_bundle=bundle,
            timeout_ms=0,
            lean_bin="/tmp/lean-not-used",
            run_request=_fake_proved_run_request,
        )


def test_build_agreement_report_rejects_non_hex_proof_hash() -> None:
    bundle = load_agreement_fixture_bundle(FIXTURE_PATH)

    def fake_run_request(request: LeanRequest) -> LeanResult:
        return LeanResult(
            theorem_id=request.theorem_id,
            status="proved",
            proof_hash="not-a-sha256",
            details={},
        )

    with pytest.raises(
        AgreementHarnessError,
        match="proof_hash must be 64-char lowercase SHA-256 hex",
    ):
        build_agreement_report(
            fixture_bundle=bundle,
            timeout_ms=1000,
            lean_bin="/tmp/lean-not-used",
            run_request=fake_run_request,
        )


def test_build_agreement_report_rejects_unknown_status() -> None:
    bundle = load_agreement_fixture_bundle(FIXTURE_PATH)

    def fake_run_request(request: LeanRequest) -> LeanResult:
        return cast(
            LeanResult,
            LeanResult.model_construct(
                theorem_id=request.theorem_id,
                status="error",
                proof_hash=_proof_hash(request.theorem_id),
                details={},
            ),
        )

    with pytest.raises(AgreementHarnessError, match="unsupported lean_observed_status"):
        build_agreement_report(
            fixture_bundle=bundle,
            timeout_ms=1000,
            lean_bin="/tmp/lean-not-used",
            run_request=fake_run_request,
        )


def test_load_agreement_fixture_bundle_missing_file_fails_closed(tmp_path: Path) -> None:
    missing_path = tmp_path / "missing.json"
    with pytest.raises(AgreementHarnessError, match="missing fixture bundle"):
        load_agreement_fixture_bundle(missing_path)


def test_load_agreement_fixture_bundle_invalid_schema_fails_closed(tmp_path: Path) -> None:
    invalid_path = tmp_path / "invalid.json"
    invalid_path.write_text(
        json.dumps(
            {
                "schema": "odeu_agreement.fixtures@0.1",
                "proof_semantics_version": "adeu.lean.core.v1",
                "fixtures": [
                    {
                        "fixture_id": "fx",
                        "theorem_prefix": "ir_fx",
                        "inputs": [],
                        "python_expected_status": {
                            "pred_closed_world": "proved",
                            "exception_gating": "proved",
                        },
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    with pytest.raises(
        AgreementHarnessError,
        match="schema-invalid agreement fixtures",
    ):
        load_agreement_fixture_bundle(invalid_path)


def test_validate_agreement_report_rejects_summary_drift() -> None:
    bundle = load_agreement_fixture_bundle(FIXTURE_PATH)
    report = build_agreement_report(
        fixture_bundle=bundle,
        timeout_ms=1000,
        lean_bin="/tmp/lean-not-used",
        run_request=_fake_proved_run_request,
    )
    report["summary"]["disagree_rows"] = 1

    with pytest.raises(AgreementHarnessError, match="schema-invalid agreement report"):
        validate_agreement_report(report)


def test_build_agreement_report_from_fixture_path_matches_direct_builder() -> None:
    bundle = load_agreement_fixture_bundle(FIXTURE_PATH)

    direct = build_agreement_report(
        fixture_bundle=bundle,
        timeout_ms=1000,
        lean_bin="/tmp/lean-not-used",
        run_request=_fake_proved_run_request,
    )
    from_path = build_agreement_report_from_fixture_path(
        fixture_path=FIXTURE_PATH,
        timeout_ms=1000,
        lean_bin="/tmp/lean-not-used",
        run_request=_fake_proved_run_request,
    )

    assert direct == from_path


def test_build_agreement_report_from_fixture_path_does_not_mutate_fixture_snapshot() -> None:
    before = FIXTURE_PATH.read_bytes()
    report = build_agreement_report_from_fixture_path(
        fixture_path=FIXTURE_PATH,
        timeout_ms=1000,
        lean_bin="/tmp/lean-not-used",
        run_request=_fake_proved_run_request,
    )
    after = FIXTURE_PATH.read_bytes()

    assert report["summary"]["all_agree"] is True
    assert before == after


def test_build_agreement_report_no_network_calls(monkeypatch: pytest.MonkeyPatch) -> None:
    bundle = load_agreement_fixture_bundle(FIXTURE_PATH)

    def deny_create_connection(*args: object, **kwargs: object) -> None:
        raise AssertionError(f"unexpected outbound network call: {args} {kwargs}")

    def deny_socket_connect(self: socket.socket, *args: object, **kwargs: object) -> None:
        raise AssertionError(f"unexpected outbound socket connect: {args} {kwargs}")

    monkeypatch.setattr(socket, "create_connection", deny_create_connection)
    monkeypatch.setattr(socket.socket, "connect", deny_socket_connect)
    report = build_agreement_report(
        fixture_bundle=bundle,
        timeout_ms=1000,
        lean_bin="/tmp/lean-not-used",
        run_request=_fake_proved_run_request,
    )

    assert report["summary"]["all_agree"] is True
