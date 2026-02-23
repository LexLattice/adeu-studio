from __future__ import annotations

import json
from contextlib import nullcontext
from pathlib import Path

import adeu_api.main as api_main
import adeu_api.trust_invariant_vnext_plus22 as trust_invariant
import pytest
from adeu_api.hashing import canonical_json, sha256_text
from fastapi import HTTPException, Response


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _pair() -> dict[str, str]:
    return {
        "source_text_hash": "3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa",
        "core_ir_artifact_id": "core_ir.case_a_1",
        "concept_artifact_id": "concept.case_a_1",
    }


def _coherence_fixture_payload() -> dict[str, object]:
    path = (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "stop_gate"
        / "vnext_plus20"
        / "cross_ir_coherence_diagnostics_case_a_1.json"
    )
    return json.loads(path.read_text(encoding="utf-8"))


def _normative_advice_fixture_payload(*, fixture_name: str) -> dict[str, object]:
    path = (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "stop_gate"
        / "vnext_plus21"
        / f"normative_advice_packet_{fixture_name}.json"
    )
    return json.loads(path.read_text(encoding="utf-8"))


def _created_at_stripped_sha256(payload: dict[str, object]) -> str:
    return sha256_text(canonical_json(trust_invariant._strip_created_at_recursive(payload)))


@pytest.fixture(autouse=True)
def _clear_trust_invariant_manifest_caches() -> None:
    trust_invariant._coherence_fixture_index_for_manifest.cache_clear()
    trust_invariant._normative_advice_fixture_index_for_manifest.cache_clear()
    yield
    trust_invariant._coherence_fixture_index_for_manifest.cache_clear()
    trust_invariant._normative_advice_fixture_index_for_manifest.cache_clear()


def _build_packet(**kwargs: str | Path) -> dict[str, object]:
    with trust_invariant.trust_invariant_non_enforcement_context():
        return trust_invariant.build_trust_invariant_packet_vnext_plus22(**kwargs)


def test_build_trust_invariant_packet_requires_runtime_non_enforcement_context() -> None:
    with pytest.raises(trust_invariant.TrustInvariantVnextPlus22Error) as exc_info:
        trust_invariant.build_trust_invariant_packet_vnext_plus22(**_pair())

    assert exc_info.value.code == "URM_ADEU_TRUST_INVARIANT_REQUEST_INVALID"
    assert (
        exc_info.value.reason
        == "trust-invariant runtime non-enforcement context is not active"
    )


def test_build_trust_invariant_packet_is_deterministic_and_schema_valid() -> None:
    first = _build_packet(**_pair())
    second = _build_packet(**_pair())

    assert first["schema"] == "adeu_trust_invariant_packet@0.1"
    assert canonical_json(first) == canonical_json(second)

    proof_summary = first["proof_summary"]
    assert proof_summary["total_checks"] == 4
    assert proof_summary["passed_checks"] + proof_summary["failed_checks"] == 4
    assert proof_summary["counts_by_invariant_code"] == {
        "CANONICAL_JSON_CONFORMANCE": 1,
        "HASH_RECOMPUTE_MATCH": 1,
        "MANIFEST_CHAIN_STABILITY": 1,
        "REPLAY_HASH_STABILITY": 1,
    }

    proof_items = first["proof_items"]
    assert [item["invariant_code"] for item in proof_items] == [
        "CANONICAL_JSON_CONFORMANCE",
        "HASH_RECOMPUTE_MATCH",
        "MANIFEST_CHAIN_STABILITY",
        "REPLAY_HASH_STABILITY",
    ]

    replay_item = proof_items[3]
    assert replay_item["justification_refs"] == [
        (
            "artifact:adeu_trust_invariant_packet@0.1:"
            f"{_pair()['source_text_hash']}:{_pair()['core_ir_artifact_id']}:"
            f"{_pair()['concept_artifact_id']}"
        )
    ]
    assert "expected_hash" not in replay_item
    assert isinstance(replay_item["observed_hash"], str)
    assert len(replay_item["observed_hash"]) == 64

    canonical_item = proof_items[0]
    assert "expected_hash" not in canonical_item
    assert "observed_hash" not in canonical_item


def test_build_trust_invariant_packet_selects_lexicographically_first_normative_fixture() -> None:
    packet = _build_packet(**_pair())

    case_a_hash = _created_at_stripped_sha256(
        _normative_advice_fixture_payload(fixture_name="case_a_1")
    )
    case_b_hash = _created_at_stripped_sha256(
        _normative_advice_fixture_payload(fixture_name="case_b_1")
    )

    assert packet["normative_advice_packet_hash"] == case_a_hash
    assert case_a_hash != case_b_hash


def test_trust_invariant_pair_endpoint_returns_packet_and_cache_header() -> None:
    response = Response()
    payload = api_main.get_urm_proof_trust_pair_endpoint(
        source_text_hash=_pair()["source_text_hash"],
        core_ir_artifact_id=_pair()["core_ir_artifact_id"],
        concept_artifact_id=_pair()["concept_artifact_id"],
        response=response,
    ).model_dump(mode="json")

    assert payload["schema"] == "adeu_trust_invariant_packet@0.1"
    assert payload["proof_summary"]["total_checks"] == 4
    assert response.headers["Cache-Control"] == api_main._READ_SURFACE_CACHE_CONTROL


def test_trust_invariant_pair_endpoint_unknown_pair_returns_not_found() -> None:
    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_proof_trust_pair_endpoint(
            source_text_hash="f" * 64,
            core_ir_artifact_id=_pair()["core_ir_artifact_id"],
            concept_artifact_id=_pair()["concept_artifact_id"],
            response=Response(),
        )

    assert exc_info.value.status_code == 404
    assert exc_info.value.detail["code"] == "URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND"


def test_trust_invariant_pair_endpoint_missing_normative_artifact_returns_not_found(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest_path = tmp_path / "vnext_plus21_manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": "stop_gate.vnext_plus21_manifest@1",
                "normative_advice_packet_fixtures": [
                    {
                        "fixture_id": "normative_advice.packet.case_a",
                        "surface_id": "adeu.normative_advice.packet",
                        "source_text_hash": _pair()["source_text_hash"],
                        "core_ir_artifact_id": _pair()["core_ir_artifact_id"],
                        "concept_artifact_id": _pair()["concept_artifact_id"],
                        "runs": [
                            {
                                "normative_advice_packet_path": "missing_normative_packet.json",
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(
        trust_invariant,
        "VNEXT_PLUS21_STOP_GATE_MANIFEST_PATH",
        manifest_path,
    )
    trust_invariant._normative_advice_fixture_index_for_manifest.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_proof_trust_pair_endpoint(
            source_text_hash=_pair()["source_text_hash"],
            core_ir_artifact_id=_pair()["core_ir_artifact_id"],
            concept_artifact_id=_pair()["concept_artifact_id"],
            response=Response(),
        )

    assert exc_info.value.status_code == 404
    assert exc_info.value.detail["code"] == "URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND"


def test_build_trust_invariant_packet_manifest_chain_mismatch_emits_fail_item(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    coherence_payload = _coherence_fixture_payload()
    coherence_payload["bridge_manifest_hash"] = "0" * 64
    coherence_path = tmp_path / "coherence_mismatch.json"
    coherence_path.write_text(json.dumps(coherence_payload), encoding="utf-8")

    manifest_path = tmp_path / "vnext_plus20_manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": "stop_gate.vnext_plus20_manifest@1",
                "cross_ir_coherence_diagnostics_fixtures": [
                    {
                        "fixture_id": "cross_ir.coherence_diagnostics.case_a",
                        "surface_id": "adeu.cross_ir.coherence_diagnostics",
                        "source_text_hash": _pair()["source_text_hash"],
                        "core_ir_artifact_id": _pair()["core_ir_artifact_id"],
                        "concept_artifact_id": _pair()["concept_artifact_id"],
                        "runs": [
                            {
                                "cross_ir_coherence_diagnostics_path": str(coherence_path),
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(
        trust_invariant,
        "VNEXT_PLUS20_STOP_GATE_MANIFEST_PATH",
        manifest_path,
    )
    trust_invariant._coherence_fixture_index_for_manifest.cache_clear()

    payload = _build_packet(**_pair())
    assert payload["proof_summary"]["failed_checks"] == 1

    manifest_item = next(
        item
        for item in payload["proof_items"]
        if item["invariant_code"] == "MANIFEST_CHAIN_STABILITY"
    )
    assert manifest_item["status"] == "fail"
    assert manifest_item["expected_hash"] != manifest_item["observed_hash"]


def test_trust_invariant_pair_endpoint_coherence_replay_drift_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    coherence_payload_a = _coherence_fixture_payload()
    coherence_payload_b = _coherence_fixture_payload()
    coherence_payload_b["issues"][0]["message"] = "drifted coherence replay message"  # type: ignore[index]

    coherence_path_a = tmp_path / "coherence_a.json"
    coherence_path_b = tmp_path / "coherence_b.json"
    coherence_path_a.write_text(json.dumps(coherence_payload_a), encoding="utf-8")
    coherence_path_b.write_text(json.dumps(coherence_payload_b), encoding="utf-8")

    manifest_path = tmp_path / "vnext_plus20_manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": "stop_gate.vnext_plus20_manifest@1",
                "cross_ir_coherence_diagnostics_fixtures": [
                    {
                        "fixture_id": "cross_ir.coherence_diagnostics.case_a",
                        "surface_id": "adeu.cross_ir.coherence_diagnostics",
                        "source_text_hash": _pair()["source_text_hash"],
                        "core_ir_artifact_id": _pair()["core_ir_artifact_id"],
                        "concept_artifact_id": _pair()["concept_artifact_id"],
                        "runs": [
                            {
                                "cross_ir_coherence_diagnostics_path": str(coherence_path_a),
                            },
                            {
                                "cross_ir_coherence_diagnostics_path": str(coherence_path_b),
                            },
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(
        trust_invariant,
        "VNEXT_PLUS20_STOP_GATE_MANIFEST_PATH",
        manifest_path,
    )
    trust_invariant._coherence_fixture_index_for_manifest.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_proof_trust_pair_endpoint(
            source_text_hash=_pair()["source_text_hash"],
            core_ir_artifact_id=_pair()["core_ir_artifact_id"],
            concept_artifact_id=_pair()["concept_artifact_id"],
            response=Response(),
        )

    assert exc_info.value.status_code == 500
    assert exc_info.value.detail["code"] == "URM_ADEU_TRUST_INVARIANT_DIAGNOSTIC_DRIFT"


def test_trust_invariant_endpoint_fails_closed_on_non_enforcement_context_violation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(api_main, "trust_invariant_non_enforcement_context", nullcontext)

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_proof_trust_pair_endpoint(
            source_text_hash=_pair()["source_text_hash"],
            core_ir_artifact_id=_pair()["core_ir_artifact_id"],
            concept_artifact_id=_pair()["concept_artifact_id"],
            response=Response(),
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_TRUST_INVARIANT_REQUEST_INVALID"


def test_build_trust_invariant_packet_wraps_packet_validation_errors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FailPacket:
        @staticmethod
        def model_validate(_payload: object) -> object:
            raise ValueError("forced packet validation failure")

    monkeypatch.setattr(trust_invariant, "AdeuTrustInvariantPacket", _FailPacket)

    with pytest.raises(trust_invariant.TrustInvariantVnextPlus22Error) as exc_info:
        _build_packet(**_pair())

    assert exc_info.value.code == "URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID"
    assert exc_info.value.reason == "trust-invariant packet payload failed schema validation"
