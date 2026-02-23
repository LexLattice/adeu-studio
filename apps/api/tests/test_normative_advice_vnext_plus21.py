from __future__ import annotations

import json
from pathlib import Path

import adeu_api.main as api_main
import adeu_api.normative_advice_vnext_plus21 as normative_advice
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


@pytest.fixture(autouse=True)
def _clear_normative_advice_manifest_cache() -> None:
    normative_advice._coherence_fixture_index_for_manifest.cache_clear()
    yield
    normative_advice._coherence_fixture_index_for_manifest.cache_clear()


def test_build_normative_advice_packet_is_deterministic_and_schema_valid() -> None:
    first = normative_advice.build_normative_advice_packet_vnext_plus21(**_pair())
    second = normative_advice.build_normative_advice_packet_vnext_plus21(**_pair())

    assert first["schema"] == "adeu_normative_advice_packet@0.1"
    assert canonical_json(first) == canonical_json(second)
    assert first["advice_summary"]["total_advice"] == len(first["advice_items"])
    assert first["advice_summary"]["counts_by_code"] == {
        "SOURCE_DIVERGENCE_REVIEW": 1,
    }
    assert first["advice_summary"]["counts_by_priority"] == {
        "high": 1,
    }
    for advice in first["advice_items"]:
        assert advice["justification_refs"] == sorted(advice["justification_refs"])
        assert len(advice["justification_refs"]) == 1
        expected_advice_id = sha256_text(
            canonical_json(
                {
                    "advice_code": advice["advice_code"],
                    "concept_refs": advice["concept_refs"],
                    "core_ir_refs": advice["core_ir_refs"],
                    "justification_refs": advice["justification_refs"],
                }
            )
        )[:16]
        assert advice["advice_id"] == expected_advice_id


def test_build_normative_advice_packet_refs_are_verbatim_from_source_issue() -> None:
    packet = normative_advice.build_normative_advice_packet_vnext_plus21(**_pair())
    coherence_payload = _coherence_fixture_payload()
    coherence_issue_by_id = {
        str(issue["issue_id"]): issue for issue in coherence_payload["issues"]  # type: ignore[index]
    }
    for advice in packet["advice_items"]:
        issue_ref = advice["justification_refs"][0]
        issue_id = issue_ref.split(":", 1)[1]
        source_issue = coherence_issue_by_id[issue_id]
        assert advice["concept_refs"] == source_issue["concept_refs"]
        assert advice["core_ir_refs"] == source_issue["core_ir_refs"]


def test_build_normative_advice_packet_source_issue_snapshot_opt_in() -> None:
    packet = normative_advice.build_normative_advice_packet_vnext_plus21(
        **_pair(),
        include_source_issue_snapshot=True,
    )
    for advice in packet["advice_items"]:
        snapshot = advice["source_issue_snapshot"]
        assert snapshot["issue_id"] == advice["justification_refs"][0].split(":", 1)[1]
        assert snapshot["issue_code"] == "SOURCE_HASH_MISMATCH"
        assert "evidence" in snapshot


def test_normative_advice_pair_endpoint_returns_packet_and_cache_header() -> None:
    response = Response()
    payload = api_main.get_urm_normative_advice_pair_endpoint(
        source_text_hash=_pair()["source_text_hash"],
        core_ir_artifact_id=_pair()["core_ir_artifact_id"],
        concept_artifact_id=_pair()["concept_artifact_id"],
        response=response,
    ).model_dump(mode="json")

    assert payload["schema"] == "adeu_normative_advice_packet@0.1"
    assert payload["advice_summary"]["total_advice"] == 1
    assert response.headers["Cache-Control"] == api_main._READ_SURFACE_CACHE_CONTROL


def test_normative_advice_pair_endpoint_unknown_pair_returns_not_found() -> None:
    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_normative_advice_pair_endpoint(
            source_text_hash="f" * 64,
            core_ir_artifact_id=_pair()["core_ir_artifact_id"],
            concept_artifact_id=_pair()["concept_artifact_id"],
            response=Response(),
        )

    assert exc_info.value.status_code == 404
    assert exc_info.value.detail["code"] == "URM_ADEU_NORMATIVE_ADVICE_ARTIFACT_NOT_FOUND"


def test_normative_advice_pair_endpoint_missing_coherence_artifact_returns_not_found(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
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
                                "cross_ir_coherence_diagnostics_path": "missing_coherence.json",
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(normative_advice, "VNEXT_PLUS20_STOP_GATE_MANIFEST_PATH", manifest_path)
    normative_advice._coherence_fixture_index_for_manifest.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_normative_advice_pair_endpoint(
            source_text_hash=_pair()["source_text_hash"],
            core_ir_artifact_id=_pair()["core_ir_artifact_id"],
            concept_artifact_id=_pair()["concept_artifact_id"],
            response=Response(),
        )

    assert exc_info.value.status_code == 404
    assert exc_info.value.detail["code"] == "URM_ADEU_NORMATIVE_ADVICE_ARTIFACT_NOT_FOUND"


def test_normative_advice_pair_endpoint_bridge_manifest_hash_mismatch_returns_payload_invalid(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
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
    monkeypatch.setattr(normative_advice, "VNEXT_PLUS20_STOP_GATE_MANIFEST_PATH", manifest_path)
    normative_advice._coherence_fixture_index_for_manifest.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_normative_advice_pair_endpoint(
            source_text_hash=_pair()["source_text_hash"],
            core_ir_artifact_id=_pair()["core_ir_artifact_id"],
            concept_artifact_id=_pair()["concept_artifact_id"],
            response=Response(),
        )

    assert exc_info.value.status_code == 500
    assert exc_info.value.detail["code"] == "URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID"
