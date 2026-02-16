from __future__ import annotations

import json
from pathlib import Path

from adeu_api.main import (
    ConceptSemanticDepthRequest,
    SemanticDepthMaterializeRequest,
    concepts_semantic_depth_endpoint,
    semantic_depth_materialize_endpoint,
)
from adeu_api.storage import get_semantic_depth_report_by_client_request_id
from adeu_concepts import ConceptIR
from adeu_semantic_depth import build_semantic_depth_report, semantic_depth_hash
from fastapi import HTTPException


def _concept_ir(doc_id: str, *, gloss: str, claim_text: str, link_kind: str) -> ConceptIR:
    return ConceptIR.model_validate(
        {
            "schema_version": "adeu.concepts.v0",
            "concept_id": f"concept:{doc_id}",
            "context": {"doc_id": doc_id},
            "terms": [{"id": "term_pay", "label": "Payment"}],
            "senses": [{"id": "sense_pay", "term_id": "term_pay", "gloss": gloss}],
            "claims": [{"id": "claim_pay", "sense_id": "sense_pay", "text": claim_text}],
            "links": [
                {
                    "id": "link_pay",
                    "kind": link_kind,
                    "src_sense_id": "sense_pay",
                    "dst_sense_id": "sense_pay",
                }
            ],
        }
    )


def _packet() -> dict[str, object]:
    return build_semantic_depth_report(
        input_artifact_refs=["artifact:a", "artifact:b"],
        conflict_items=[
            {
                "conflict_key": {
                    "kind": "status_flip",
                    "subject_ref": {"ref_type": "doc", "doc_ref": "doc:a"},
                    "object_ref": {"ref_type": "doc", "doc_ref": "doc:b"},
                }
            }
        ],
    )


def test_concepts_semantic_depth_endpoint_returns_packet() -> None:
    response = concepts_semantic_depth_endpoint(
        ConceptSemanticDepthRequest(
            left_ir=_concept_ir(
                "doc:left",
                gloss="pay within 5 days",
                claim_text="must pay in 5 days",
                link_kind="incompatibility",
            ),
            right_ir=_concept_ir(
                "doc:right",
                gloss="pay within 10 days",
                claim_text="must pay in 10 days",
                link_kind="commitment",
            ),
        )
    )

    assert response.schema == "semantic_depth_report@1"
    assert len(response.input_artifact_refs) == 2
    assert response.semantic_depth_hash


def test_semantic_depth_materialize_is_idempotent_and_emits_single_event(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    evidence_root = tmp_path / "evidence"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("URM_EVIDENCE_ROOT", str(evidence_root))

    req = SemanticDepthMaterializeRequest(
        client_request_id="req-semantic-depth-1",
        semantic_depth_report=_packet(),
        parent_stream_id="urm_policy:test_profile",
        parent_seq=21,
    )
    created = semantic_depth_materialize_endpoint(req)
    replay = semantic_depth_materialize_endpoint(req)

    assert created.idempotent_replay is False
    assert replay.idempotent_replay is True
    assert replay.semantic_depth_report_id == created.semantic_depth_report_id
    assert replay.semantic_depth_hash == created.semantic_depth_hash

    event_path = evidence_root / "governance" / "policy" / "test_profile" / "urm_events.ndjson"
    lines = [line for line in event_path.read_text(encoding="utf-8").splitlines() if line.strip()]
    assert len(lines) == 1
    payload = json.loads(lines[0])
    assert payload["event"] == "SEMANTIC_DEPTH_MATERIALIZED"
    assert payload["detail"]["client_request_id"] == "req-semantic-depth-1"


def test_semantic_depth_materialize_idempotency_conflict_raises(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    evidence_root = tmp_path / "evidence"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("URM_EVIDENCE_ROOT", str(evidence_root))

    first_packet = build_semantic_depth_report(
        input_artifact_refs=["artifact:a", "artifact:b"],
        conflict_items=[],
    )
    second_packet = build_semantic_depth_report(
        input_artifact_refs=["artifact:c", "artifact:d"],
        conflict_items=[],
    )

    semantic_depth_materialize_endpoint(
        SemanticDepthMaterializeRequest(
            client_request_id="req-semantic-depth-conflict",
            semantic_depth_report=first_packet,
            parent_stream_id="urm_policy:test_profile",
            parent_seq=1,
        )
    )

    try:
        semantic_depth_materialize_endpoint(
            SemanticDepthMaterializeRequest(
                client_request_id="req-semantic-depth-conflict",
                semantic_depth_report=second_packet,
                parent_stream_id="urm_policy:test_profile",
                parent_seq=1,
            )
        )
        assert False, "expected idempotency conflict"
    except HTTPException as exc:
        assert exc.status_code == 409
        assert isinstance(exc.detail, dict)
        assert exc.detail["code"] == "URM_SEMANTIC_DEPTH_IDEMPOTENCY_CONFLICT"


def test_semantic_depth_materialize_invalid_ref_uses_frozen_error_code(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    evidence_root = tmp_path / "evidence"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("URM_EVIDENCE_ROOT", str(evidence_root))

    packet = _packet()
    packet["input_artifact_refs"] = ["bad:ref", "artifact:b"]

    try:
        semantic_depth_materialize_endpoint(
            SemanticDepthMaterializeRequest(
                client_request_id="req-semantic-depth-invalid-ref",
                semantic_depth_report=packet,
                parent_stream_id="urm_policy:test_profile",
                parent_seq=1,
            )
        )
        assert False, "expected invalid ref failure"
    except HTTPException as exc:
        assert exc.status_code == 400
        assert isinstance(exc.detail, dict)
        assert exc.detail["code"] == "URM_SEMANTIC_DEPTH_INVALID_REF"


def test_semantic_depth_materialize_rejects_path_traversal_event_ref(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    evidence_root = tmp_path / "evidence"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("URM_EVIDENCE_ROOT", str(evidence_root))

    packet = _packet()
    packet["diff_refs"] = ["event:../escape#1"]
    packet["semantic_depth_hash"] = semantic_depth_hash(packet)

    try:
        semantic_depth_materialize_endpoint(
            SemanticDepthMaterializeRequest(
                client_request_id="req-semantic-depth-traversal-ref",
                semantic_depth_report=packet,
                parent_stream_id="urm_policy:test_profile",
                parent_seq=1,
            )
        )
        assert False, "expected invalid ref failure"
    except HTTPException as exc:
        assert exc.status_code == 400
        assert isinstance(exc.detail, dict)
        assert exc.detail["code"] == "URM_SEMANTIC_DEPTH_INVALID_REF"


def test_semantic_depth_materialize_rolls_back_when_event_emit_fails(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    evidence_root = tmp_path / "evidence"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("URM_EVIDENCE_ROOT", str(evidence_root))

    req = SemanticDepthMaterializeRequest(
        client_request_id="req-semantic-depth-event-fail",
        semantic_depth_report=_packet(),
        parent_stream_id="urm_policy:test_profile",
        parent_seq=7,
    )

    def _raise_emit(*, row):  # noqa: ANN001
        raise RuntimeError("emit failed")

    monkeypatch.setattr("adeu_api.main._emit_semantic_depth_materialized_event", _raise_emit)

    try:
        semantic_depth_materialize_endpoint(req)
        assert False, "expected event emit failure"
    except HTTPException as exc:
        assert exc.status_code == 500
        assert isinstance(exc.detail, dict)
        assert exc.detail["code"] == "URM_SEMANTIC_DEPTH_EVENT_EMIT_FAILED"

    persisted = get_semantic_depth_report_by_client_request_id(
        client_request_id=req.client_request_id
    )
    assert persisted is None
