from __future__ import annotations

import json
from pathlib import Path

from adeu_api.main import (
    DiffRequest,
    ExplainDiffPacketResponse,
    ExplainFlipAdeuRequest,
    ExplainMaterializeRequest,
    diff_endpoint,
    explain_flip_endpoint,
    explain_materialize_endpoint,
)
from adeu_api.storage import get_explain_artifact_by_client_request_id
from adeu_explain import build_explain_diff_packet, validate_explain_diff_packet
from adeu_ir import AdeuIR
from fastapi import HTTPException


def _left_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_left",
            "context": {
                "doc_id": "doc:test:explain",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-10T00:00:00Z",
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "stmt_a",
                        "kind": "obligation",
                        "subject": {"ref_type": "text", "text": "Supplier"},
                        "action": {"verb": "deliver"},
                        "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                        "provenance": {
                            "doc_ref": "doc:test:explain#sec1",
                            "span": {"start": 0, "end": 12},
                        },
                    }
                ]
            },
        }
    )


def _right_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_right",
            "context": {
                "doc_id": "doc:test:explain",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-10T00:00:00Z",
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "stmt_a",
                        "kind": "prohibition",
                        "subject": {"ref_type": "text", "text": "Supplier"},
                        "action": {"verb": "deliver"},
                        "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                        "provenance": {
                            "doc_ref": "doc:test:explain#sec1",
                            "span": {"start": 0, "end": 12},
                        },
                    }
                ]
            },
        }
    )


def _simple_diff_report_payload() -> dict[str, object]:
    return {
        "left_id": "left",
        "right_id": "right",
        "structural": {"json_patches": [], "changed_paths": [], "changed_object_ids": []},
        "solver": {
            "left_runs": [],
            "right_runs": [],
            "status_flip": "NO_RUNS",
            "core_delta": {"added_atoms": [], "removed_atoms": []},
            "model_delta": {
                "added_assignments": [],
                "removed_assignments": [],
                "changed_assignments": [],
                "changed_atoms": [],
            },
            "request_hash_changed": False,
            "formula_hash_changed": False,
            "unpaired_left_hashes": [],
            "unpaired_right_hashes": [],
        },
        "causal_slice": {
            "touched_atoms": [],
            "touched_object_ids": [],
            "touched_json_paths": [],
            "explanation_items": [],
        },
        "summary": {
            "status_flip": "NO_RUNS",
            "solver_pairing_state": "NO_RUNS",
            "mapping_trust": "derived_bridge",
            "solver_trust": "kernel_only",
            "proof_trust": None,
            "unpaired_left_keys": [],
            "unpaired_right_keys": [],
            "structural_patch_count": "0",
            "solver_touched_atom_count": "0",
            "causal_atom_count": "0",
            "run_source": "recomputed",
            "recompute_mode": "LAX",
            "left_backend": None,
            "right_backend": None,
            "left_timeout_ms": None,
            "right_timeout_ms": None,
        },
    }


def test_diff_endpoint_explain_format_returns_packet() -> None:
    req = DiffRequest(left_ir=_left_ir(), right_ir=_right_ir())
    response = diff_endpoint(req, format="explain_diff@1")
    assert isinstance(response, ExplainDiffPacketResponse)
    assert response.schema == "explain_diff@1"
    assert response.explain_kind == "semantic_diff"
    assert len(response.input_artifact_refs) == 2
    validate_explain_diff_packet(response.model_dump(mode="json", exclude_none=True))


def test_explain_flip_endpoint_explain_format_returns_packet() -> None:
    req = ExplainFlipAdeuRequest(
        domain="adeu",
        left_ir=_left_ir(),
        right_ir=_right_ir(),
        left_validator_runs=[
            {
                "request_hash": "req-inline",
                "formula_hash": "f-inline",
                "status": "UNSAT",
                "evidence_json": {"unsat_core": ["atom_stmt"], "model": {}},
                "atom_map_json": {
                    "atom_stmt": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0/kind"}
                },
            }
        ],
        right_validator_runs=[
            {
                "request_hash": "req-inline",
                "formula_hash": "f-inline",
                "status": "SAT",
                "evidence_json": {"unsat_core": [], "model": {"atom_stmt": "True"}},
                "atom_map_json": {
                    "atom_stmt": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0/kind"}
                },
            }
        ],
    )
    response = explain_flip_endpoint(req, format="explain_diff@1")
    assert isinstance(response, ExplainDiffPacketResponse)
    assert response.explain_kind == "flip_explain"
    assert "diff_report" in response.sections
    assert "flip_explanation" in response.sections
    validate_explain_diff_packet(response.model_dump(mode="json", exclude_none=True))


def test_explain_materialize_endpoint_is_idempotent_and_emits_single_event(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    evidence_root = tmp_path / "evidence"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("URM_EVIDENCE_ROOT", str(evidence_root))

    packet = build_explain_diff_packet(
        explain_kind="semantic_diff",
        input_artifact_refs=["artifact:a", "artifact:b"],
        diff_report=_simple_diff_report_payload(),
    )
    req = ExplainMaterializeRequest(
        client_request_id="req-explain-1",
        explain_packet=packet,
        parent_stream_id="urm_policy:test_profile",
        parent_seq=11,
    )

    created = explain_materialize_endpoint(req)
    replay = explain_materialize_endpoint(req)

    assert created.idempotent_replay is False
    assert replay.idempotent_replay is True
    assert replay.explain_id == created.explain_id
    assert replay.explain_hash == created.explain_hash

    event_path = evidence_root / "governance" / "policy" / "test_profile" / "urm_events.ndjson"
    lines = [line for line in event_path.read_text(encoding="utf-8").splitlines() if line.strip()]
    assert len(lines) == 1
    payload = json.loads(lines[0])
    assert payload["event"] == "EXPLAIN_MATERIALIZED"
    assert payload["detail"]["client_request_id"] == "req-explain-1"


def test_explain_materialize_endpoint_idempotency_conflict_raises(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    evidence_root = tmp_path / "evidence"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("URM_EVIDENCE_ROOT", str(evidence_root))

    first_packet = build_explain_diff_packet(
        explain_kind="semantic_diff",
        input_artifact_refs=["artifact:a"],
        diff_report=_simple_diff_report_payload(),
    )
    second_packet = build_explain_diff_packet(
        explain_kind="semantic_diff",
        input_artifact_refs=["artifact:b"],
        diff_report=_simple_diff_report_payload(),
    )

    explain_materialize_endpoint(
        ExplainMaterializeRequest(
            client_request_id="req-explain-conflict",
            explain_packet=first_packet,
            parent_stream_id="urm_policy:test_profile",
            parent_seq=1,
        )
    )

    try:
        explain_materialize_endpoint(
            ExplainMaterializeRequest(
                client_request_id="req-explain-conflict",
                explain_packet=second_packet,
                parent_stream_id="urm_policy:test_profile",
                parent_seq=1,
            )
        )
        assert False, "expected idempotency conflict"
    except HTTPException as exc:
        assert exc.status_code == 409
        assert isinstance(exc.detail, dict)
        assert exc.detail["code"] == "URM_IDEMPOTENCY_KEY_CONFLICT"


def test_explain_materialize_invalid_ref_uses_frozen_error_code(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    evidence_root = tmp_path / "evidence"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("URM_EVIDENCE_ROOT", str(evidence_root))

    packet = build_explain_diff_packet(
        explain_kind="semantic_diff",
        input_artifact_refs=["artifact:a"],
        diff_report=_simple_diff_report_payload(),
    )
    packet["input_artifact_refs"] = ["bad:ref"]

    try:
        explain_materialize_endpoint(
            ExplainMaterializeRequest(
                client_request_id="req-invalid-ref",
                explain_packet=packet,
                parent_stream_id="urm_policy:test_profile",
                parent_seq=1,
            )
        )
        assert False, "expected invalid ref failure"
    except HTTPException as exc:
        assert exc.status_code == 400
        assert isinstance(exc.detail, dict)
        assert exc.detail["code"] == "URM_EXPLAIN_INVALID_REF"


def test_explain_materialize_rolls_back_artifact_when_event_emit_fails(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    evidence_root = tmp_path / "evidence"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("URM_EVIDENCE_ROOT", str(evidence_root))

    packet = build_explain_diff_packet(
        explain_kind="semantic_diff",
        input_artifact_refs=["artifact:a"],
        diff_report=_simple_diff_report_payload(),
    )
    req = ExplainMaterializeRequest(
        client_request_id="req-event-fail",
        explain_packet=packet,
        parent_stream_id="urm_policy:test_profile",
        parent_seq=7,
    )

    def _raise_emit(*, row):  # noqa: ANN001
        raise RuntimeError("emit failed")

    monkeypatch.setattr("adeu_api.main._emit_explain_materialized_event", _raise_emit)

    try:
        explain_materialize_endpoint(req)
        assert False, "expected event emit failure"
    except HTTPException as exc:
        assert exc.status_code == 500
        assert isinstance(exc.detail, dict)
        assert exc.detail["code"] == "URM_EXPLAIN_EVENT_EMIT_FAILED"

    persisted = get_explain_artifact_by_client_request_id(client_request_id=req.client_request_id)
    assert persisted is None
