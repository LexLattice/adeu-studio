from __future__ import annotations

import os
import socket
from pathlib import Path

import pytest
from adeu_api.main import (
    ArtifactCreateRequest,
    create_artifact_endpoint,
    list_artifact_proofs_endpoint,
)
from adeu_ir import AdeuIR
from adeu_kernel import KernelMode


def _sample_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_formal_lane_real_lean",
            "context": {
                "doc_id": "doc:test:formal:lean",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-06T00:00:00Z",
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "dn_keep_1",
                        "kind": "obligation",
                        "subject": {"ref_type": "text", "text": "Supplier"},
                        "action": {"verb": "deliver"},
                        "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                        "provenance": {
                            "doc_ref": "doc:test:formal:lean#sec1",
                            "span": {"start": 0, "end": 20},
                        },
                    }
                ]
            },
        }
    )


@pytest.mark.skipif(
    os.environ.get("ADEU_REQUIRE_REAL_LEAN_LANE") != "1",
    reason="real Lean CI lane only",
)
def test_real_lean_lane_uses_lean_backend_and_no_network(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_PROOF_BACKEND", "lean")
    monkeypatch.setenv("ADEU_LEAN_TIMEOUT_MS", "15000")

    def deny_create_connection(*args: object, **kwargs: object) -> None:
        raise AssertionError(f"unexpected outbound network call: {args} {kwargs}")

    def deny_socket_connect(self: socket.socket, *args: object, **kwargs: object) -> None:
        raise AssertionError(f"unexpected outbound socket connect: {args} {kwargs}")

    monkeypatch.setattr(socket, "create_connection", deny_create_connection)
    monkeypatch.setattr(socket.socket, "connect", deny_socket_connect)

    created = create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )
    proofs = list_artifact_proofs_endpoint(created.artifact_id)

    assert created.solver_trust in {"proof_checked", "solver_backed"}
    assert created.proof_trust in {"lean_core_v1_proved", "lean_core_v1_partial_or_failed"}
    assert created.proof_trust != "mock_backend_not_proof_checked"
    assert len(proofs.items) >= 3
    assert {item.proof.backend for item in proofs.items} == {"lean"}
