from __future__ import annotations

from typing import Any, Literal

from adeu_explain import (
    ConceptAnalysisDelta,
    DiffReport,
    FlipExplanation,
    build_explain_diff_packet,
    inline_source_ref,
    validate_explain_diff_packet,
)
from pydantic import BaseModel

from .hashing import sha256_canonical_json


def as_artifact_ref(value: str) -> str:
    return f"artifact:{value}"


def as_explain_artifact_ref(explain_id: str) -> str:
    return f"artifact:explain:{explain_id}"


def model_payload(value: Any) -> Any:
    if isinstance(value, BaseModel):
        return value.model_dump(mode="json", exclude_none=True)
    return value


def input_ref_for_side(
    *,
    domain: str,
    side: Literal["left", "right"],
    artifact_id: str | None,
    ir: Any,
    source_text: str | None = None,
    doc_id: str | None = None,
) -> str:
    if artifact_id:
        return as_artifact_ref(artifact_id)
    payload: dict[str, Any] = {
        "domain": domain,
        "side": side,
        "ir": model_payload(ir),
    }
    if source_text is not None:
        payload["source_text"] = source_text
    if doc_id is not None:
        payload["doc_id"] = doc_id
    return inline_source_ref(payload)


def build_diff_refs_for_packet(
    *,
    diff_report: DiffReport,
    explain_kind: str,
) -> list[str]:
    payload = {
        "explain_kind": explain_kind,
        "left_id": diff_report.left_id,
        "right_id": diff_report.right_id,
        "status_flip": diff_report.summary.status_flip,
        "solver_pairing_state": diff_report.summary.solver_pairing_state,
    }
    digest = sha256_canonical_json(payload)
    return [f"artifact:diff_sha256:{digest}"]


def build_witness_refs_for_packet(diff_report: DiffReport) -> list[str]:
    refs: set[str] = set()
    for item in diff_report.causal_slice.explanation_items:
        digest = sha256_canonical_json(
            {
                "atom_name": item.atom_name,
                "object_id": item.object_id,
                "json_path": item.json_path,
            }
        )
        refs.add(f"artifact:witness_sha256:{digest}")
    return sorted(refs)


def build_validator_packet_refs_for_packet(diff_report: DiffReport) -> list[str]:
    refs: set[str] = set()
    for run in [*diff_report.solver.left_runs, *diff_report.solver.right_runs]:
        request_hash = (run.request_hash or "").strip()
        formula_hash = (run.formula_hash or "").strip()
        run_id = (run.run_id or "").strip()
        if request_hash and formula_hash:
            refs.add(f"artifact:validator_evidence:{request_hash}:{formula_hash}")
            continue
        if run_id:
            refs.add(f"artifact:validator_run:{run_id}")
    return sorted(refs)


def build_explain_packet_payload(
    *,
    explain_kind: str,
    diff_report: DiffReport,
    input_artifact_refs: list[str],
    flip_explanation: FlipExplanation | None = None,
    analysis_delta: ConceptAnalysisDelta | None = None,
    run_ir_mismatch: bool | None = None,
    left_mismatch: bool | None = None,
    right_mismatch: bool | None = None,
) -> dict[str, Any]:
    packet = build_explain_diff_packet(
        explain_kind=explain_kind,
        input_artifact_refs=input_artifact_refs,
        diff_report=diff_report,
        diff_refs=build_diff_refs_for_packet(
            diff_report=diff_report,
            explain_kind=explain_kind,
        ),
        witness_refs=build_witness_refs_for_packet(diff_report),
        validator_evidence_packet_refs=build_validator_packet_refs_for_packet(diff_report),
        flip_explanation=flip_explanation,
        analysis_delta=analysis_delta,
        run_ir_mismatch=run_ir_mismatch,
        left_mismatch=left_mismatch,
        right_mismatch=right_mismatch,
    )
    validate_explain_diff_packet(packet)
    return packet
