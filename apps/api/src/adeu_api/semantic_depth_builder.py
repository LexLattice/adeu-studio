from __future__ import annotations

from typing import Any

from adeu_concepts import ConceptIR
from adeu_semantic_depth import (
    build_semantic_depth_report_from_concept_pair,
    validate_semantic_depth_report,
)


def as_semantic_depth_artifact_ref(semantic_depth_report_id: str) -> str:
    return f"artifact:semantic_depth:{semantic_depth_report_id}"


def build_semantic_depth_report_payload(
    *,
    left_ir: ConceptIR,
    right_ir: ConceptIR,
    input_artifact_refs: list[str] | None = None,
    diff_refs: list[str] | None = None,
    witness_refs: list[str] | None = None,
    semantics_diagnostics_ref: str | None = None,
    explain_diff_ref: str | None = None,
    coherence_summary: dict[str, Any] | None = None,
    nonsemantic_fields: dict[str, Any] | None = None,
) -> dict[str, Any]:
    packet = build_semantic_depth_report_from_concept_pair(
        left_ir=left_ir,
        right_ir=right_ir,
        input_artifact_refs=input_artifact_refs,
        diff_refs=diff_refs or (),
        witness_refs=witness_refs or (),
        semantics_diagnostics_ref=semantics_diagnostics_ref,
        explain_diff_ref=explain_diff_ref,
        coherence_summary=coherence_summary,
        nonsemantic_fields=nonsemantic_fields,
    )
    validate_semantic_depth_report(packet)
    return packet
