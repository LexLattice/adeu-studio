from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .integrity_cycle_policy import AdeuIntegrityCyclePolicy
from .integrity_cycle_policy_extended import AdeuIntegrityCyclePolicyExtended
from .integrity_dangling_reference import AdeuIntegrityDanglingReference
from .integrity_deontic_conflict import AdeuIntegrityDeonticConflict
from .integrity_deontic_conflict_extended import AdeuIntegrityDeonticConflictExtended
from .integrity_reference_integrity_extended import (
    AdeuIntegrityReferenceIntegrityExtended,
)
from .lane_report import AdeuLaneReport
from .models import AdeuCoreIR
from .normative_advice_packet import AdeuNormativeAdvicePacket
from .projection_alignment import AdeuProjectionAlignment
from .projection_alignment_fidelity import (
    AdeuProjectionAlignmentFidelity,
    AdeuProjectionAlignmentFidelityInput,
)
from .read_surface_payload import AdeuReadSurfacePayload
from .semantics_v4_candidate_packet import AdeuSemanticsV4CandidatePacket
from .trust_invariant_packet import AdeuTrustInvariantPacket


def _write_schema(path: Path, schema: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    core_ir_schema = AdeuCoreIR.model_json_schema(by_alias=True)
    lane_report_schema = AdeuLaneReport.model_json_schema(by_alias=True)
    integrity_cycle_policy_schema = AdeuIntegrityCyclePolicy.model_json_schema(by_alias=True)
    integrity_cycle_policy_extended_schema = AdeuIntegrityCyclePolicyExtended.model_json_schema(
        by_alias=True
    )
    integrity_deontic_conflict_schema = AdeuIntegrityDeonticConflict.model_json_schema(
        by_alias=True
    )
    integrity_deontic_conflict_extended_schema = (
        AdeuIntegrityDeonticConflictExtended.model_json_schema(by_alias=True)
    )
    integrity_dangling_reference_schema = AdeuIntegrityDanglingReference.model_json_schema(
        by_alias=True
    )
    integrity_reference_integrity_extended_schema = (
        AdeuIntegrityReferenceIntegrityExtended.model_json_schema(by_alias=True)
    )
    projection_alignment_schema = AdeuProjectionAlignment.model_json_schema(by_alias=True)
    read_surface_payload_schema = AdeuReadSurfacePayload.model_json_schema(by_alias=True)
    normative_advice_packet_schema = AdeuNormativeAdvicePacket.model_json_schema(by_alias=True)
    trust_invariant_packet_schema = AdeuTrustInvariantPacket.model_json_schema(by_alias=True)
    semantics_v4_candidate_packet_schema = AdeuSemanticsV4CandidatePacket.model_json_schema(
        by_alias=True
    )
    projection_alignment_fidelity_input_schema = (
        AdeuProjectionAlignmentFidelityInput.model_json_schema(by_alias=True)
    )
    projection_alignment_fidelity_schema = AdeuProjectionAlignmentFidelity.model_json_schema(
        by_alias=True
    )

    authoritative_path = root / "packages" / "adeu_core_ir" / "schema" / "adeu_core_ir.v0_1.json"
    _write_schema(authoritative_path, core_ir_schema)

    lane_authoritative_path = (
        root / "packages" / "adeu_core_ir" / "schema" / "adeu_lane_report.v0_1.json"
    )
    _write_schema(lane_authoritative_path, lane_report_schema)

    integrity_cycle_policy_authoritative_path = (
        root / "packages" / "adeu_core_ir" / "schema" / "adeu_integrity_cycle_policy.v0_1.json"
    )
    _write_schema(
        integrity_cycle_policy_authoritative_path,
        integrity_cycle_policy_schema,
    )

    integrity_cycle_policy_extended_authoritative_path = (
        root
        / "packages"
        / "adeu_core_ir"
        / "schema"
        / "adeu_integrity_cycle_policy_extended.v0_1.json"
    )
    _write_schema(
        integrity_cycle_policy_extended_authoritative_path,
        integrity_cycle_policy_extended_schema,
    )

    integrity_deontic_conflict_authoritative_path = (
        root / "packages" / "adeu_core_ir" / "schema" / "adeu_integrity_deontic_conflict.v0_1.json"
    )
    _write_schema(
        integrity_deontic_conflict_authoritative_path,
        integrity_deontic_conflict_schema,
    )

    integrity_deontic_conflict_extended_authoritative_path = (
        root
        / "packages"
        / "adeu_core_ir"
        / "schema"
        / "adeu_integrity_deontic_conflict_extended.v0_1.json"
    )
    _write_schema(
        integrity_deontic_conflict_extended_authoritative_path,
        integrity_deontic_conflict_extended_schema,
    )

    integrity_dangling_reference_authoritative_path = (
        root
        / "packages"
        / "adeu_core_ir"
        / "schema"
        / "adeu_integrity_dangling_reference.v0_1.json"
    )
    _write_schema(
        integrity_dangling_reference_authoritative_path,
        integrity_dangling_reference_schema,
    )

    integrity_reference_integrity_extended_authoritative_path = (
        root
        / "packages"
        / "adeu_core_ir"
        / "schema"
        / "adeu_integrity_reference_integrity_extended.v0_1.json"
    )
    _write_schema(
        integrity_reference_integrity_extended_authoritative_path,
        integrity_reference_integrity_extended_schema,
    )

    projection_alignment_authoritative_path = (
        root / "packages" / "adeu_core_ir" / "schema" / "adeu_projection_alignment.v0_1.json"
    )
    _write_schema(projection_alignment_authoritative_path, projection_alignment_schema)

    read_surface_payload_authoritative_path = (
        root / "packages" / "adeu_core_ir" / "schema" / "adeu_read_surface_payload.v0_1.json"
    )
    _write_schema(read_surface_payload_authoritative_path, read_surface_payload_schema)

    normative_advice_packet_authoritative_path = (
        root / "packages" / "adeu_core_ir" / "schema" / "adeu_normative_advice_packet.v0_1.json"
    )
    _write_schema(
        normative_advice_packet_authoritative_path,
        normative_advice_packet_schema,
    )

    trust_invariant_packet_authoritative_path = (
        root / "packages" / "adeu_core_ir" / "schema" / "adeu_trust_invariant_packet.v0_1.json"
    )
    _write_schema(
        trust_invariant_packet_authoritative_path,
        trust_invariant_packet_schema,
    )

    semantics_v4_candidate_packet_authoritative_path = (
        root
        / "packages"
        / "adeu_core_ir"
        / "schema"
        / "adeu_semantics_v4_candidate_packet.v0_1.json"
    )
    _write_schema(
        semantics_v4_candidate_packet_authoritative_path,
        semantics_v4_candidate_packet_schema,
    )

    projection_alignment_fidelity_input_authoritative_path = (
        root
        / "packages"
        / "adeu_core_ir"
        / "schema"
        / "adeu_projection_alignment_fidelity_input.v0_1.json"
    )
    _write_schema(
        projection_alignment_fidelity_input_authoritative_path,
        projection_alignment_fidelity_input_schema,
    )

    projection_alignment_fidelity_authoritative_path = (
        root
        / "packages"
        / "adeu_core_ir"
        / "schema"
        / "adeu_projection_alignment_fidelity.v0_1.json"
    )
    _write_schema(
        projection_alignment_fidelity_authoritative_path,
        projection_alignment_fidelity_schema,
    )

    mirror_path = root / "spec" / "adeu_core_ir.schema.json"
    _write_schema(mirror_path, core_ir_schema)

    lane_mirror_path = root / "spec" / "adeu_lane_report.schema.json"
    _write_schema(lane_mirror_path, lane_report_schema)

    integrity_cycle_policy_mirror_path = root / "spec" / "adeu_integrity_cycle_policy.schema.json"
    _write_schema(
        integrity_cycle_policy_mirror_path,
        integrity_cycle_policy_schema,
    )

    integrity_cycle_policy_extended_mirror_path = (
        root / "spec" / "adeu_integrity_cycle_policy_extended.schema.json"
    )
    _write_schema(
        integrity_cycle_policy_extended_mirror_path,
        integrity_cycle_policy_extended_schema,
    )

    integrity_deontic_conflict_mirror_path = (
        root / "spec" / "adeu_integrity_deontic_conflict.schema.json"
    )
    _write_schema(
        integrity_deontic_conflict_mirror_path,
        integrity_deontic_conflict_schema,
    )

    integrity_deontic_conflict_extended_mirror_path = (
        root / "spec" / "adeu_integrity_deontic_conflict_extended.schema.json"
    )
    _write_schema(
        integrity_deontic_conflict_extended_mirror_path,
        integrity_deontic_conflict_extended_schema,
    )

    integrity_dangling_reference_mirror_path = (
        root / "spec" / "adeu_integrity_dangling_reference.schema.json"
    )
    _write_schema(
        integrity_dangling_reference_mirror_path,
        integrity_dangling_reference_schema,
    )

    integrity_reference_integrity_extended_mirror_path = (
        root / "spec" / "adeu_integrity_reference_integrity_extended.schema.json"
    )
    _write_schema(
        integrity_reference_integrity_extended_mirror_path,
        integrity_reference_integrity_extended_schema,
    )

    projection_alignment_mirror_path = root / "spec" / "adeu_projection_alignment.schema.json"
    _write_schema(projection_alignment_mirror_path, projection_alignment_schema)

    read_surface_payload_mirror_path = root / "spec" / "adeu_read_surface_payload.schema.json"
    _write_schema(read_surface_payload_mirror_path, read_surface_payload_schema)

    normative_advice_packet_mirror_path = root / "spec" / "adeu_normative_advice_packet.schema.json"
    _write_schema(
        normative_advice_packet_mirror_path,
        normative_advice_packet_schema,
    )

    trust_invariant_packet_mirror_path = root / "spec" / "adeu_trust_invariant_packet.schema.json"
    _write_schema(
        trust_invariant_packet_mirror_path,
        trust_invariant_packet_schema,
    )

    semantics_v4_candidate_packet_mirror_path = (
        root / "spec" / "adeu_semantics_v4_candidate_packet.schema.json"
    )
    _write_schema(
        semantics_v4_candidate_packet_mirror_path,
        semantics_v4_candidate_packet_schema,
    )

    projection_alignment_fidelity_input_mirror_path = (
        root / "spec" / "adeu_projection_alignment_fidelity_input.schema.json"
    )
    _write_schema(
        projection_alignment_fidelity_input_mirror_path,
        projection_alignment_fidelity_input_schema,
    )

    projection_alignment_fidelity_mirror_path = (
        root / "spec" / "adeu_projection_alignment_fidelity.schema.json"
    )
    _write_schema(
        projection_alignment_fidelity_mirror_path,
        projection_alignment_fidelity_schema,
    )


if __name__ == "__main__":
    main()
