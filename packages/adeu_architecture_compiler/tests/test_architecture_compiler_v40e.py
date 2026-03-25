from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_compiler import (
    UX_DOMAIN_PACKET_TARGET_FAMILY,
    derive_v40e_ux_domain_packet,
    derive_v40e_ux_domain_packets,
)
from adeu_architecture_compiler.projection import _bundle_id, _manifest_id
from adeu_core_ir import UXDomainPacket, canonicalize_ux_domain_packet_payload
from adeu_ir.repo import repo_root
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root(*parts: str) -> Path:
    return _repo_root().joinpath("apps", "api", "fixtures", *parts)


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_arch_fixture(arc: str, name: str) -> dict[str, object]:
    return _load_json(_fixture_root("architecture", arc, name))


def _load_ux_fixture(name: str) -> dict[str, object]:
    return _load_json(_fixture_root("ux_governance", "vnext_plus61", name))


def test_v40e_ready_ux_domain_packet_reference_fixture_replays() -> None:
    emitted_fixture = _load_arch_fixture(
        "vnext_plus81",
        "ux_domain_packet_v81_ready_reference.json",
    )
    ready_bundle = _load_arch_fixture(
        "vnext_plus80",
        "adeu_architecture_projection_bundle_v80_ready_reference.json",
    )
    ready_manifest = _load_arch_fixture(
        "vnext_plus80",
        "adeu_architecture_projection_manifest_v80_ready_reference.json",
    )
    projection_id = ready_manifest["projection_units"][0]["projection_id"]  # type: ignore[index]

    emitted_packet = UXDomainPacket.model_validate(emitted_fixture)
    assert emitted_packet.schema == UX_DOMAIN_PACKET_TARGET_FAMILY

    derived_packet = derive_v40e_ux_domain_packet(
        semantic_ir_payload=_load_arch_fixture(
            "vnext_plus78",
            "adeu_architecture_semantic_ir_v78_ready_derivative.json",
        ),
        conformance_report_payload=_load_arch_fixture(
            "vnext_plus78",
            "adeu_architecture_conformance_report_v78_ready_reference.json",
        ),
        conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json",
        checkpoint_trace_payload=_load_arch_fixture(
            "vnext_plus79",
            "adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
        ),
        checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
        projection_bundle_payload=ready_bundle,
        projection_bundle_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_ready_reference.json",
        projection_manifest_payload=ready_manifest,
        projection_manifest_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_ready_reference.json",
        ux_domain_packet_payload=_load_ux_fixture(
            "ux_domain_packet_artifact_inspector_reference.json"
        ),
        ux_domain_packet_path="apps/api/fixtures/ux_governance/vnext_plus61/ux_domain_packet_artifact_inspector_reference.json",
        approved_profile_table_payload=_load_ux_fixture(
            "v36a_first_family_approved_profile_table.json"
        ),
        approved_profile_table_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json",
        same_context_glossary_payload=_load_ux_fixture(
            "v36a_same_context_reachability_glossary.json"
        ),
        same_context_glossary_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_same_context_reachability_glossary.json",
        projection_id=projection_id,  # type: ignore[arg-type]
        repository_root=_repo_root(),
    )
    derived_packets = derive_v40e_ux_domain_packets(
        semantic_ir_payload=_load_arch_fixture(
            "vnext_plus78",
            "adeu_architecture_semantic_ir_v78_ready_derivative.json",
        ),
        conformance_report_payload=_load_arch_fixture(
            "vnext_plus78",
            "adeu_architecture_conformance_report_v78_ready_reference.json",
        ),
        conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json",
        checkpoint_trace_payload=_load_arch_fixture(
            "vnext_plus79",
            "adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
        ),
        checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
        projection_bundle_payload=ready_bundle,
        projection_bundle_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_ready_reference.json",
        projection_manifest_payload=ready_manifest,
        projection_manifest_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_ready_reference.json",
        ux_domain_packet_payload=_load_ux_fixture(
            "ux_domain_packet_artifact_inspector_reference.json"
        ),
        ux_domain_packet_path="apps/api/fixtures/ux_governance/vnext_plus61/ux_domain_packet_artifact_inspector_reference.json",
        approved_profile_table_payload=_load_ux_fixture(
            "v36a_first_family_approved_profile_table.json"
        ),
        approved_profile_table_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json",
        same_context_glossary_payload=_load_ux_fixture(
            "v36a_same_context_reachability_glossary.json"
        ),
        same_context_glossary_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_same_context_reachability_glossary.json",
        repository_root=_repo_root(),
    )

    assert derived_packet == emitted_fixture
    assert derived_packets == {projection_id: emitted_fixture}
    assert canonicalize_ux_domain_packet_payload(emitted_fixture) == emitted_fixture


def test_v40e_blocked_projection_units_emit_no_ux_domain_packets() -> None:
    blocked_bundle = _load_arch_fixture(
        "vnext_plus80",
        "adeu_architecture_projection_bundle_v80_blocked_reference.json",
    )
    blocked_manifest = _load_arch_fixture(
        "vnext_plus80",
        "adeu_architecture_projection_manifest_v80_blocked_reference.json",
    )
    projection_id = blocked_manifest["projection_units"][0]["projection_id"]  # type: ignore[index]

    derived_packets = derive_v40e_ux_domain_packets(
        semantic_ir_payload=_load_arch_fixture(
            "vnext_plus77",
            "adeu_architecture_semantic_ir_v77_reference.json",
        ),
        conformance_report_payload=_load_arch_fixture(
            "vnext_plus78",
            "adeu_architecture_conformance_report_v78_blocked_reference.json",
        ),
        conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_blocked_reference.json",
        checkpoint_trace_payload=_load_arch_fixture(
            "vnext_plus79",
            "adeu_architecture_checkpoint_trace_v79_human_needed_reference.json",
        ),
        checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_human_needed_reference.json",
        projection_bundle_payload=blocked_bundle,
        projection_bundle_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_blocked_reference.json",
        projection_manifest_payload=blocked_manifest,
        projection_manifest_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_blocked_reference.json",
        ux_domain_packet_payload=_load_ux_fixture(
            "ux_domain_packet_artifact_inspector_reference.json"
        ),
        ux_domain_packet_path="apps/api/fixtures/ux_governance/vnext_plus61/ux_domain_packet_artifact_inspector_reference.json",
        approved_profile_table_payload=_load_ux_fixture(
            "v36a_first_family_approved_profile_table.json"
        ),
        approved_profile_table_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json",
        same_context_glossary_payload=_load_ux_fixture(
            "v36a_same_context_reachability_glossary.json"
        ),
        same_context_glossary_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_same_context_reachability_glossary.json",
        repository_root=_repo_root(),
    )

    assert derived_packets == {}

    with pytest.raises(
        ValueError,
        match="V40-E may not emit ux_domain_packet for blocked projection units",
    ):
        derive_v40e_ux_domain_packet(
            semantic_ir_payload=_load_arch_fixture(
                "vnext_plus77",
                "adeu_architecture_semantic_ir_v77_reference.json",
            ),
            conformance_report_payload=_load_arch_fixture(
                "vnext_plus78",
                "adeu_architecture_conformance_report_v78_blocked_reference.json",
            ),
            conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_blocked_reference.json",
            checkpoint_trace_payload=_load_arch_fixture(
                "vnext_plus79",
                "adeu_architecture_checkpoint_trace_v79_human_needed_reference.json",
            ),
            checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_human_needed_reference.json",
            projection_bundle_payload=blocked_bundle,
            projection_bundle_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_blocked_reference.json",
            projection_manifest_payload=blocked_manifest,
            projection_manifest_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_blocked_reference.json",
            ux_domain_packet_payload=_load_ux_fixture(
                "ux_domain_packet_artifact_inspector_reference.json"
            ),
            ux_domain_packet_path="apps/api/fixtures/ux_governance/vnext_plus61/ux_domain_packet_artifact_inspector_reference.json",
            approved_profile_table_payload=_load_ux_fixture(
                "v36a_first_family_approved_profile_table.json"
            ),
            approved_profile_table_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json",
            same_context_glossary_payload=_load_ux_fixture(
                "v36a_same_context_reachability_glossary.json"
            ),
            same_context_glossary_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_same_context_reachability_glossary.json",
            projection_id=projection_id,  # type: ignore[arg-type]
            repository_root=_repo_root(),
        )


def test_v40e_requires_exact_one_to_one_projection_binding() -> None:
    with pytest.raises(
        ValueError,
        match="projection_id must resolve to exactly one released projection unit",
    ):
        derive_v40e_ux_domain_packet(
            semantic_ir_payload=_load_arch_fixture(
                "vnext_plus78",
                "adeu_architecture_semantic_ir_v78_ready_derivative.json",
            ),
            conformance_report_payload=_load_arch_fixture(
                "vnext_plus78",
                "adeu_architecture_conformance_report_v78_ready_reference.json",
            ),
            conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json",
            checkpoint_trace_payload=_load_arch_fixture(
                "vnext_plus79",
                "adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
            ),
            checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
            projection_bundle_payload=_load_arch_fixture(
                "vnext_plus80",
                "adeu_architecture_projection_bundle_v80_ready_reference.json",
            ),
            projection_bundle_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_ready_reference.json",
            projection_manifest_payload=_load_arch_fixture(
                "vnext_plus80",
                "adeu_architecture_projection_manifest_v80_ready_reference.json",
            ),
            projection_manifest_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_ready_reference.json",
            ux_domain_packet_payload=_load_ux_fixture(
                "ux_domain_packet_artifact_inspector_reference.json"
            ),
            ux_domain_packet_path="apps/api/fixtures/ux_governance/vnext_plus61/ux_domain_packet_artifact_inspector_reference.json",
            approved_profile_table_payload=_load_ux_fixture(
                "v36a_first_family_approved_profile_table.json"
            ),
            approved_profile_table_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json",
            same_context_glossary_payload=_load_ux_fixture(
                "v36a_same_context_reachability_glossary.json"
            ),
            same_context_glossary_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_same_context_reachability_glossary.json",
            projection_id="missing_projection_id",
            repository_root=_repo_root(),
        )


def test_v40e_rejects_ux_morph_ir_field_smuggling() -> None:
    payload = deepcopy(_load_ux_fixture("ux_domain_packet_artifact_inspector_reference.json"))
    payload["surface_compilation_units"] = ["surface_root"]

    with pytest.raises(ValidationError):
        derive_v40e_ux_domain_packets(
            semantic_ir_payload=_load_arch_fixture(
                "vnext_plus78",
                "adeu_architecture_semantic_ir_v78_ready_derivative.json",
            ),
            conformance_report_payload=_load_arch_fixture(
                "vnext_plus78",
                "adeu_architecture_conformance_report_v78_ready_reference.json",
            ),
            conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json",
            checkpoint_trace_payload=_load_arch_fixture(
                "vnext_plus79",
                "adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
            ),
            checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
            projection_bundle_payload=_load_arch_fixture(
                "vnext_plus80",
                "adeu_architecture_projection_bundle_v80_ready_reference.json",
            ),
            projection_bundle_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_ready_reference.json",
            projection_manifest_payload=_load_arch_fixture(
                "vnext_plus80",
                "adeu_architecture_projection_manifest_v80_ready_reference.json",
            ),
            projection_manifest_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_ready_reference.json",
            ux_domain_packet_payload=payload,
            ux_domain_packet_path="apps/api/fixtures/ux_governance/vnext_plus61/ux_domain_packet_artifact_inspector_reference.json",
            approved_profile_table_payload=_load_ux_fixture(
                "v36a_first_family_approved_profile_table.json"
            ),
            approved_profile_table_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json",
            same_context_glossary_payload=_load_ux_fixture(
                "v36a_same_context_reachability_glossary.json"
            ),
            same_context_glossary_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_same_context_reachability_glossary.json",
            repository_root=_repo_root(),
        )


def test_v40e_rejects_governance_profile_drift() -> None:
    profile_table = deepcopy(_load_ux_fixture("v36a_first_family_approved_profile_table.json"))
    profile_table["profiles"] = [
        profile
        for profile in profile_table["profiles"]  # type: ignore[index]
        if profile["profile_id"] == "artifact_inspector_alternate"
    ]

    with pytest.raises(ValidationError, match="profiles must contain exactly two entries"):
        derive_v40e_ux_domain_packets(
            semantic_ir_payload=_load_arch_fixture(
                "vnext_plus78",
                "adeu_architecture_semantic_ir_v78_ready_derivative.json",
            ),
            conformance_report_payload=_load_arch_fixture(
                "vnext_plus78",
                "adeu_architecture_conformance_report_v78_ready_reference.json",
            ),
            conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json",
            checkpoint_trace_payload=_load_arch_fixture(
                "vnext_plus79",
                "adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
            ),
            checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
            projection_bundle_payload=_load_arch_fixture(
                "vnext_plus80",
                "adeu_architecture_projection_bundle_v80_ready_reference.json",
            ),
            projection_bundle_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_ready_reference.json",
            projection_manifest_payload=_load_arch_fixture(
                "vnext_plus80",
                "adeu_architecture_projection_manifest_v80_ready_reference.json",
            ),
            projection_manifest_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_ready_reference.json",
            ux_domain_packet_payload=_load_ux_fixture(
                "ux_domain_packet_artifact_inspector_reference.json"
            ),
            ux_domain_packet_path="apps/api/fixtures/ux_governance/vnext_plus61/ux_domain_packet_artifact_inspector_reference.json",
            approved_profile_table_payload=profile_table,
            approved_profile_table_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json",
            same_context_glossary_payload=_load_ux_fixture(
                "v36a_same_context_reachability_glossary.json"
            ),
            same_context_glossary_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_same_context_reachability_glossary.json",
            repository_root=None,
        )


def test_v40e_rejects_forged_ready_projection_without_repository_root() -> None:
    blocked_bundle = deepcopy(
        _load_arch_fixture(
            "vnext_plus80",
            "adeu_architecture_projection_bundle_v80_blocked_reference.json",
        )
    )
    blocked_manifest = deepcopy(
        _load_arch_fixture(
            "vnext_plus80",
            "adeu_architecture_projection_manifest_v80_blocked_reference.json",
        )
    )
    blocked_bundle["projection_units"][0]["readiness"] = "ready"  # type: ignore[index]
    blocked_bundle["projection_units"][0]["blocked_by_ambiguity_refs"] = []  # type: ignore[index]
    blocked_bundle["projection_units"][0]["output_artifact_refs"] = [  # type: ignore[index]
        "apps/api/fixtures/architecture/vnext_plus80/adeu_core_ir_v80_ready_reference.json"
    ]
    blocked_bundle["bundle_id"] = _bundle_id(
        architecture_id=blocked_bundle["architecture_id"],  # type: ignore[arg-type]
        semantic_hash=blocked_bundle["semantic_hash"],  # type: ignore[arg-type]
        conformance_report_ref=blocked_bundle["conformance_report_ref"],  # type: ignore[arg-type]
        checkpoint_trace_ref=blocked_bundle["checkpoint_trace_ref"],  # type: ignore[arg-type]
        target_family=blocked_bundle["target_family"],  # type: ignore[arg-type]
        compiler=blocked_bundle["compiler"],  # type: ignore[arg-type]
        compiler_version=blocked_bundle["compiler_version"],  # type: ignore[arg-type]
        projection_units=blocked_bundle["projection_units"],  # type: ignore[arg-type]
    )

    blocked_manifest["projection_units"][0]["readiness"] = "ready"  # type: ignore[index]
    blocked_manifest["projection_units"][0]["blocked_by_ambiguity_refs"] = []  # type: ignore[index]
    blocked_manifest["projection_units"][0]["output_artifact_refs"] = [  # type: ignore[index]
        "apps/api/fixtures/architecture/vnext_plus80/adeu_core_ir_v80_ready_reference.json"
    ]
    blocked_manifest["touched_artifact_refs"] = [
        "apps/api/fixtures/architecture/vnext_plus80/adeu_core_ir_v80_ready_reference.json"
    ]
    blocked_manifest["blocked_by_ambiguity_refs"] = []
    blocked_manifest["manifest_id"] = _manifest_id(
        architecture_id=blocked_manifest["architecture_id"],  # type: ignore[arg-type]
        semantic_hash=blocked_manifest["semantic_hash"],  # type: ignore[arg-type]
        conformance_report_ref=blocked_manifest["conformance_report_ref"],  # type: ignore[arg-type]
        checkpoint_trace_ref=blocked_manifest["checkpoint_trace_ref"],  # type: ignore[arg-type]
        source_root_refs=blocked_manifest["source_root_refs"],  # type: ignore[arg-type]
        target_family=blocked_manifest["target_family"],  # type: ignore[arg-type]
        compiler_entrypoint=blocked_manifest["compiler_entrypoint"],  # type: ignore[arg-type]
        compiler_version=blocked_manifest["compiler_version"],  # type: ignore[arg-type]
        projection_units=blocked_manifest["projection_units"],  # type: ignore[arg-type]
        touched_artifact_refs=blocked_manifest["touched_artifact_refs"],  # type: ignore[arg-type]
        blocked_by_ambiguity_refs=blocked_manifest["blocked_by_ambiguity_refs"],  # type: ignore[arg-type]
    )

    with pytest.raises(
        ValueError,
        match="projection_unit blocked_by_ambiguity_refs must match active unit-local blockers",
    ):
        derive_v40e_ux_domain_packets(
            semantic_ir_payload=_load_arch_fixture(
                "vnext_plus77",
                "adeu_architecture_semantic_ir_v77_reference.json",
            ),
            conformance_report_payload=_load_arch_fixture(
                "vnext_plus78",
                "adeu_architecture_conformance_report_v78_blocked_reference.json",
            ),
            conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_blocked_reference.json",
            checkpoint_trace_payload=_load_arch_fixture(
                "vnext_plus79",
                "adeu_architecture_checkpoint_trace_v79_human_needed_reference.json",
            ),
            checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_human_needed_reference.json",
            projection_bundle_payload=blocked_bundle,
            projection_bundle_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_blocked_reference.json",
            projection_manifest_payload=blocked_manifest,
            projection_manifest_path="apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_blocked_reference.json",
            ux_domain_packet_payload=_load_ux_fixture(
                "ux_domain_packet_artifact_inspector_reference.json"
            ),
            ux_domain_packet_path="apps/api/fixtures/ux_governance/vnext_plus61/ux_domain_packet_artifact_inspector_reference.json",
            approved_profile_table_payload=_load_ux_fixture(
                "v36a_first_family_approved_profile_table.json"
            ),
            approved_profile_table_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json",
            same_context_glossary_payload=_load_ux_fixture(
                "v36a_same_context_reachability_glossary.json"
            ),
            same_context_glossary_path="apps/api/fixtures/ux_governance/vnext_plus61/v36a_same_context_reachability_glossary.json",
            repository_root=None,
        )
