from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_SCHEMA,
    MODULE_CONFORMANCE_REPORT_SCHEMA,
    ExternalContributionAlignmentPacket,
    ModuleConformanceReport,
    canonicalize_external_contribution_alignment_packet_payload,
    canonicalize_module_conformance_report_payload,
    derive_v39a_module_conformance,
)
from pydantic import ValidationError


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _fixture_root() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "external_contribution_alignment"
        / "vnext_plus72"
    )


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _packet_payload() -> dict[str, object]:
    return _load_json(
        _fixture_root() / "external_contribution_alignment_packet_pr293_poetry_utility.json"
    )


def _report_payload() -> dict[str, object]:
    return _load_json(
        _fixture_root() / "module_conformance_report_pr293_poetry_utility.json"
    )


def test_reference_packet_fixture_validates_and_binds_localized_inputs() -> None:
    packet = ExternalContributionAlignmentPacket.model_validate(_packet_payload())

    assert packet.schema == EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_SCHEMA
    assert packet.reference_fixture_id == "pr293_poetry_utility"
    assert packet.structural_impact_class == "X1"
    assert packet.claimed_scope.declared_surface_kind == "internal_only_utility"
    assert packet.accepted_shipped_scope.declared_surface_kind == "internal_only_utility"
    assert packet.code_alignment_inputs.checks_run == []
    assert packet.localized_subject_inputs[0].input_role == "claimed_scope_snapshot"


def test_reference_report_fixture_matches_deterministic_derivation() -> None:
    canonical_packet = canonicalize_external_contribution_alignment_packet_payload(
        _packet_payload()
    )
    canonical_report = canonicalize_module_conformance_report_payload(_report_payload())
    derived = canonicalize_module_conformance_report_payload(
        derive_v39a_module_conformance(canonical_packet).model_dump(
            mode="json",
            exclude_none=True,
        )
    )

    assert canonical_report == derived
    assert canonical_report["schema"] == MODULE_CONFORMANCE_REPORT_SCHEMA
    assert canonical_report["meta_sequence_alignment_judgment"] == "not_aligned"
    assert canonical_report["code_alignment_judgment"] == "needs_review"
    assert canonical_report["overall_judgment"] == "needs_review"
    assert canonical_report["unresolved_followup_codes"] == ["record_checks_run"]


def test_packet_rejects_forged_localized_subject_hash() -> None:
    payload = _packet_payload()
    payload["localized_subject_inputs"][0]["sha256"] = "0" * 64  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match="localized_subject_inputs\\[claimed_scope\\]\\.sha256 must match repo file bytes",
    ):
        ExternalContributionAlignmentPacket.model_validate(payload)


def test_packet_rejects_external_accepted_scope_without_observed_external_surface() -> None:
    payload = _packet_payload()
    payload["accepted_shipped_scope"]["declared_surface_kind"] = (  # type: ignore[index]
        "externally_reachable_product_surface"
    )

    with pytest.raises(
        ValidationError,
        match="accepted_shipped_scope cannot claim externally reachable product surface",
    ):
        ExternalContributionAlignmentPacket.model_validate(payload)


def test_packet_rejects_observed_surface_refs_not_localized_in_metadata_snapshot() -> None:
    payload = _packet_payload()
    payload["observed_reachable_surfaces"][0]["surface_ref"] = (  # type: ignore[index]
        "apps/api/src/adeu_api/openai_backend_missing.py:888:build_codex_exec_backend"
    )

    with pytest.raises(
        ValidationError,
        match="observed_reachable_surfaces\\.surface_ref must be localized in metadata_snapshot",
    ):
        ExternalContributionAlignmentPacket.model_validate(payload)


def test_report_rejects_accepted_scope_refs_not_present_in_observed_surfaces() -> None:
    payload = _report_payload()
    payload["accepted_shipped_scope"]["surface_refs"] = [  # type: ignore[index]
        "adeu_api.public_surface.poetry_generation"
    ]

    with pytest.raises(
        ValidationError,
        match="accepted_shipped_scope\\.surface_refs must be observed reachable surfaces",
    ):
        ModuleConformanceReport.model_validate(payload)


def test_report_rejects_overlap_between_completed_and_unresolved_actions() -> None:
    payload = _report_payload()
    payload["completed_alignment_actions"] = [  # type: ignore[index]
        "record_checks_run"
    ]

    with pytest.raises(
        ValidationError,
        match="completed_alignment_actions and unresolved_followup_codes must remain disjoint",
    ):
        ModuleConformanceReport.model_validate(payload)
