from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    SYNTHETIC_PRESSURE_MISMATCH_CONFORMANCE_REPORT_SCHEMA,
    SYNTHETIC_PRESSURE_MISMATCH_OBSERVATION_PACKET_SCHEMA,
    SyntheticPressureMismatchConformanceReport,
    SyntheticPressureMismatchObservationPacket,
    canonicalize_synthetic_pressure_mismatch_conformance_report_payload,
    canonicalize_synthetic_pressure_mismatch_observation_packet_payload,
    derive_v39c_conformance_report,
    derive_v39c_observation_packet,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixtures_root() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "synthetic_pressure_mismatch"
        / "vnext_plus74"
    )


def _load_json(name: str) -> dict[str, object]:
    return json.loads((_fixtures_root() / name).read_text(encoding="utf-8"))


def _load_exported_schema(name: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / name
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v39c_positive_observation_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_observation_packet_v74_positive.json")
    packet = SyntheticPressureMismatchObservationPacket.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert packet.schema == SYNTHETIC_PRESSURE_MISMATCH_OBSERVATION_PACKET_SCHEMA
    assert packet.subject_kind == "function_or_method"
    assert len(packet.findings) == 1
    assert packet.findings[0].rule_id == "state_model_impossible_null_check"

    derived = derive_v39c_observation_packet(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
        "subject_function_impossible_null_guard_v74.json",
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_observation_packet_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39c_no_finding_observation_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_observation_packet_v74_no_findings.json")
    packet = SyntheticPressureMismatchObservationPacket.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert packet.schema == SYNTHETIC_PRESSURE_MISMATCH_OBSERVATION_PACKET_SCHEMA
    assert packet.findings == []

    derived = derive_v39c_observation_packet(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
        "subject_function_clean_no_findings_v74.json",
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_observation_packet_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39c_reference_report_fixture_validates_and_replays() -> None:
    positive_packet = _load_json("synthetic_pressure_mismatch_observation_packet_v74_positive.json")
    no_finding_packet = _load_json(
        "synthetic_pressure_mismatch_observation_packet_v74_no_findings.json"
    )
    fixture = _load_json("synthetic_pressure_mismatch_conformance_report_v74_reference.json")
    report = SyntheticPressureMismatchConformanceReport.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert report.schema == SYNTHETIC_PRESSURE_MISMATCH_CONFORMANCE_REPORT_SCHEMA
    assert report.observation_count == 2
    assert report.finding_count == 1
    assert report.overall_pressure_mismatch_posture == "safe_autofix_candidates_present"

    derived = derive_v39c_conformance_report(
        [positive_packet, no_finding_packet],
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_conformance_report_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39c_no_finding_report_fixture_validates_and_replays() -> None:
    no_finding_packet = _load_json(
        "synthetic_pressure_mismatch_observation_packet_v74_no_findings.json"
    )
    fixture = _load_json("synthetic_pressure_mismatch_conformance_report_v74_no_findings.json")
    report = SyntheticPressureMismatchConformanceReport.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert report.finding_count == 0
    assert report.overall_pressure_mismatch_posture == "no_findings"

    derived = derive_v39c_conformance_report(
        [no_finding_packet],
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_conformance_report_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39c_fails_closed_for_registry_applicable_but_detector_unsupported_subject() -> None:
    with pytest.raises(
        ValueError,
        match=(
            "V39-C deterministic detector for released rule_id "
            "state_model_impossible_null_check does not support subject_kind code_span"
        ),
    ):
        derive_v39c_observation_packet(
            "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
            "subject_code_span_impossible_null_guard_v74.json",
            repository_root=_repo_root(),
        )


def test_v39c_packet_rejects_shadow_registry_metadata_drift() -> None:
    payload = _load_json("synthetic_pressure_mismatch_observation_packet_v74_positive.json")
    payload["findings"][0]["signal_kind"] = "shape_regularity_drift"  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match="findings\\[\\]\\.signal_kind must match the referenced registry rule",
    ):
        SyntheticPressureMismatchObservationPacket.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39c_packet_rejects_duplicate_finding_identity() -> None:
    payload = _load_json("synthetic_pressure_mismatch_observation_packet_v74_positive.json")
    payload["findings"].append(payload["findings"][0])  # type: ignore[index]

    with pytest.raises(ValidationError, match="findings.identity must not contain duplicates"):
        SyntheticPressureMismatchObservationPacket.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39c_requested_unsupported_rule_fails_closed() -> None:
    request = _load_json("synthetic_pressure_mismatch_unsupported_execution_request_v74.json")

    with pytest.raises(
        ValueError,
        match="requested_rule_ids may execute deterministic_local rules only in V39-C",
    ):
        derive_v39c_observation_packet(
            request["subject_ref"],  # type: ignore[arg-type]
            requested_rule_ids=request["requested_rule_ids"],  # type: ignore[arg-type]
            repository_root=_repo_root(),
        )


def test_v39c_report_rejects_non_literal_posture() -> None:
    payload = _load_json("synthetic_pressure_mismatch_conformance_report_v74_no_findings.json")
    payload["overall_pressure_mismatch_posture"] = 1

    with pytest.raises(ValidationError):
        SyntheticPressureMismatchConformanceReport.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39c_report_rejects_finding_refs_outside_aggregated_packet_set() -> None:
    payload = _load_json("synthetic_pressure_mismatch_conformance_report_v74_reference.json")
    payload["safe_autofix_candidates"][0]["observation_packet_id"] = "unknown_packet"  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match=(
            "safe_autofix_candidates\\.observation_packet_id must belong to "
            "aggregated_observation_packet_ids"
        ),
    ):
        SyntheticPressureMismatchConformanceReport.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39c_multi_packet_report_id_is_derived_from_packet_set() -> None:
    positive_packet = _load_json("synthetic_pressure_mismatch_observation_packet_v74_positive.json")
    no_finding_packet = _load_json(
        "synthetic_pressure_mismatch_observation_packet_v74_no_findings.json"
    )

    derived = derive_v39c_conformance_report(
        [positive_packet, no_finding_packet],
        repository_root=_repo_root(),
    )
    derived_reversed = derive_v39c_conformance_report(
        [no_finding_packet, positive_packet],
        repository_root=_repo_root(),
    )

    assert derived.report_id.startswith("v39c_v74_report_")
    assert derived.report_id != "v39c_v74_conformance_reference"
    assert derived.report_id == derived_reversed.report_id


def test_v39c_exported_schemas_validate_reference_fixtures() -> None:
    packet_validator = _load_exported_schema(
        "synthetic_pressure_mismatch_observation_packet.v1.json"
    )
    report_validator = _load_exported_schema(
        "synthetic_pressure_mismatch_conformance_report.v1.json"
    )

    assert packet_validator.is_valid(
        _load_json("synthetic_pressure_mismatch_observation_packet_v74_positive.json")
    )
    assert packet_validator.is_valid(
        _load_json("synthetic_pressure_mismatch_observation_packet_v74_no_findings.json")
    )
    assert report_validator.is_valid(
        _load_json("synthetic_pressure_mismatch_conformance_report_v74_reference.json")
    )
    assert report_validator.is_valid(
        _load_json("synthetic_pressure_mismatch_conformance_report_v74_no_findings.json")
    )

    invalid_report = _load_json(
        "synthetic_pressure_mismatch_conformance_report_v74_no_findings.json"
    )
    invalid_report["overall_pressure_mismatch_posture"] = "weighted_score_5"
    assert not report_validator.is_valid(invalid_report)
