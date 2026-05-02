from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CORPUS_BOUNDARY_CONTRACT_SCHEMA,
    REPO_CROSS_CORPUS_AUTHORITY_GAP_REGISTER_SCHEMA,
    REPO_CROSS_CORPUS_EXCEPTION_REGISTER_SCHEMA,
    REPO_IMPORTED_SUBSTRATE_PROVENANCE_REGISTER_SCHEMA,
    RepoCorpusBoundaryContract,
    RepoCrossCorpusAuthorityGapRegister,
    RepoCrossCorpusExceptionRegister,
    RepoCrossCorpusGovernanceRequest,
    RepoCrossCorpusNonIngestionGuardrail,
    RepoCrossCorpusSourceIndex,
    RepoImportedSubstrateProvenanceRegister,
    derive_v81b_cross_corpus_boundary_bundle,
    validate_v81b_cross_corpus_boundary_bundle,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root(slice_name: str) -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / slice_name


def _load_fixture(slice_name: str, name: str) -> dict[str, Any]:
    return json.loads((_fixture_root(slice_name) / name).read_text(encoding="utf-8"))


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _v81a_source_index() -> RepoCrossCorpusSourceIndex:
    return RepoCrossCorpusSourceIndex.model_validate(
        _load_fixture("vnext_plus227", "repo_cross_corpus_source_index_v227_reference.json")
    )


def _v81a_request() -> RepoCrossCorpusGovernanceRequest:
    return RepoCrossCorpusGovernanceRequest.model_validate(
        _load_fixture(
            "vnext_plus227",
            "repo_cross_corpus_governance_request_v227_reference.json",
        )
    )


def _v81a_guardrail() -> RepoCrossCorpusNonIngestionGuardrail:
    return RepoCrossCorpusNonIngestionGuardrail.model_validate(
        _load_fixture(
            "vnext_plus227",
            "repo_cross_corpus_non_ingestion_guardrail_v227_reference.json",
        )
    )


def _boundary(
    name: str = "repo_corpus_boundary_contract_v228_reference.json",
) -> RepoCorpusBoundaryContract:
    return RepoCorpusBoundaryContract.model_validate(_load_fixture("vnext_plus228", name))


def _provenance(
    name: str = "repo_imported_substrate_provenance_register_v228_reference.json",
) -> RepoImportedSubstrateProvenanceRegister:
    return RepoImportedSubstrateProvenanceRegister.model_validate(
        _load_fixture("vnext_plus228", name)
    )


def _authority_gap(
    name: str = "repo_cross_corpus_authority_gap_register_v228_reference.json",
) -> RepoCrossCorpusAuthorityGapRegister:
    return RepoCrossCorpusAuthorityGapRegister.model_validate(
        _load_fixture("vnext_plus228", name)
    )


def _exception_register(
    name: str = "repo_cross_corpus_exception_register_v228_reference.json",
) -> RepoCrossCorpusExceptionRegister:
    return RepoCrossCorpusExceptionRegister.model_validate(
        _load_fixture("vnext_plus228", name)
    )


def _validate_reference_bundle_with(
    *,
    boundary: RepoCorpusBoundaryContract | None = None,
    provenance: RepoImportedSubstrateProvenanceRegister | None = None,
    authority_gap: RepoCrossCorpusAuthorityGapRegister | None = None,
    exception_register: RepoCrossCorpusExceptionRegister | None = None,
) -> None:
    validate_v81b_cross_corpus_boundary_bundle(
        cross_corpus_source_index=_v81a_source_index(),
        cross_corpus_governance_request=_v81a_request(),
        cross_corpus_non_ingestion_guardrail=_v81a_guardrail(),
        corpus_boundary_contract=boundary or _boundary(),
        imported_substrate_provenance_register=provenance or _provenance(),
        cross_corpus_authority_gap_register=authority_gap or _authority_gap(),
        cross_corpus_exception_register=exception_register or _exception_register(),
    )


def test_v228_reference_bundle_validates() -> None:
    boundary = _boundary()
    provenance = _provenance()
    authority_gap = _authority_gap()
    exception_register = _exception_register()

    assert boundary.schema == REPO_CORPUS_BOUNDARY_CONTRACT_SCHEMA
    assert provenance.schema == REPO_IMPORTED_SUBSTRATE_PROVENANCE_REGISTER_SCHEMA
    assert authority_gap.schema == REPO_CROSS_CORPUS_AUTHORITY_GAP_REGISTER_SCHEMA
    assert exception_register.schema == REPO_CROSS_CORPUS_EXCEPTION_REGISTER_SCHEMA
    assert {row.data_handling_posture for row in boundary.boundary_contract_rows} == {
        "no_data_handling_performed_by_v81"
    }
    assert {row.corpus_transfer_posture for row in boundary.boundary_contract_rows} == {
        "no_corpus_transfer_performed_by_v81"
    }
    assert {
        row.connector_activation_posture for row in boundary.boundary_contract_rows
    } == {"no_connector_activation_performed_by_v81"}
    assert {row.truth_status_forbidden for row in provenance.provenance_rows} == {
        "corpus_truth_not_claimed"
    }
    assert {row.benchmark_truth_posture for row in provenance.provenance_rows} == {
        "benchmark_truth_not_claimed"
    }
    assert {row.blocking_posture for row in exception_register.exception_rows} == {
        "blocking"
    }

    _validate_reference_bundle_with(
        boundary=boundary,
        provenance=provenance,
        authority_gap=authority_gap,
        exception_register=exception_register,
    )


def test_v228_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_corpus_boundary_contract.v1.json").validate(
        _load_fixture("vnext_plus228", "repo_corpus_boundary_contract_v228_reference.json")
    )
    _schema_validator("repo_imported_substrate_provenance_register.v1.json").validate(
        _load_fixture(
            "vnext_plus228",
            "repo_imported_substrate_provenance_register_v228_reference.json",
        )
    )
    _schema_validator("repo_cross_corpus_authority_gap_register.v1.json").validate(
        _load_fixture(
            "vnext_plus228",
            "repo_cross_corpus_authority_gap_register_v228_reference.json",
        )
    )
    _schema_validator("repo_cross_corpus_exception_register.v1.json").validate(
        _load_fixture("vnext_plus228", "repo_cross_corpus_exception_register_v228_reference.json")
    )


def test_v228_derivation_helper_matches_reference_fixtures() -> None:
    (
        _source_index,
        _request,
        _guardrail,
        boundary,
        provenance,
        authority_gap,
        exception_register,
    ) = derive_v81b_cross_corpus_boundary_bundle(repo_root=_repo_root())

    assert boundary.model_dump(mode="json") == _load_fixture(
        "vnext_plus228",
        "repo_corpus_boundary_contract_v228_reference.json",
    )
    assert provenance.model_dump(mode="json") == _load_fixture(
        "vnext_plus228",
        "repo_imported_substrate_provenance_register_v228_reference.json",
    )
    assert authority_gap.model_dump(mode="json") == _load_fixture(
        "vnext_plus228",
        "repo_cross_corpus_authority_gap_register_v228_reference.json",
    )
    assert exception_register.model_dump(mode="json") == _load_fixture(
        "vnext_plus228",
        "repo_cross_corpus_exception_register_v228_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_cross_corpus_governance_v228_reject_boundary_handles_data.json",
            RepoCorpusBoundaryContract,
            "must not handle corpus data",
        ),
        (
            "repo_cross_corpus_governance_v228_reject_boundary_transfers_data.json",
            RepoCorpusBoundaryContract,
            "must not transfer corpus data",
        ),
        (
            "repo_cross_corpus_governance_v228_reject_boundary_activates_connector.json",
            RepoCorpusBoundaryContract,
            "must not activate connectors",
        ),
        (
            "repo_cross_corpus_governance_v228_reject_provenance_claims_truth.json",
            RepoImportedSubstrateProvenanceRegister,
            "must not claim corpus truth",
        ),
        (
            "repo_cross_corpus_governance_v228_reject_benchmark_truth.json",
            RepoImportedSubstrateProvenanceRegister,
            "must not claim benchmark truth",
        ),
        (
            "repo_cross_corpus_governance_v228_reject_authority_gap_grants_authority.json",
            RepoCrossCorpusAuthorityGapRegister,
            "may not carry cross-corpus action authority",
        ),
        (
            "repo_cross_corpus_governance_v228_reject_exception_resolved_by_prose.json",
            RepoCrossCorpusExceptionRegister,
            "cannot be resolved by prose",
        ),
        (
            "repo_cross_corpus_governance_v228_reject_product_exception_warning_ready.json",
            RepoCrossCorpusExceptionRegister,
            "must remain blocked",
        ),
    ],
)
def test_v228_reject_fixtures_fail_model_validation(
    fixture_name: str,
    model_type: type[
        RepoCorpusBoundaryContract
        | RepoImportedSubstrateProvenanceRegister
        | RepoCrossCorpusAuthorityGapRegister
        | RepoCrossCorpusExceptionRegister
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus228", fixture_name))


def test_v228_bundle_rejects_unknown_v81a_request_ref() -> None:
    boundary = _boundary()
    boundary_row = boundary.boundary_contract_rows[0].model_copy(
        update={"request_refs": ["cross-corpus-governance:v81a:unknown"]}
    )
    boundary = boundary.model_copy(
        update={"boundary_contract_rows": [boundary_row, *boundary.boundary_contract_rows[1:]]}
    )

    with pytest.raises(ValueError, match="corpus boundary contract request refs must be known"):
        _validate_reference_bundle_with(boundary=boundary)


def test_v228_bundle_rejects_unknown_source_ref() -> None:
    boundary = _boundary()
    boundary_row = boundary.boundary_contract_rows[0].model_copy(
        update={"source_refs": ["docs/UNKNOWN_CROSS_CORPUS_SOURCE.md"]}
    )
    boundary = boundary.model_copy(
        update={"boundary_contract_rows": [boundary_row, *boundary.boundary_contract_rows[1:]]}
    )

    with pytest.raises(ValueError, match="corpus boundary contract source refs must be known"):
        _validate_reference_bundle_with(boundary=boundary)


def test_v228_bundle_rejects_unknown_provenance_boundary_ref() -> None:
    provenance = _provenance()
    provenance_row = provenance.provenance_rows[0].model_copy(
        update={"boundary_contract_refs": ["corpus-boundary:v81b:unknown"]}
    )
    provenance = provenance.model_copy(
        update={"provenance_rows": [provenance_row, *provenance.provenance_rows[1:]]}
    )

    with pytest.raises(ValueError, match="provenance boundary refs must be known"):
        _validate_reference_bundle_with(provenance=provenance)


def test_v228_bundle_rejects_exception_row_without_request_refs() -> None:
    exception_register = _exception_register()
    exception_row = exception_register.exception_rows[0].model_copy(
        update={"request_refs": []}
    )
    exception_register = exception_register.model_copy(update={"exception_rows": [exception_row]})

    with pytest.raises(ValueError, match="cross-corpus exception request refs must be non-empty"):
        _validate_reference_bundle_with(exception_register=exception_register)
