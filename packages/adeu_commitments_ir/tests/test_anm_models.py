from __future__ import annotations

import json
from pathlib import Path
from typing import get_args

import pytest
from adeu_commitments_ir import (
    CHECKER_FACT_BUNDLE_SCHEMA,
    D1_NORMALIZED_IR_SCHEMA,
    POLICY_EVALUATION_RESULT_SET_SCHEMA,
    POLICY_OBLIGATION_LEDGER_SCHEMA,
    PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA,
    CheckerFactBundle,
    D1NormalizedIR,
    PolicyEvaluationResultSet,
    PolicyObligationLedger,
    PredicateContractsBootstrap,
)
from adeu_commitments_ir.anm_models import FactType, ProvenanceMode
from pydantic import ValidationError


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47a" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def _fixture_path_v47b(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47b" / name


def _read_json_v47b(name: str) -> dict[str, object]:
    return json.loads(_fixture_path_v47b(name).read_text(encoding="utf-8"))


def test_v47a_models_accept_committed_reference_payloads() -> None:
    d1_ir = D1NormalizedIR.model_validate(_read_json("reference_d1_normalized_ir.json"))
    predicate_contracts = PredicateContractsBootstrap.model_validate(
        _read_json("reference_predicate_contracts_bootstrap.json")
    )
    fact_bundle = CheckerFactBundle.model_validate(_read_json("reference_fact_bundle.json"))
    result_set = PolicyEvaluationResultSet.model_validate(
        _read_json("reference_policy_evaluation_result_set.json")
    )
    ledger = PolicyObligationLedger.model_validate(
        _read_json("reference_policy_obligation_ledger.json")
    )

    assert d1_ir.schema == D1_NORMALIZED_IR_SCHEMA
    assert predicate_contracts.schema == PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA
    assert fact_bundle.schema == CHECKER_FACT_BUNDLE_SCHEMA
    assert result_set.schema == POLICY_EVALUATION_RESULT_SET_SCHEMA
    assert ledger.schema == POLICY_OBLIGATION_LEDGER_SCHEMA


def test_v47a_rejects_fact_bundle_with_verdict_semantics() -> None:
    with pytest.raises(ValidationError):
        CheckerFactBundle.model_validate(_read_json("reject_fact_bundle_with_verdict.json"))


def test_v47a_rejects_result_row_missing_required_outcome() -> None:
    with pytest.raises(ValidationError):
        PolicyEvaluationResultSet.model_validate(_read_json("reject_result_row_missing_outcome.json"))


def test_v47a_rejects_fabricated_clause_scope_blocker_ledger_row() -> None:
    with pytest.raises(ValidationError):
        PolicyObligationLedger.model_validate(
            _read_json("reject_clause_scope_blocker_fabricated_ledger_row.json")
        )


@pytest.mark.parametrize(
    ("d1_name", "contracts_name", "fact_bundle_name", "result_name", "ledger_name"),
    [
        (
            "standalone_reference_d1_normalized_ir.json",
            "standalone_reference_predicate_contracts_bootstrap.json",
            "standalone_fact_bundle.json",
            "standalone_reference_policy_evaluation_result_set.json",
            "standalone_reference_policy_obligation_ledger.json",
        ),
        (
            "companion_reference_d1_normalized_ir.json",
            "companion_reference_predicate_contracts_bootstrap.json",
            "companion_fact_bundle.json",
            "companion_reference_policy_evaluation_result_set.json",
            "companion_reference_policy_obligation_ledger.json",
        ),
    ],
)
def test_v47b_models_accept_committed_reference_payloads(
    d1_name: str,
    contracts_name: str,
    fact_bundle_name: str,
    result_name: str,
    ledger_name: str,
) -> None:
    d1_ir = D1NormalizedIR.model_validate(_read_json_v47b(d1_name))
    predicate_contracts = PredicateContractsBootstrap.model_validate(
        _read_json_v47b(contracts_name)
    )
    fact_bundle = CheckerFactBundle.model_validate(_read_json_v47b(fact_bundle_name))
    result_set = PolicyEvaluationResultSet.model_validate(_read_json_v47b(result_name))
    ledger = PolicyObligationLedger.model_validate(_read_json_v47b(ledger_name))

    assert d1_ir.schema == D1_NORMALIZED_IR_SCHEMA
    assert predicate_contracts.schema == PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA
    assert fact_bundle.schema == CHECKER_FACT_BUNDLE_SCHEMA
    assert result_set.schema == POLICY_EVALUATION_RESULT_SET_SCHEMA
    assert ledger.schema == POLICY_OBLIGATION_LEDGER_SCHEMA


def test_v47b_models_accept_zero_match_and_clause_scope_reference_payloads() -> None:
    result_set = PolicyEvaluationResultSet.model_validate(
        _read_json_v47b("standalone_zero_match_policy_evaluation_result_set.json")
    )
    ledger = PolicyObligationLedger.model_validate(
        _read_json_v47b("standalone_zero_match_policy_obligation_ledger.json")
    )
    reconciled_ledger = PolicyObligationLedger.model_validate(
        _read_json_v47b("standalone_zero_match_reconciled_policy_obligation_ledger.json")
    )
    blocker_result_set = PolicyEvaluationResultSet.model_validate(
        _read_json_v47b("clause_scope_blocker_reference_policy_evaluation_result_set.json")
    )
    blocker_ledger = PolicyObligationLedger.model_validate(
        _read_json_v47b("clause_scope_blocker_reference_policy_obligation_ledger.json")
    )

    assert result_set.schema == POLICY_EVALUATION_RESULT_SET_SCHEMA
    assert ledger.schema == POLICY_OBLIGATION_LEDGER_SCHEMA
    assert reconciled_ledger.schema == POLICY_OBLIGATION_LEDGER_SCHEMA
    assert blocker_result_set.schema == POLICY_EVALUATION_RESULT_SET_SCHEMA
    assert blocker_ledger.schema == POLICY_OBLIGATION_LEDGER_SCHEMA


def test_v47b_fact_type_and_provenance_mode_vocabularies_are_exact() -> None:
    assert get_args(FactType) == (
        "value_observation",
        "value_type_observation",
        "binding_observation",
        "carrier_read",
        "path_presence_observation",
        "path_cardinality_observation",
        "explicit_carriage_observation",
    )
    assert get_args(ProvenanceMode) == (
        "direct",
        "derived",
        "indirect",
        "absent",
        "inconclusive",
    )


def test_v47b_rejects_value_type_fact_with_non_string_values() -> None:
    with pytest.raises(ValidationError):
        CheckerFactBundle.model_validate(
            _read_json_v47b("reject_value_type_fact_non_string_values.json")
        )


def test_v47b_rejects_clause_scope_result_row_with_subject_ref() -> None:
    with pytest.raises(ValidationError):
        PolicyEvaluationResultSet.model_validate(
            _read_json_v47b("reject_clause_scope_row_with_subject_ref.json")
        )
