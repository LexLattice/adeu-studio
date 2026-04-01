from __future__ import annotations

import json
from pathlib import Path

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
from pydantic import ValidationError


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47a" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


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
