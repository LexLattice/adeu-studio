from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_commitments_ir import CheckerFactBundle, PolicyEvaluationResultSet, PolicyObligationLedger
from adeu_semantic_source import (
    AnmCompileError,
    build_v47a_reference_chain,
    compile_authoritative_normative_markdown,
    default_bootstrap_predicate_contracts,
    evaluate_authoritative_normative_markdown,
    project_policy_obligation_ledger,
)


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47a" / name


def _fixture_path_v47b(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47b" / name


def _read_text(name: str) -> str:
    return _fixture_path(name).read_text(encoding="utf-8")


def _read_text_v47b(name: str) -> str:
    return _fixture_path_v47b(name).read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_commitments_fixture(name: str) -> dict[str, object]:
    path = (
        Path(__file__).resolve().parents[2]
        / "adeu_commitments_ir"
        / "tests"
        / "fixtures"
        / "v47a"
        / name
    )
    return _read_json(path)


def _read_commitments_fixture_v47b(name: str) -> dict[str, object]:
    path = (
        Path(__file__).resolve().parents[2]
        / "adeu_commitments_ir"
        / "tests"
        / "fixtures"
        / "v47b"
        / name
    )
    return _read_json(path)


def test_v47a_reference_chain_replays_deterministically() -> None:
    source_text = _read_text("reference_policy.adeu.md")
    fact_bundle = CheckerFactBundle.model_validate(
        _read_commitments_fixture("reference_fact_bundle.json")
    )

    d1_ir, contracts, result_set, ledger = build_v47a_reference_chain(
        source_text=source_text,
        source_doc_ref="packages/adeu_semantic_source/tests/fixtures/v47a/reference_policy.adeu.md",
        fact_bundle=fact_bundle,
        result_set_id="result-set:v47a-reference",
        ledger_id="ledger:v47a-reference",
    )

    assert d1_ir.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture(
        "reference_d1_normalized_ir.json"
    )
    assert contracts.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture(
        "reference_predicate_contracts_bootstrap.json"
    )
    assert result_set.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture(
        "reference_policy_evaluation_result_set.json"
    )
    assert ledger.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture(
        "reference_policy_obligation_ledger.json"
    )


@pytest.mark.parametrize(
    (
        "source_name",
        "source_doc_ref",
        "fact_bundle_name",
        "result_set_id",
        "ledger_id",
        "d1_name",
        "contracts_name",
        "result_name",
        "ledger_name",
    ),
    [
        (
            "standalone_policy.adeu.md",
            "packages/adeu_semantic_source/tests/fixtures/v47b/standalone_policy.adeu.md",
            "standalone_fact_bundle.json",
            "result-set:v47b-standalone",
            "ledger:v47b-standalone",
            "standalone_reference_d1_normalized_ir.json",
            "standalone_reference_predicate_contracts_bootstrap.json",
            "standalone_reference_policy_evaluation_result_set.json",
            "standalone_reference_policy_obligation_ledger.json",
        ),
        (
            "companion_policy.md",
            "packages/adeu_semantic_source/tests/fixtures/v47b/companion_policy.md",
            "companion_fact_bundle.json",
            "result-set:v47b-companion",
            "ledger:v47b-companion",
            "companion_reference_d1_normalized_ir.json",
            "companion_reference_predicate_contracts_bootstrap.json",
            "companion_reference_policy_evaluation_result_set.json",
            "companion_reference_policy_obligation_ledger.json",
        ),
    ],
)
def test_v47b_examples_replay_deterministically(
    source_name: str,
    source_doc_ref: str,
    fact_bundle_name: str,
    result_set_id: str,
    ledger_id: str,
    d1_name: str,
    contracts_name: str,
    result_name: str,
    ledger_name: str,
) -> None:
    source_text = _read_text_v47b(source_name)
    d1_ir = compile_authoritative_normative_markdown(
        source_text=source_text,
        source_doc_ref=source_doc_ref,
    )
    fact_bundle = CheckerFactBundle.model_validate(_read_commitments_fixture_v47b(fact_bundle_name))
    contracts = default_bootstrap_predicate_contracts()
    result_set = evaluate_authoritative_normative_markdown(
        d1_ir=d1_ir,
        fact_bundle=fact_bundle,
        predicate_contracts=contracts,
        result_set_id=result_set_id,
    )
    ledger = project_policy_obligation_ledger(
        result_set=result_set,
        ledger_id=ledger_id,
    )

    assert d1_ir.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47b(
        d1_name
    )
    assert contracts.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47b(
        contracts_name
    )
    assert result_set.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47b(
        result_name
    )
    assert ledger.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47b(
        ledger_name
    )


def test_v47a_zero_match_emits_notice_without_ledger_rows() -> None:
    source_text = _read_text("reference_policy.adeu.md")
    d1_ir = compile_authoritative_normative_markdown(
        source_text=source_text,
        source_doc_ref="packages/adeu_semantic_source/tests/fixtures/v47a/reference_policy.adeu.md",
    )
    fact_bundle = CheckerFactBundle.model_validate(
        _read_commitments_fixture("zero_match_fact_bundle.json")
    )
    result_set = evaluate_authoritative_normative_markdown(
        d1_ir=d1_ir,
        fact_bundle=fact_bundle,
        predicate_contracts=default_bootstrap_predicate_contracts(),
        result_set_id="result-set:v47a-zero-match",
    )
    ledger = project_policy_obligation_ledger(
        result_set=result_set,
        ledger_id="ledger:v47a-zero-match",
    )

    assert result_set.results == []
    assert len(result_set.notices) == len(d1_ir.clauses)
    assert ledger.rows == []


def test_v47a_unsupported_selector_stays_clause_scope_blocker_without_ledger_row() -> None:
    source_text = _read_text("unknown_selector_policy.adeu.md")
    d1_ir = compile_authoritative_normative_markdown(
        source_text=source_text,
        source_doc_ref="packages/adeu_semantic_source/tests/fixtures/v47a/unknown_selector_policy.adeu.md",
    )
    fact_bundle = CheckerFactBundle.model_validate(
        _read_commitments_fixture("reference_fact_bundle.json")
    )
    result_set = evaluate_authoritative_normative_markdown(
        d1_ir=d1_ir,
        fact_bundle=fact_bundle,
        predicate_contracts=default_bootstrap_predicate_contracts(),
        result_set_id="result-set:v47a-unknown-selector",
    )
    ledger = project_policy_obligation_ledger(
        result_set=result_set,
        ledger_id="ledger:v47a-unknown-selector",
    )

    assert len(result_set.results) == 1
    row = result_set.results[0]
    assert row.result_scope_kind == "clause_scope_blocker"
    assert row.effective_verdict == "unknown_resolution"
    assert ledger.rows == []


def test_v47b_clause_scope_blocker_example_stays_distinct_from_subject_rows() -> None:
    source_text = _read_text_v47b("clause_scope_blocker_policy.adeu.md")
    d1_ir = compile_authoritative_normative_markdown(
        source_text=source_text,
        source_doc_ref=(
            "packages/adeu_semantic_source/tests/fixtures/v47b/"
            "clause_scope_blocker_policy.adeu.md"
        ),
    )
    fact_bundle = CheckerFactBundle.model_validate(
        _read_commitments_fixture_v47b("standalone_fact_bundle.json")
    )
    result_set = evaluate_authoritative_normative_markdown(
        d1_ir=d1_ir,
        fact_bundle=fact_bundle,
        predicate_contracts=default_bootstrap_predicate_contracts(),
        result_set_id="result-set:v47b-clause-blocker",
    )
    ledger = project_policy_obligation_ledger(
        result_set=result_set,
        ledger_id="ledger:v47b-clause-blocker",
    )

    assert d1_ir.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47b(
        "clause_scope_blocker_reference_d1_normalized_ir.json"
    )
    assert result_set.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47b(
        "clause_scope_blocker_reference_policy_evaluation_result_set.json"
    )
    assert ledger.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47b(
        "clause_scope_blocker_reference_policy_obligation_ledger.json"
    )
    assert len(result_set.results) == 1
    assert result_set.results[0].result_scope_kind == "clause_scope_blocker"
    assert "subject_ref" not in result_set.model_dump(mode="json", exclude_none=True)["results"][0]


def test_v47b_zero_match_emits_notices_without_first_ledger_rows() -> None:
    source_text = _read_text_v47b("standalone_policy.adeu.md")
    d1_ir = compile_authoritative_normative_markdown(
        source_text=source_text,
        source_doc_ref="packages/adeu_semantic_source/tests/fixtures/v47b/standalone_policy.adeu.md",
    )
    fact_bundle = CheckerFactBundle.model_validate(
        _read_commitments_fixture_v47b("standalone_zero_match_fact_bundle.json")
    )
    result_set = evaluate_authoritative_normative_markdown(
        d1_ir=d1_ir,
        fact_bundle=fact_bundle,
        predicate_contracts=default_bootstrap_predicate_contracts(),
        result_set_id="result-set:v47b-standalone-zero-match",
    )
    ledger = project_policy_obligation_ledger(
        result_set=result_set,
        ledger_id="ledger:v47b-standalone-zero-match",
    )

    assert result_set.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47b(
        "standalone_zero_match_policy_evaluation_result_set.json"
    )
    assert ledger.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47b(
        "standalone_zero_match_policy_obligation_ledger.json"
    )
    assert result_set.results == []
    assert ledger.rows == []


def test_v47b_zero_match_after_prior_instantiation_reconciles_existing_rows() -> None:
    result_set = PolicyEvaluationResultSet.model_validate(
        _read_commitments_fixture_v47b("standalone_zero_match_policy_evaluation_result_set.json")
    )
    previous_ledger = PolicyObligationLedger.model_validate(
        _read_commitments_fixture_v47b("standalone_reference_policy_obligation_ledger.json")
    )

    ledger = project_policy_obligation_ledger(
        result_set=result_set,
        ledger_id="ledger:v47b-standalone-zero-match",
        previous_ledger=previous_ledger,
    )

    assert ledger.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47b(
        "standalone_zero_match_reconciled_policy_obligation_ledger.json"
    )


def test_v47a_missing_qualifier_contract_fails_closed() -> None:
    source_text = _read_text("reference_policy.adeu.md")
    d1_ir = compile_authoritative_normative_markdown(
        source_text=source_text,
        source_doc_ref="packages/adeu_semantic_source/tests/fixtures/v47a/reference_policy.adeu.md",
    )
    fact_bundle = CheckerFactBundle.model_validate(
        _read_commitments_fixture("reference_fact_bundle.json")
    )
    predicate_contracts = default_bootstrap_predicate_contracts().model_copy(
        update={
            "contracts": [
                contract
                for contract in default_bootstrap_predicate_contracts().contracts
                if contract.predicate_id != "present"
            ]
        }
    )

    with pytest.raises(
        AnmCompileError,
        match="references missing predicate contract\\(s\\) present",
    ):
        evaluate_authoritative_normative_markdown(
            d1_ir=d1_ir,
            fact_bundle=fact_bundle,
            predicate_contracts=predicate_contracts,
            result_set_id="result-set:v47a-missing-qualifier-contract",
        )


def test_v47a_eq_is_type_sensitive_for_boolean_vs_integer() -> None:
    source_text = """
:::D@1 id=bool-eq
ON artifact.emitted[*]
@enabled MUST settings.enabled == true
:::
"""
    d1_ir = compile_authoritative_normative_markdown(
        source_text=source_text,
        source_doc_ref="packages/adeu_semantic_source/tests/fixtures/v47a/type_sensitive_eq.adeu.md",
    )
    fact_bundle = CheckerFactBundle.model_validate(
        {
            "schema": "checker_fact_bundle@1",
            "bundle_id": "fact-bundle:type-sensitive-eq",
            "scope_snapshot": "snapshot:type-sensitive-eq",
            "checker_profile": {
                "checker_profile_id": "checker-profile:type-sensitive-eq",
                "checker_ids": ["checker:type-sensitive-eq"],
            },
            "facts": [
                {
                    "fact_id": "fact:type-sensitive-eq",
                    "subject_ref": "artifact:item",
                    "fact_type": "value_observation",
                    "path": "settings.enabled",
                    "values": [1],
                    "provenance": {
                        "carrier_ref": "carrier:type-sensitive-eq",
                        "mode": "direct",
                    },
                    "checker_id": "checker:type-sensitive-eq",
                    "emitted_at": "2026-04-01T00:00:00Z",
                }
            ],
        }
    )

    result_set = evaluate_authoritative_normative_markdown(
        d1_ir=d1_ir,
        fact_bundle=fact_bundle,
        predicate_contracts=default_bootstrap_predicate_contracts(),
        result_set_id="result-set:type-sensitive-eq",
    )

    assert len(result_set.results) == 1
    row = result_set.results[0]
    assert row.observed_outcome == "fail"
    assert row.effective_verdict == "fail"


def test_v47a_rejects_scope_mismatched_previous_ledger() -> None:
    result_set = PolicyEvaluationResultSet.model_validate(
        _read_commitments_fixture("reference_policy_evaluation_result_set.json")
    )
    previous_ledger = deepcopy(_read_commitments_fixture("reference_policy_obligation_ledger.json"))
    previous_ledger["scope_snapshot"] = "snapshot:other-scope"

    with pytest.raises(
        ValueError,
        match="previous_ledger scope_snapshot must match result_set scope_snapshot",
    ):
        project_policy_obligation_ledger(
            result_set=result_set,
            ledger_id="ledger:v47a-scope-mismatch",
            previous_ledger=PolicyObligationLedger.model_validate(previous_ledger),
        )


@pytest.mark.parametrize(
    "fixture_name",
    [
        "reject_prose_only_obligation.md",
        "reject_source_level_deferred.adeu.md",
        "reject_boolean_logic.adeu.md",
    ],
)
def test_v47a_rejects_forbidden_source_forms(fixture_name: str) -> None:
    with pytest.raises(AnmCompileError):
        compile_authoritative_normative_markdown(
            source_text=_read_text(fixture_name),
            source_doc_ref=f"packages/adeu_semantic_source/tests/fixtures/v47a/{fixture_name}",
        )
