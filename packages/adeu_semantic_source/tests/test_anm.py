from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_commitments_ir import CheckerFactBundle
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


def _read_text(name: str) -> str:
    return _fixture_path(name).read_text(encoding="utf-8")


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
