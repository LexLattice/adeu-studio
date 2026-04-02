from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_commitments_ir import (
    AnmMarkdownCoexistenceProfile,
    AnmPolicyConsumerBindingProfile,
    AnmSelectorPredicateOwnershipProfile,
    CheckerFactBundle,
    CheckerProfile,
    FactProvenance,
    PathPresenceObservationFact,
    PolicyObligationLedger,
)
from adeu_ir.repo import repo_root
from adeu_semantic_source import (
    AnmCompileError,
    build_v47e_policy_consumer_binding_profile,
    build_v47f_benchmark_policy_consumer_binding_profile,
    compile_authoritative_normative_markdown,
    default_bootstrap_predicate_contracts,
    evaluate_authoritative_normative_markdown,
    project_policy_obligation_ledger,
)


def _fixture_path_v47c(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47c" / name


def _fixture_path_v47f(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47f" / name


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _read_text_v47c(name: str) -> str:
    return _fixture_path_v47c(name).read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_spec_v47f(name: str) -> dict[str, object]:
    return _read_json(_fixture_path_v47f(name))


def _read_commitments_fixture_v47f(name: str) -> dict[str, object]:
    path = (
        _repo_root()
        / "packages"
        / "adeu_commitments_ir"
        / "tests"
        / "fixtures"
        / "v47f"
        / name
    )
    return _read_json(path)


def _reference_coexistence_profile() -> AnmMarkdownCoexistenceProfile:
    fixture = (
        _repo_root()
        / "packages"
        / "adeu_commitments_ir"
        / "tests"
        / "fixtures"
        / "v47c"
        / "reference_anm_markdown_coexistence_profile.json"
    )
    return AnmMarkdownCoexistenceProfile.model_validate(_read_json(fixture))


def _reference_ownership_profile() -> AnmSelectorPredicateOwnershipProfile:
    fixture = (
        _repo_root()
        / "packages"
        / "adeu_commitments_ir"
        / "tests"
        / "fixtures"
        / "v47d"
        / "reference_anm_selector_predicate_ownership_profile.json"
    )
    return AnmSelectorPredicateOwnershipProfile.model_validate(_read_json(fixture))


def _reference_result_chain():
    source_ref = "packages/adeu_semantic_source/tests/fixtures/v47c/standalone_policy.adeu.md"
    d1_ir = compile_authoritative_normative_markdown(
        source_text=_read_text_v47c("standalone_policy.adeu.md"),
        source_doc_ref=source_ref,
    )
    fact_bundle = CheckerFactBundle(
        bundle_id="fact-bundle:v47f-reference",
        scope_snapshot="snapshot:v47c-reference",
        checker_profile=CheckerProfile(
            checker_profile_id="checker-profile:v47f-reference",
            checker_ids=["checker:v47f"],
        ),
        facts=[
            PathPresenceObservationFact(
                fact_id="fact:metadata.owner:artifact:beta",
                subject_ref="artifact:beta",
                provenance=FactProvenance(
                    carrier_ref="carrier:artifact:beta",
                    mode="direct",
                ),
                checker_id="checker:v47f",
                emitted_at="2026-04-02T00:00:00Z",
                path="metadata.owner",
                values=[True],
            )
        ],
    )
    contracts = default_bootstrap_predicate_contracts()
    result_set = evaluate_authoritative_normative_markdown(
        d1_ir=d1_ir,
        fact_bundle=fact_bundle,
        predicate_contracts=contracts,
        result_set_id="result-set:v47f-reference",
    )
    ledger = project_policy_obligation_ledger(
        result_set=result_set,
        ledger_id="ledger:v47f-reference",
    )
    return d1_ir, result_set, ledger


def _reference_policy_consumer_profile() -> AnmPolicyConsumerBindingProfile:
    spec_path = (
        Path(__file__).parent
        / "fixtures"
        / "v47e"
        / "reference_policy_consumer_spec.json"
    )
    spec = _read_json(spec_path)
    d1_ir, result_set, ledger = _reference_result_chain()
    return build_v47e_policy_consumer_binding_profile(
        snapshot_id=spec["snapshot_id"],
        source_scope_profile=spec["source_scope_profile"],
        released_stack_refs=spec["released_stack_refs"],
        d1_ir=d1_ir,
        result_set=result_set,
        ledger=ledger,
        coexistence_profile=_reference_coexistence_profile(),
        ownership_profile=_reference_ownership_profile(),
        consumer_row_specs=spec["consumer_row_specs"],
        descriptive_artifact_registry=spec["descriptive_artifact_registry"],
        runtime_event_registry=spec["runtime_event_registry"],
    )


def test_v47f_reference_profile_replays_deterministically() -> None:
    spec = _read_spec_v47f("reference_benchmark_policy_consumer_spec.json")
    d1_ir, result_set, ledger = _reference_result_chain()

    profile = build_v47f_benchmark_policy_consumer_binding_profile(
        snapshot_id=spec["snapshot_id"],
        source_scope_profile=spec["source_scope_profile"],
        released_stack_refs=spec["released_stack_refs"],
        d1_ir=d1_ir,
        result_set=result_set,
        ledger=ledger,
        coexistence_profile=_reference_coexistence_profile(),
        ownership_profile=_reference_ownership_profile(),
        policy_consumer_profile=_reference_policy_consumer_profile(),
        benchmark_consumer_row_specs=spec["benchmark_consumer_row_specs"],
        local_eval_registry=spec["local_eval_registry"],
        scorecard_registry=spec["scorecard_registry"],
        behavior_evidence_registry=spec["behavior_evidence_registry"],
    )

    assert profile.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47f(
        "reference_anm_benchmark_policy_consumer_binding_profile.json"
    )


def test_v47f_accepts_all_three_benchmark_worlds() -> None:
    spec = _read_spec_v47f("reference_benchmark_policy_consumer_spec.json")
    d1_ir, result_set, ledger = _reference_result_chain()

    profile = build_v47f_benchmark_policy_consumer_binding_profile(
        snapshot_id=spec["snapshot_id"],
        source_scope_profile=spec["source_scope_profile"],
        released_stack_refs=spec["released_stack_refs"],
        d1_ir=d1_ir,
        result_set=result_set,
        ledger=ledger,
        coexistence_profile=_reference_coexistence_profile(),
        ownership_profile=_reference_ownership_profile(),
        policy_consumer_profile=_reference_policy_consumer_profile(),
        benchmark_consumer_row_specs=spec["benchmark_consumer_row_specs"],
        local_eval_registry=spec["local_eval_registry"],
        scorecard_registry=spec["scorecard_registry"],
        behavior_evidence_registry=spec["behavior_evidence_registry"],
    )

    assert {row.benchmark_consumer_world_kind for row in profile.benchmark_consumer_rows} == {
        "released_v42_behavior_evidence_artifact_world",
        "released_v42_local_eval_artifact_world",
        "released_v42_scorecard_artifact_world",
    }


def test_v47f_rejects_support_only_authority_claim() -> None:
    spec = _read_spec_v47f("reject_support_only_authority_spec.json")
    d1_ir, result_set, ledger = _reference_result_chain()

    with pytest.raises(AnmCompileError, match="String should have at least 1 character"):
        build_v47f_benchmark_policy_consumer_binding_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            d1_ir=d1_ir,
            result_set=result_set,
            ledger=ledger,
            coexistence_profile=_reference_coexistence_profile(),
            ownership_profile=_reference_ownership_profile(),
            policy_consumer_profile=_reference_policy_consumer_profile(),
            benchmark_consumer_row_specs=spec["benchmark_consumer_row_specs"],
            local_eval_registry=spec.get("local_eval_registry"),
            scorecard_registry=spec.get("scorecard_registry"),
            behavior_evidence_registry=spec.get("behavior_evidence_registry"),
        )


def test_v47f_rejects_contradictory_supporting_surfaces() -> None:
    spec = _read_spec_v47f("reference_benchmark_policy_consumer_spec.json")
    d1_ir, result_set, ledger = _reference_result_chain()
    payload = ledger.model_dump(mode="json", exclude_none=True)
    payload["rows"][0]["latest_effective_verdict"] = "fail"
    payload["rows"][0]["ledger_state"] = "violated"
    contradictory_ledger = PolicyObligationLedger.model_validate(payload)

    with pytest.raises(
        AnmCompileError,
        match="has contradictory supporting result/ledger posture",
    ):
        build_v47f_benchmark_policy_consumer_binding_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            d1_ir=d1_ir,
            result_set=result_set,
            ledger=contradictory_ledger,
            coexistence_profile=_reference_coexistence_profile(),
            ownership_profile=_reference_ownership_profile(),
            policy_consumer_profile=_reference_policy_consumer_profile(),
            benchmark_consumer_row_specs=spec["benchmark_consumer_row_specs"],
            local_eval_registry=spec["local_eval_registry"],
            scorecard_registry=spec["scorecard_registry"],
            behavior_evidence_registry=spec["behavior_evidence_registry"],
        )


def test_v47f_rejects_supporting_surface_with_wrong_target() -> None:
    spec = _read_spec_v47f("reference_benchmark_policy_consumer_spec.json")
    d1_ir, result_set, ledger = _reference_result_chain()
    payload = result_set.model_dump(mode="json", exclude_none=True)
    payload["results"][0]["subject_ref"] = "artifact:gamma"
    incompatible_result_set = result_set.model_validate(payload)

    with pytest.raises(
        AnmCompileError,
        match=(
            "supporting result ref result:release_surface:owner:artifact:beta does not "
            "cohere to benchmark target artifact:beta"
        ),
    ):
        build_v47f_benchmark_policy_consumer_binding_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            d1_ir=d1_ir,
            result_set=incompatible_result_set,
            ledger=ledger,
            coexistence_profile=_reference_coexistence_profile(),
            ownership_profile=_reference_ownership_profile(),
            policy_consumer_profile=_reference_policy_consumer_profile(),
            benchmark_consumer_row_specs=spec["benchmark_consumer_row_specs"],
            local_eval_registry=spec["local_eval_registry"],
            scorecard_registry=spec["scorecard_registry"],
            behavior_evidence_registry=spec["behavior_evidence_registry"],
        )


def test_v47f_rejects_unresolved_local_eval_ref() -> None:
    spec = _read_spec_v47f("reject_unresolved_local_eval_ref_spec.json")
    d1_ir, result_set, ledger = _reference_result_chain()

    with pytest.raises(
        AnmCompileError,
        match=(
            "released local eval ref "
            "apps/api/fixtures/arc_agi/vnext_plus92/adeu_arc_local_eval_record_v92_missing.json "
            "is unresolved"
        ),
    ):
        build_v47f_benchmark_policy_consumer_binding_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            d1_ir=d1_ir,
            result_set=result_set,
            ledger=ledger,
            coexistence_profile=_reference_coexistence_profile(),
            ownership_profile=_reference_ownership_profile(),
            policy_consumer_profile=_reference_policy_consumer_profile(),
            benchmark_consumer_row_specs=spec["benchmark_consumer_row_specs"],
            local_eval_registry=spec["local_eval_registry"],
            scorecard_registry=spec.get("scorecard_registry"),
            behavior_evidence_registry=spec.get("behavior_evidence_registry"),
        )


def test_v47f_rejects_world_ref_kind_mismatch() -> None:
    spec = _read_spec_v47f("reject_world_ref_kind_mismatch_spec.json")
    d1_ir, result_set, ledger = _reference_result_chain()

    with pytest.raises(
        AnmCompileError,
        match=(
            "released_v42_local_eval_artifact_world rows require "
            "benchmark_consumer_ref_kind = released_v42_local_eval_record_ref"
        ),
    ):
        build_v47f_benchmark_policy_consumer_binding_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            d1_ir=d1_ir,
            result_set=result_set,
            ledger=ledger,
            coexistence_profile=_reference_coexistence_profile(),
            ownership_profile=_reference_ownership_profile(),
            policy_consumer_profile=_reference_policy_consumer_profile(),
            benchmark_consumer_row_specs=spec["benchmark_consumer_row_specs"],
            local_eval_registry=spec["local_eval_registry"],
            scorecard_registry=spec.get("scorecard_registry"),
            behavior_evidence_registry=spec.get("behavior_evidence_registry"),
        )


def test_v47f_rejects_bypass_upstream_profile() -> None:
    spec = _read_spec_v47f("reject_bypass_upstream_profile_spec.json")
    d1_ir, result_set, ledger = _reference_result_chain()

    with pytest.raises(
        AnmCompileError,
        match=(
            "benchmark consumer ref "
            "apps/api/fixtures/arc_agi/vnext_plus92/adeu_arc_local_eval_record_v92_reference.json "
            "bypasses released V47-D selector doctrine"
        ),
    ):
        build_v47f_benchmark_policy_consumer_binding_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            d1_ir=d1_ir,
            result_set=result_set,
            ledger=ledger,
            coexistence_profile=_reference_coexistence_profile(),
            ownership_profile=_reference_ownership_profile(),
            policy_consumer_profile=_reference_policy_consumer_profile(),
            benchmark_consumer_row_specs=spec["benchmark_consumer_row_specs"],
            local_eval_registry=spec["local_eval_registry"],
            scorecard_registry=spec.get("scorecard_registry"),
            behavior_evidence_registry=spec.get("behavior_evidence_registry"),
        )
