from __future__ import annotations

from copy import deepcopy

import pytest
from adeu_obligation_broker import (
    REPO_HIERARCHICAL_OBLIGATION_CATALOG_SCHEMA,
    REPO_INHERITED_OBLIGATION_LEDGER_SCHEMA,
    REPO_OBLIGATION_ACTIVATION_ASSESSMENT_SCHEMA,
    REPO_OBLIGATION_BROKER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    DeltaAttributionRow,
    HandoffPressureRow,
    RepoHierarchicalObligationCatalog,
    RepoInheritedObligationLedger,
    RepoObligationActivationAssessment,
    RepoObligationBrokerFamilyCloseoutAlignment,
    RepoObligationDeltaAttributionLedger,
    RepoObligationStaleLedgerInvalidationReport,
    build_delta_attribution_ledger,
    build_family_closeout_alignment,
    build_integration_handoff,
    build_stale_ledger_invalidation_report,
    canonical_hash,
    compute_obligation_closure,
    validate_obligation_ledger,
)
from pydantic import ValidationError


def _catalog_payload() -> dict[str, object]:
    return {
        "schema": REPO_HIERARCHICAL_OBLIGATION_CATALOG_SCHEMA,
        "catalog_id": "program-odeu-obligations",
        "catalog_version": "v0-test",
        "catalog_authority": "support",
        "catalog_nodes": [
            {
                "node_id": "5",
                "parent_node_id": None,
                "node_kind": "macro",
                "title": "Output Router",
                "default_inheritance": "inherited_required",
                "authority_ref": "docs/support/example.md#5",
                "required_child_node_ids": ["5.1", "5.2"],
            },
            {
                "node_id": "5.1",
                "parent_node_id": "5",
                "node_kind": "terminal_leaf",
                "title": "Stdout",
                "default_inheritance": "inherited_required",
                "authority_ref": "docs/support/example.md#5.1",
                "required_child_node_ids": [],
            },
            {
                "node_id": "5.2",
                "parent_node_id": "5",
                "node_kind": "terminal_leaf",
                "title": "Stderr",
                "default_inheritance": "inherited_required",
                "authority_ref": "docs/support/example.md#5.2",
                "required_child_node_ids": [],
            },
        ],
    }


def _catalog() -> RepoHierarchicalObligationCatalog:
    catalog_without_hash = RepoHierarchicalObligationCatalog.model_validate(_catalog_payload())
    payload = catalog_without_hash.model_dump(mode="json", exclude_none=True)
    payload["catalog_hash"] = canonical_hash(catalog_without_hash, drop_keys={"catalog_hash"})
    return RepoHierarchicalObligationCatalog.model_validate(payload)


def _activation(catalog: RepoHierarchicalObligationCatalog) -> RepoObligationActivationAssessment:
    return RepoObligationActivationAssessment.model_validate(
        {
            "schema": REPO_OBLIGATION_ACTIVATION_ASSESSMENT_SCHEMA,
            "catalog_id": catalog.catalog_id,
            "catalog_version": catalog.catalog_version,
            "catalog_hash": catalog.catalog_hash,
            "semantic_judgment_authority_posture": "model_authored_broker_schema_validated",
            "activation_rows": [
                {
                    "node_id": "5",
                    "activation_status": "applies",
                    "warrant_refs": ["warrant:visible-spec"],
                    "activation_note": "The output router macro applies.",
                }
            ],
            "warrant_rows": [
                {
                    "warrant_ref": "warrant:visible-spec",
                    "warrant_kind": "visible_spec",
                    "authority_layer": "support",
                    "warrant_summary": "The task exposes output surfaces.",
                }
            ],
        }
    )


def _ledger(
    catalog: RepoHierarchicalObligationCatalog,
    activation: RepoObligationActivationAssessment,
) -> RepoInheritedObligationLedger:
    return RepoInheritedObligationLedger.model_validate(
        {
            "schema": REPO_INHERITED_OBLIGATION_LEDGER_SCHEMA,
            "catalog_id": catalog.catalog_id,
            "catalog_version": catalog.catalog_version,
            "catalog_hash": activation.catalog_hash,
            "activation_assessment_ref": canonical_hash(activation),
            "obligation_rows": [
                {
                    "node_id": "5",
                    "inherited_from_node_id": None,
                    "inheritance_status": "root_selected",
                    "obligation_status": "covered_terminalized",
                    "probe_refs": ["probe:macro"],
                    "implementation_owner": "worker:spec",
                },
                {
                    "node_id": "5.1",
                    "inherited_from_node_id": "5",
                    "inheritance_status": "inherited_required",
                    "obligation_status": "covered_terminalized",
                    "probe_refs": ["probe:stdout"],
                    "implementation_owner": "worker:spec",
                },
                {
                    "node_id": "5.2",
                    "inherited_from_node_id": "5",
                    "inheritance_status": "inherited_required",
                    "obligation_status": "covered_terminalized",
                    "probe_refs": ["probe:stderr"],
                    "implementation_owner": "worker:spec",
                },
            ],
            "proof_rows": [],
            "readiness_claim_rows": [],
            "stale_catalog_posture": "current_catalog_hash_bound",
        }
    )


def _closure() -> tuple[RepoHierarchicalObligationCatalog, object]:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _ledger(catalog, activation)
    validation_report = validate_obligation_ledger(
        catalog=catalog,
        activation=activation,
        ledger=ledger,
    )
    return catalog, compute_obligation_closure(
        catalog=catalog,
        ledger=ledger,
        validation_report=validation_report,
    )


def _delta_row(
    *,
    node_id: str = "5.1",
    source_delta_ref: str = "delta:stdout",
    interpretation: str = "representative_transfer_success",
    closure_effect_posture: str = "pressure_only_no_closure",
    evidence_boundary_posture: str = "local_locked_probe_delta",
) -> DeltaAttributionRow:
    return DeltaAttributionRow.model_validate(
        {
            "node_id": node_id,
            "macro_ref": "5",
            "source_delta_ref": source_delta_ref,
            "attribution_kind": "failure_reduction_pressure",
            "attribution_confidence": "medium",
            "matrix_rows_green": ["row:stdout"],
            "rows_moved_to_other_failure": [],
            "regressions": [],
            "interpretation": interpretation,
            "closure_effect_posture": closure_effect_posture,
            "evidence_boundary_posture": evidence_boundary_posture,
        }
    )


def test_local_locked_probe_delta_is_attributed_without_product_truth() -> None:
    catalog, closure = _closure()

    ledger = build_delta_attribution_ledger(
        catalog=catalog,
        closure_report=closure,
        run_before_ref="run:before",
        run_after_ref="run:after",
        delta_attribution_rows=[_delta_row()],
        changed_failure_rows=["eval-row:stdout"],
    )

    assert ledger.delta_authority_posture == "pressure_attribution_only_not_product_truth"
    assert ledger.evidence_boundary_posture == "local_locked_probe_delta"
    assert ledger.delta_attribution_rows[0].node_id == "5.1"


def test_delta_attribution_rejects_unknown_node_ids() -> None:
    catalog, closure = _closure()

    with pytest.raises(ValueError):
        build_delta_attribution_ledger(
            catalog=catalog,
            closure_report=closure,
            run_before_ref="run:before",
            run_after_ref="run:after",
            delta_attribution_rows=[_delta_row(node_id="5.9")],
        )


def test_official_like_pressure_cannot_close_macro() -> None:
    catalog, closure = _closure()

    with pytest.raises(ValidationError):
        build_delta_attribution_ledger(
            catalog=catalog,
            closure_report=closure,
            run_before_ref="run:before",
            run_after_ref="run:after",
            delta_attribution_rows=[
                _delta_row(
                    node_id="5",
                    interpretation="macro_closure_success",
                    closure_effect_posture="macro_closure_supported_by_released_closure",
                    evidence_boundary_posture="official_like_pressure",
                )
            ],
            evidence_boundary_posture="official_like_pressure",
        )


def test_attribution_row_requires_evidence_boundary_posture() -> None:
    payload = _delta_row().model_dump(mode="json")
    payload.pop("evidence_boundary_posture")

    with pytest.raises(ValidationError):
        DeltaAttributionRow.model_validate(payload)


def test_stale_catalog_hash_invalidates_prior_ledgers_and_probe_plans() -> None:
    report = build_stale_ledger_invalidation_report(
        prior_catalog_id="program-odeu-obligations",
        prior_catalog_version="v0",
        prior_catalog_hash="sha256:old",
        current_catalog_id="program-odeu-obligations",
        current_catalog_version="v1",
        current_catalog_hash="sha256:new",
        prior_ledger_refs=["ledger:old"],
        prior_probe_plan_refs=["probe-plan:old"],
    )

    assert report.stale_ledger_reuse_posture == "stale_catalog_hash_invalidated"
    assert report.invalidated_ledger_refs == ["ledger:old"]
    assert report.invalidated_probe_plan_refs == ["probe-plan:old"]


def test_stale_catalog_hash_change_without_invalidations_fails_closed() -> None:
    with pytest.raises(ValidationError):
        RepoObligationStaleLedgerInvalidationReport.model_validate(
            {
                "schema": "repo_obligation_stale_ledger_invalidation_report@1",
                "prior_catalog_id": "program-odeu-obligations",
                "prior_catalog_version": "v0",
                "prior_catalog_hash": "sha256:old",
                "current_catalog_id": "program-odeu-obligations",
                "current_catalog_version": "v1",
                "current_catalog_hash": "sha256:new",
                "invalidated_ledger_refs": [],
                "invalidated_probe_plan_refs": [],
                "invalidation_reason_rows": [],
                "stale_ledger_reuse_posture": "current_catalog_hash_bound",
            }
        )


def test_unchanged_catalog_hash_rejects_invalidation_refs() -> None:
    with pytest.raises(ValidationError):
        RepoObligationStaleLedgerInvalidationReport.model_validate(
            {
                "schema": "repo_obligation_stale_ledger_invalidation_report@1",
                "prior_catalog_id": "program-odeu-obligations",
                "prior_catalog_version": "v1",
                "prior_catalog_hash": "sha256:same",
                "current_catalog_id": "program-odeu-obligations",
                "current_catalog_version": "v1",
                "current_catalog_hash": "sha256:same",
                "invalidated_ledger_refs": ["ledger:current"],
                "invalidated_probe_plan_refs": [],
                "invalidation_reason_rows": [
                    {
                        "invalidated_ref": "ledger:current",
                        "stale_reason": "contradictory invalidation",
                        "invalidation_status": "invalidated",
                    }
                ],
                "stale_ledger_reuse_posture": "current_catalog_hash_bound",
            }
        )


def test_integration_handoff_is_pressure_only_and_non_selecting() -> None:
    catalog, _closure_report = _closure()

    handoff = build_integration_handoff(
        catalog=catalog,
        handoff_pressure_kind="future_probe_execution_governance_review",
        handoff_pressure_rows=[
            HandoffPressureRow.model_validate(
                {
                    "pressure_ref": "pressure:probe-execution",
                    "target_node_refs": ["5.1"],
                    "handoff_pressure_kind": "future_probe_execution_governance_review",
                    "pressure_summary": "Terminal node still needs execution governance.",
                    "evidence_boundary_posture": "local_locked_probe_delta",
                }
            )
        ],
    )

    assert handoff.handoff_non_selection_posture == "pressure_only_no_future_family_selection"
    assert handoff.probe_execution_authority_posture == "no_probe_execution_authority"
    assert handoff.future_family_selection_posture == "no_future_family_selection"


def test_integration_handoff_rejects_mixed_pressure_kinds() -> None:
    catalog, _closure_report = _closure()

    with pytest.raises(ValidationError):
        build_integration_handoff(
            catalog=catalog,
            handoff_pressure_kind="future_probe_execution_governance_review",
            handoff_pressure_rows=[
                HandoffPressureRow.model_validate(
                    {
                        "pressure_ref": "pressure:probe-execution",
                        "target_node_refs": ["5.1"],
                        "handoff_pressure_kind": "future_probe_execution_governance_review",
                        "pressure_summary": "Probe execution governance pressure.",
                        "evidence_boundary_posture": "local_locked_probe_delta",
                    }
                ),
                HandoffPressureRow.model_validate(
                    {
                        "pressure_ref": "pressure:implementation",
                        "target_node_refs": ["5.2"],
                        "handoff_pressure_kind": "future_implementation_authority_review",
                        "pressure_summary": "Mixed implementation pressure.",
                        "evidence_boundary_posture": "local_locked_probe_delta",
                    }
                ),
            ],
        )


def test_handoff_rejects_unknown_node_ids() -> None:
    catalog, _closure_report = _closure()

    with pytest.raises(ValueError):
        build_integration_handoff(
            catalog=catalog,
            handoff_pressure_kind="future_family_only",
            handoff_pressure_rows=[
                HandoffPressureRow.model_validate(
                    {
                        "pressure_ref": "pressure:unknown",
                        "target_node_refs": ["9"],
                        "handoff_pressure_kind": "future_family_only",
                        "pressure_summary": "Unknown node pressure.",
                        "evidence_boundary_posture": "post_eval_pressure_only",
                    }
                )
            ],
        )


def test_open_with_deferred_family_closeout_rejects_active_blockers() -> None:
    with pytest.raises(ValidationError):
        RepoObligationBrokerFamilyCloseoutAlignment.model_validate(
            {
                "schema": REPO_OBLIGATION_BROKER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
                "family_ref": "HOB-0",
                "closed_slices": ["HOB-0-A", "HOB-0-B", "HOB-0-C"],
                "slice_a_closeout_ref": "closeout:HOB-0-A",
                "slice_b_closeout_ref": "closeout:HOB-0-B",
                "slice_c_closeout_ref": "closeout:HOB-0-C",
                "family_scope_posture": "hob_0_family_open_with_deferred_refs",
                "residual_deferred_refs": ["deferred:integration"],
                "blocker_refs": ["blocker:unresolved-b"],
                "integration_authority_posture": "no_integration_authority",
                "implementation_authority_posture": "no_implementation_authority",
                "future_family_selection_posture": "no_future_family_selection",
            }
        )


def test_family_closeout_alignment_closes_only_without_residual_blockers() -> None:
    alignment = build_family_closeout_alignment(
        slice_a_closeout_ref="closeout:HOB-0-A",
        slice_b_closeout_ref="closeout:HOB-0-B",
        slice_c_closeout_ref="closeout:HOB-0-C",
    )

    assert alignment.family_scope_posture == "hob_0_family_closed"
    assert alignment.closed_slices == ["HOB-0-A", "HOB-0-B", "HOB-0-C"]
    assert alignment.future_family_selection_posture == "no_future_family_selection"


def test_family_closeout_rejects_unknown_slices() -> None:
    with pytest.raises(ValidationError):
        RepoObligationBrokerFamilyCloseoutAlignment.model_validate(
            {
                "schema": REPO_OBLIGATION_BROKER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
                "family_ref": "HOB-0",
                "closed_slices": ["HOB-0-A", "HOB-0-D"],
                "slice_a_closeout_ref": "closeout:HOB-0-A",
                "slice_b_closeout_ref": "closeout:HOB-0-B",
                "slice_c_closeout_ref": "closeout:HOB-0-C",
                "family_scope_posture": "hob_0_family_closed",
                "residual_deferred_refs": [],
                "blocker_refs": [],
                "integration_authority_posture": "no_integration_authority",
                "implementation_authority_posture": "no_implementation_authority",
                "future_family_selection_posture": "no_future_family_selection",
            }
        )


def test_family_closeout_cannot_hide_residual_blockers() -> None:
    with pytest.raises(ValidationError):
        RepoObligationBrokerFamilyCloseoutAlignment.model_validate(
            {
                "schema": REPO_OBLIGATION_BROKER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
                "family_ref": "HOB-0",
                "closed_slices": ["HOB-0-A", "HOB-0-B", "HOB-0-C"],
                "slice_a_closeout_ref": "closeout:HOB-0-A",
                "slice_b_closeout_ref": "closeout:HOB-0-B",
                "slice_c_closeout_ref": "closeout:HOB-0-C",
                "family_scope_posture": "hob_0_family_closed",
                "residual_deferred_refs": ["deferred:integration"],
                "blocker_refs": [],
                "integration_authority_posture": "no_integration_authority",
                "implementation_authority_posture": "no_implementation_authority",
                "future_family_selection_posture": "no_future_family_selection",
            }
        )


def test_shuffled_inputs_preserve_delta_ledger_hash_and_row_order() -> None:
    catalog, closure = _closure()
    first = build_delta_attribution_ledger(
        catalog=catalog,
        closure_report=closure,
        run_before_ref="run:before",
        run_after_ref="run:after",
        delta_attribution_rows=[
            _delta_row(node_id="5.2", source_delta_ref="delta:stderr"),
            _delta_row(node_id="5.1", source_delta_ref="delta:stdout"),
        ],
        changed_failure_rows=["row:b", "row:a"],
    )
    payload = first.model_dump(mode="json", exclude_none=True)
    shuffled = deepcopy(payload)
    shuffled["delta_attribution_rows"] = list(reversed(shuffled["delta_attribution_rows"]))
    shuffled["changed_failure_rows"] = list(reversed(shuffled["changed_failure_rows"]))
    second = RepoObligationDeltaAttributionLedger.model_validate(shuffled)

    assert [row.source_delta_ref for row in second.delta_attribution_rows] == [
        "delta:stderr",
        "delta:stdout",
    ]
    assert canonical_hash(first, drop_keys={"ledger_hash"}) == canonical_hash(
        second,
        drop_keys={"ledger_hash"},
    )
