from __future__ import annotations

from copy import deepcopy

import pytest
from adeu_obligation_broker import (
    REPO_HIERARCHICAL_OBLIGATION_CATALOG_SCHEMA,
    REPO_INHERITED_OBLIGATION_LEDGER_SCHEMA,
    REPO_OBLIGATION_ACTIVATION_ASSESSMENT_SCHEMA,
    REPO_OBLIGATION_CLOSURE_REPORT_SCHEMA,
    InheritedObligationRow,
    ProbeMatrixRow,
    RepoHierarchicalObligationCatalog,
    RepoInheritedObligationLedger,
    RepoObligationActivationAssessment,
    RepoObligationClosureReport,
    SubtreeClosureRow,
    WeakestChildReadinessRow,
    build_implementation_batch_contract,
    build_operationalization_report,
    canonical_hash,
    compute_obligation_closure,
    plan_next_frontier,
    plan_probe_matrix,
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
                "required_child_node_ids": ["5.1", "5.2", "5.3"],
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
            {
                "node_id": "5.3",
                "parent_node_id": "5",
                "node_kind": "terminal_leaf",
                "title": "Exit",
                "default_inheritance": "inherited_required",
                "authority_ref": "docs/support/example.md#5.3",
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
                    "warrant_summary": "The task exposes stdout, stderr, and exit surfaces.",
                }
            ],
        }
    )


def _row(
    node_id: str,
    parent: str | None,
    status: str,
    *,
    proof_ref: str | None = None,
) -> InheritedObligationRow:
    return InheritedObligationRow(
        node_id=node_id,
        inherited_from_node_id=parent,
        inheritance_status="root_selected" if parent is None else "inherited_required",
        obligation_status=status,
        proof_ref=proof_ref,
        probe_refs=["probe:locked-reference-parity"],
        implementation_owner="worker:spec",
    )


def _ledger(
    catalog: RepoHierarchicalObligationCatalog,
    activation: RepoObligationActivationAssessment,
    *,
    statuses: dict[str, str] | None = None,
) -> RepoInheritedObligationLedger:
    status_by_node = {
        "5": "covered_terminalized",
        "5.1": "covered_terminalized",
        "5.2": "covered_terminalized",
        "5.3": "covered_terminalized",
    }
    status_by_node.update(statuses or {})
    proof_rows = []
    for node_id, status in status_by_node.items():
        if status == "blocked_pending_equivalence":
            proof_rows.append(
                {
                    "proof_ref": f"proof:{node_id}:equivalence",
                    "node_id": node_id,
                    "proof_kind": "blocking",
                    "proof_type": "pending_equivalence",
                    "protected_surfaces": {"stderr": True, "exit": True},
                    "warrant_ref": "warrant:visible-spec",
                    "blocking_status": "blocked_pending_equivalence",
                    "required_next_evidence": "Prove target-substrate equivalence.",
                    "proof_text": "Blocked pending methodological equivalence.",
                }
            )
    return RepoInheritedObligationLedger(
        schema=REPO_INHERITED_OBLIGATION_LEDGER_SCHEMA,
        catalog_id=catalog.catalog_id,
        catalog_version=catalog.catalog_version,
        catalog_hash=activation.catalog_hash,
        activation_assessment_ref=canonical_hash(activation),
        obligation_rows=[
            _row("5", None, status_by_node["5"]),
            _row("5.1", "5", status_by_node["5.1"]),
            _row(
                "5.2",
                "5",
                status_by_node["5.2"],
                proof_ref=(
                    "proof:5.2:equivalence"
                    if status_by_node["5.2"] == "blocked_pending_equivalence"
                    else None
                ),
            ),
            _row("5.3", "5", status_by_node["5.3"]),
        ],
        proof_rows=proof_rows,
        readiness_claim_rows=[],
        stale_catalog_posture="current_catalog_hash_bound",
    )


def _closure_report(
    *,
    statuses: dict[str, str] | None = None,
) -> tuple[
    RepoHierarchicalObligationCatalog,
    RepoInheritedObligationLedger,
    RepoObligationClosureReport,
]:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _ledger(catalog, activation, statuses=statuses)
    validation_report = validate_obligation_ledger(
        catalog=catalog,
        activation=activation,
        ledger=ledger,
    )
    return (
        catalog,
        ledger,
        compute_obligation_closure(
            catalog=catalog,
            ledger=ledger,
            validation_report=validation_report,
        ),
    )


def test_all_required_children_gold_ready_closes_parent_gold() -> None:
    _catalog_obj, _ledger_obj, closure = _closure_report()

    parent = next(row for row in closure.subtree_closure_rows if row.node_id == "5")

    assert closure.closure_status == "gold_ready"
    assert parent.closure_basis == "all_children_gold_ready"
    assert parent.closure_status == "gold_ready"


def test_scoped_child_limits_parent_to_scoped_ready() -> None:
    _catalog_obj, _ledger_obj, closure = _closure_report(
        statuses={"5.2": "covered_by_probe_matrix"}
    )

    parent = next(row for row in closure.subtree_closure_rows if row.node_id == "5")
    weakest = next(row for row in closure.weakest_child_readiness_rows if row.node_id == "5")

    assert parent.closure_basis == "all_children_scoped_ready"
    assert parent.closure_status == "scoped_ready"
    assert weakest.weakest_child_node_id == "5.2"
    assert weakest.weakest_child_readiness == "scoped_ready"


def test_blocked_child_blocks_parent_closure() -> None:
    _catalog_obj, _ledger_obj, closure = _closure_report(
        statuses={"5.2": "blocked_pending_equivalence"}
    )

    parent = next(row for row in closure.subtree_closure_rows if row.node_id == "5")

    assert closure.closure_status == "blocked"
    assert parent.closure_basis == "blocked_by_child"
    assert "5.2" in parent.blocker_node_refs


def test_a_validation_blocker_blocks_b_closure() -> None:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _ledger(catalog, activation)
    payload = ledger.model_dump(mode="json", exclude_none=True)
    payload["obligation_rows"] = [
        row for row in payload["obligation_rows"] if row["node_id"] != "5.2"
    ]
    ledger = RepoInheritedObligationLedger.model_validate(payload)
    validation_report = validate_obligation_ledger(
        catalog=catalog,
        activation=activation,
        ledger=ledger,
    )

    closure = compute_obligation_closure(
        catalog=catalog,
        ledger=ledger,
        validation_report=validation_report,
    )

    assert validation_report.validation_status == "failed_closed"
    assert closure.closure_status == "blocked"
    assert {
        row.closure_basis for row in closure.subtree_closure_rows
    } == {"blocked_by_A_validation"}


def test_parent_readiness_cannot_exceed_weakest_child() -> None:
    with pytest.raises(ValidationError):
        RepoObligationClosureReport(
            schema=REPO_OBLIGATION_CLOSURE_REPORT_SCHEMA,
            catalog_id="program-odeu-obligations",
            catalog_version="v0-test",
            catalog_hash="sha256:abc",
            inherited_obligation_ledger_hash="sha256:ledger",
            traversal_validation_report_hash="sha256:validation",
            a_validation_status="passed",
            subtree_closure_rows=[
                SubtreeClosureRow(
                    node_id="5",
                    child_node_ids=["5.1"],
                    closure_basis="all_children_gold_ready",
                    closure_status="gold_ready",
                )
            ],
            weakest_child_readiness_rows=[
                WeakestChildReadinessRow(
                    node_id="5",
                    weakest_child_node_id="5.1",
                    weakest_child_readiness="scoped_ready",
                )
            ],
            closure_basis_rows=[],
            closure_status="gold_ready",
            closure_authority_posture="local_broker_accounting_only_not_product_truth",
        )


def test_representative_only_branch_cannot_be_marked_fixed_or_gold() -> None:
    with pytest.raises(ValidationError):
        SubtreeClosureRow(
            node_id="5",
            child_node_ids=["5.1"],
            closure_basis="representative_only",
            closure_status="gold_ready",
            representative_only=True,
        )


def test_next_frontier_preserves_a_frontier_and_prioritizes_blockers() -> None:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _ledger(catalog, activation, statuses={"5.2": "blocked_pending_equivalence"})
    validation_report = validate_obligation_ledger(
        catalog=catalog,
        activation=activation,
        ledger=ledger,
    )
    closure = compute_obligation_closure(
        catalog=catalog,
        ledger=ledger,
        validation_report=validation_report,
    )

    frontier = plan_next_frontier(validation_report=validation_report, closure_report=closure)

    assert [row.frontier_ref for row in frontier.frontier_rows] == [
        row.frontier_ref for row in validation_report.frontier_rows
    ]
    assert any(row.priority == "critical" for row in frontier.frontier_priority_rows)
    assert all(
        row.batchability in {"batchable", "requires_sequential_review"}
        for row in frontier.frontier_batchability_rows
    )


def test_probe_matrix_plan_is_plan_only_not_observed() -> None:
    catalog, _ledger_obj, closure = _closure_report()

    plan = plan_probe_matrix(catalog=catalog, closure_report=closure, held_out_node_refs=["5.3"])

    assert plan.probe_authority_posture == "plan_only_not_observed"
    assert plan.probe_plan_non_execution_posture == "plan_only_no_probe_execution"
    assert {row.node_id for row in plan.probe_matrix_rows} == {"5.1", "5.2", "5.3"}
    assert all(
        row.probe_authority_posture == "plan_only_not_observed"
        for row in plan.probe_matrix_rows
    )
    assert next(row for row in plan.probe_matrix_rows if row.node_id == "5.3").probe_kind == (
        "held_out_regression_probe"
    )


def test_probe_matrix_rows_reject_execution_or_observation_posture() -> None:
    with pytest.raises(ValidationError):
        ProbeMatrixRow.model_validate(
            {
                "node_id": "5.1",
                "probe_kind": "terminal_behavior_probe",
                "expected_surface_refs": ["surface:5.1"],
                "probe_authority_posture": "observed_passed",
            }
        )


def test_batch_contract_is_bounded_and_non_dispatching() -> None:
    catalog, _ledger_obj, closure = _closure_report()
    plan = plan_probe_matrix(catalog=catalog, closure_report=closure)

    contract = build_implementation_batch_contract(
        probe_matrix_plan=plan,
        included_node_refs=["5.1", "5.2"],
        owner_ref="worker:spec",
        max_macro_count=2,
    )

    assert contract.worker_dispatch_authority_posture == "no_worker_dispatch_authority"
    assert contract.submit_allowed_posture == "submit_not_allowed_planning_only"
    assert contract.included_node_refs == ["5.1", "5.2"]


def test_batch_contract_rejects_nodes_outside_target_scope() -> None:
    catalog, _ledger_obj, closure = _closure_report()
    plan = plan_probe_matrix(catalog=catalog, closure_report=closure)
    payload = build_implementation_batch_contract(
        probe_matrix_plan=plan,
        included_node_refs=["5.1"],
        owner_ref="worker:spec",
        max_macro_count=1,
    ).model_dump(mode="json", exclude_none=True)
    payload["included_node_refs"] = ["5.4"]
    payload["implementation_owner_rows"][0]["node_refs"] = ["5.4"]

    with pytest.raises(ValidationError):
        build_implementation_batch_contract(
            probe_matrix_plan=plan,
            included_node_refs=["5.4"],
            owner_ref="worker:spec",
            max_macro_count=1,
        )


def test_operationalization_report_remains_planning_only() -> None:
    catalog, _ledger_obj, closure = _closure_report()
    plan = plan_probe_matrix(catalog=catalog, closure_report=closure)
    contract = build_implementation_batch_contract(
        probe_matrix_plan=plan,
        included_node_refs=["5.1"],
        owner_ref="worker:spec",
        max_macro_count=1,
    )

    report = build_operationalization_report(
        closure_report=closure,
        probe_matrix_plan=plan,
        batch_contract=contract,
        worker_task_ref="worker-task:planning-only",
    )

    assert report.operationalization_status == "ready_for_implementation_planning"
    assert report.operationalization_non_authority_posture == "planning_only_not_product_truth"


def test_shuffled_inputs_preserve_closure_hash_and_row_order() -> None:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _ledger(catalog, activation)
    payload = ledger.model_dump(mode="json", exclude_none=True)
    shuffled = deepcopy(payload)
    shuffled["obligation_rows"] = list(reversed(shuffled["obligation_rows"]))
    shuffled_ledger = RepoInheritedObligationLedger.model_validate(shuffled)
    first_validation = validate_obligation_ledger(
        catalog=catalog,
        activation=activation,
        ledger=ledger,
    )
    second_validation = validate_obligation_ledger(
        catalog=catalog,
        activation=activation,
        ledger=shuffled_ledger,
    )

    first = compute_obligation_closure(
        catalog=catalog,
        ledger=ledger,
        validation_report=first_validation,
    )
    second = compute_obligation_closure(
        catalog=catalog,
        ledger=shuffled_ledger,
        validation_report=second_validation,
    )

    assert [row.node_id for row in second.subtree_closure_rows] == ["5", "5.1", "5.2", "5.3"]
    assert canonical_hash(first, drop_keys={"report_hash"}) == canonical_hash(
        second,
        drop_keys={"report_hash"},
    )
