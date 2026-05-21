from __future__ import annotations

from copy import deepcopy

import pytest
from adeu_obligation_broker import (
    REPO_HIERARCHICAL_OBLIGATION_CATALOG_SCHEMA,
    REPO_INHERITED_OBLIGATION_LEDGER_SCHEMA,
    REPO_OBLIGATION_ACTIVATION_ASSESSMENT_SCHEMA,
    InheritedObligationRow,
    IrrelevanceProofRow,
    ProtectedSurfaces,
    RepoHierarchicalObligationCatalog,
    RepoInheritedObligationLedger,
    RepoObligationActivationAssessment,
    canonical_hash,
    expand_inherited_obligations,
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


def _closed_row(node_id: str, parent: str | None) -> InheritedObligationRow:
    return InheritedObligationRow(
        node_id=node_id,
        inherited_from_node_id=parent,
        inheritance_status="root_selected" if parent is None else "inherited_required",
        obligation_status="covered_terminalized",
        probe_refs=["probe:locked-reference-parity"],
        implementation_owner="worker:spec",
    )


def _valid_closed_ledger(
    catalog: RepoHierarchicalObligationCatalog,
    activation: RepoObligationActivationAssessment,
) -> RepoInheritedObligationLedger:
    return RepoInheritedObligationLedger(
        schema=REPO_INHERITED_OBLIGATION_LEDGER_SCHEMA,
        catalog_id=catalog.catalog_id,
        catalog_version=catalog.catalog_version,
        catalog_hash=activation.catalog_hash,
        activation_assessment_ref=canonical_hash(activation),
        obligation_rows=[
            _closed_row("5", None),
            _closed_row("5.1", "5"),
            _closed_row("5.2", "5"),
            _closed_row("5.3", "5"),
        ],
        proof_rows=[],
        readiness_claim_rows=[],
        stale_catalog_posture="current_catalog_hash_bound",
    )


def test_parent_applies_imports_all_children() -> None:
    catalog = _catalog()
    activation = _activation(catalog)

    ledger = expand_inherited_obligations(catalog, activation)

    assert [row.node_id for row in ledger.obligation_rows] == ["5", "5.1", "5.2", "5.3"]
    assert {
        row.node_id
        for row in ledger.obligation_rows
        if row.inheritance_status == "inherited_required"
    } == {
        "5.1",
        "5.2",
        "5.3",
    }


def test_missing_child_fails_closed_and_emits_frontier() -> None:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _valid_closed_ledger(catalog, activation)
    payload = ledger.model_dump(mode="json", exclude_none=True)
    payload["obligation_rows"] = [
        row for row in payload["obligation_rows"] if row["node_id"] != "5.2"
    ]
    ledger = RepoInheritedObligationLedger.model_validate(payload)

    report = validate_obligation_ledger(catalog=catalog, activation=activation, ledger=ledger)

    assert report.validation_status == "failed_closed"
    assert "MISSING_INHERITED_OBLIGATION" in {row.diagnostic_code for row in report.diagnostic_rows}
    assert any(
        row.node_id == "5.2" and row.frontier_reason == "inherited_required_missing_status"
        for row in report.frontier_rows
    )


def test_wrong_child_lineage_fails_closed() -> None:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _valid_closed_ledger(catalog, activation)
    payload = ledger.model_dump(mode="json", exclude_none=True)
    for row in payload["obligation_rows"]:
        if row["node_id"] == "5.2":
            row["inherited_from_node_id"] = None
            row["inheritance_status"] = "root_selected"
    ledger = RepoInheritedObligationLedger.model_validate(payload)

    report = validate_obligation_ledger(catalog=catalog, activation=activation, ledger=ledger)

    assert report.validation_status == "failed_closed"
    assert "INHERITED_OBLIGATION_LINEAGE_MISMATCH" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }
    assert any(row.node_id == "5.2" for row in report.frontier_rows)


def test_scoped_deferral_blocks_parent_gold_ready_claim() -> None:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _valid_closed_ledger(catalog, activation)
    payload = ledger.model_dump(mode="json", exclude_none=True)
    for row in payload["obligation_rows"]:
        if row["node_id"] == "5.2":
            row["obligation_status"] = "scoped_deferred_with_expected_risk"
            row["proof_ref"] = "proof:defer-stderr"
            row["expected_risk_if_deferred"] = "Stderr exactness remains scoped-risk only."
    payload["proof_rows"] = [
        {
            "proof_ref": "proof:defer-stderr",
            "node_id": "5.2",
            "proof_kind": "deferral",
            "proof_type": "scoped_deferral",
            "protected_surfaces": {"stderr": True},
            "warrant_ref": "warrant:visible-spec",
            "deferral_status": "scoped_deferred_with_expected_risk",
            "expected_risk": "Stderr exactness remains scoped-risk only.",
            "proof_text": "The branch is deliberately scoped-deferred for this pass.",
        }
    ]
    payload["readiness_claim_rows"] = [
        {
            "node_id": "5",
            "readiness_status": "gold_ready",
            "readiness_claim_ref": "claim:parent-gold",
        }
    ]
    ledger = RepoInheritedObligationLedger.model_validate(payload)

    report = validate_obligation_ledger(catalog=catalog, activation=activation, ledger=ledger)

    assert report.validation_status == "failed_closed"
    assert report.false_parent_closure_blocked is True
    assert "FALSE_PARENT_GOLD_READY_CLAIM" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }


def test_proved_irrelevant_requires_discriminated_proof_row() -> None:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _valid_closed_ledger(catalog, activation)
    payload = ledger.model_dump(mode="json", exclude_none=True)
    for row in payload["obligation_rows"]:
        if row["node_id"] == "5.2":
            row["obligation_status"] = "proved_irrelevant"
            row["proof_ref"] = "proof:stderr-irrelevant"
    ledger = RepoInheritedObligationLedger.model_validate(payload)

    report = validate_obligation_ledger(catalog=catalog, activation=activation, ledger=ledger)

    assert report.validation_status == "failed_closed"
    assert "UNKNOWN_PROOF_REF" in {row.diagnostic_code for row in report.diagnostic_rows}


def test_unknown_status_vocabulary_fails_schema_validation() -> None:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _valid_closed_ledger(catalog, activation)
    payload = ledger.model_dump(mode="json", exclude_none=True)
    payload["obligation_rows"][1]["obligation_status"] = "probably_ok"

    with pytest.raises(ValidationError):
        RepoInheritedObligationLedger.model_validate(payload)


def test_open_and_blocked_children_emit_deterministic_frontier_rows() -> None:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _valid_closed_ledger(catalog, activation)
    payload = ledger.model_dump(mode="json", exclude_none=True)
    for row in payload["obligation_rows"]:
        if row["node_id"] == "5.1":
            row["obligation_status"] = "open"
            row.pop("probe_refs", None)
            row.pop("implementation_owner", None)
        if row["node_id"] == "5.2":
            row["obligation_status"] = "blocked_pending_equivalence"
            row["proof_ref"] = "proof:stderr-equivalence"
    payload["proof_rows"] = [
        {
            "proof_ref": "proof:stderr-equivalence",
            "node_id": "5.2",
            "proof_kind": "blocking",
            "proof_type": "pending_equivalence",
            "protected_surfaces": {"stderr": True, "exit": True},
            "warrant_ref": "warrant:visible-spec",
            "blocking_status": "blocked_pending_equivalence",
            "required_next_evidence": "Prove stderr/exit parity under target substrate.",
            "proof_text": "The branch is blocked pending equivalence evidence.",
        }
    ]
    ledger = RepoInheritedObligationLedger.model_validate(payload)

    first_report = validate_obligation_ledger(catalog=catalog, activation=activation, ledger=ledger)
    second_report = validate_obligation_ledger(
        catalog=catalog, activation=activation, ledger=ledger
    )

    assert [
        (row.node_id, row.frontier_reason, row.required_next_action)
        for row in first_report.frontier_rows
    ] == [
        (row.node_id, row.frontier_reason, row.required_next_action)
        for row in second_report.frontier_rows
    ]
    assert ("5.1", "active_branch_needs_terminalization", "terminalization") in [
        (row.node_id, row.frontier_reason, row.required_next_action)
        for row in first_report.frontier_rows
    ]
    assert (
        "5.2",
        "blocked_pending_methodological_equivalence",
        "methodological_equivalence_check",
    ) in [
        (row.node_id, row.frontier_reason, row.required_next_action)
        for row in first_report.frontier_rows
    ]


def test_shuffled_input_order_preserves_canonical_hash_and_row_order() -> None:
    catalog = _catalog()
    activation = _activation(catalog)
    ledger = _valid_closed_ledger(catalog, activation)
    payload = ledger.model_dump(mode="json", exclude_none=True)
    shuffled = deepcopy(payload)
    shuffled["obligation_rows"] = list(reversed(shuffled["obligation_rows"]))
    shuffled["readiness_claim_rows"] = [
        {
            "node_id": "5",
            "readiness_status": "scoped_ready",
            "readiness_claim_ref": "claim:parent-scoped",
        }
    ]
    shuffled["proof_rows"] = [
        IrrelevanceProofRow(
            proof_ref="proof:sample",
            node_id="5.3",
            proof_kind="irrelevance",
            proof_type="negative_reference_behavior",
            protected_surfaces=ProtectedSurfaces(exit=True),
            warrant_ref="warrant:visible-spec",
            proof_text="Sample proof row used only to exercise canonical ordering.",
        ).model_dump(mode="json")
    ]
    canonical = deepcopy(shuffled)
    canonical["obligation_rows"] = sorted(
        canonical["obligation_rows"], key=lambda row: row["node_id"]
    )

    first = RepoInheritedObligationLedger.model_validate(shuffled)
    second = RepoInheritedObligationLedger.model_validate(canonical)

    assert [row.node_id for row in first.obligation_rows] == ["5", "5.1", "5.2", "5.3"]
    assert canonical_hash(first, drop_keys={"ledger_hash"}) == canonical_hash(
        second,
        drop_keys={"ledger_hash"},
    )
