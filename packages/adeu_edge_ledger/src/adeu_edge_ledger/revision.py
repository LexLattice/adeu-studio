from __future__ import annotations

from typing import Iterable

from .models import (
    EdgeTaxonomyRevisionEntry,
    EdgeTaxonomyRevisionRegister,
    SymbolEdgeAdjudicationLedger,
    _sha256_canonical_payload,
    compute_edge_taxonomy_revision_register_id,
)

_ANCHOR_ADJUDICATION_STATUSES = {"witness_found", "checked_no_witness_found"}


def _normalize_revision_entries(
    revision_entries: Iterable[EdgeTaxonomyRevisionEntry | dict[str, object]],
) -> list[EdgeTaxonomyRevisionEntry]:
    return [
        entry
        if isinstance(entry, EdgeTaxonomyRevisionEntry)
        else EdgeTaxonomyRevisionEntry.model_validate(entry)
        for entry in revision_entries
    ]


def _normalize_prior_register(
    prior_revision_register: EdgeTaxonomyRevisionRegister | dict[str, object] | None,
) -> EdgeTaxonomyRevisionRegister | None:
    if prior_revision_register is None:
        return None
    if isinstance(prior_revision_register, EdgeTaxonomyRevisionRegister):
        return prior_revision_register
    return EdgeTaxonomyRevisionRegister.model_validate(prior_revision_register)


def _validate_entry_support_rows(
    *,
    register: EdgeTaxonomyRevisionRegister,
    adjudication_ledger: SymbolEdgeAdjudicationLedger,
) -> None:
    ledger_rows_by_ref = {row.edge_class_ref: row for row in adjudication_ledger.adjudication_rows}

    for entry in register.revision_entries:
        for subject_ref in entry.subject_edge_class_refs:
            if subject_ref not in ledger_rows_by_ref:
                raise ValueError(
                    "revision subject_edge_class_refs must resolve against the bound "
                    "adjudication ledger rows"
                )

        statuses: list[str] = []
        for row_ref in entry.supporting_adjudication_row_refs:
            if row_ref not in ledger_rows_by_ref:
                raise ValueError(
                    "supporting_adjudication_row_refs must resolve against the bound "
                    "adjudication ledger rows"
                )
            statuses.append(ledger_rows_by_ref[row_ref].adjudication_status)

        if not any(status in _ANCHOR_ADJUDICATION_STATUSES for status in statuses):
            if statuses and all(status == "deferred" for status in statuses):
                raise ValueError(
                    "revision entries must not use deferred adjudication rows as sole support"
                )
            raise ValueError(
                "revision entries require at least one witness_found or "
                "checked_no_witness_found support row"
            )


def derive_edge_taxonomy_revision_register(
    *,
    adjudication_ledger: SymbolEdgeAdjudicationLedger,
    revision_entries: Iterable[EdgeTaxonomyRevisionEntry | dict[str, object]],
    prior_revision_register: EdgeTaxonomyRevisionRegister | dict[str, object] | None = None,
) -> EdgeTaxonomyRevisionRegister:
    prior = _normalize_prior_register(prior_revision_register)
    new_entries = _normalize_revision_entries(revision_entries)
    preserved_entries = [] if prior is None else list(prior.revision_entries)

    payload_without_id = {
        "schema": EdgeTaxonomyRevisionRegister.model_fields["schema_id"].default,
        "bound_edge_class_catalog_ref": adjudication_ledger.bound_edge_class_catalog_ref,
        "bound_probe_template_catalog_ref": adjudication_ledger.bound_probe_template_catalog_ref,
        "bound_adjudication_ledger_ref": adjudication_ledger.ledger_id,
        "prior_revision_register_ref": None if prior is None else prior.register_id,
        "revision_entries": [
            entry.model_dump(mode="json", exclude_none=True)
            for entry in [*preserved_entries, *new_entries]
        ],
    }
    register_hash = _sha256_canonical_payload(payload_without_id)
    register = EdgeTaxonomyRevisionRegister(
        register_id=compute_edge_taxonomy_revision_register_id(
            {
                **payload_without_id,
                "register_hash": register_hash,
            }
        ),
        bound_edge_class_catalog_ref=adjudication_ledger.bound_edge_class_catalog_ref,
        bound_probe_template_catalog_ref=adjudication_ledger.bound_probe_template_catalog_ref,
        bound_adjudication_ledger_ref=adjudication_ledger.ledger_id,
        prior_revision_register_ref=None if prior is None else prior.register_id,
        revision_entries=[*preserved_entries, *new_entries],
        register_hash=register_hash,
    )
    _validate_entry_support_rows(register=register, adjudication_ledger=adjudication_ledger)
    if prior is not None:
        validate_edge_taxonomy_revision_register_bindings(
            register_payload=register.model_dump(mode="json", by_alias=True, exclude_none=True),
            adjudication_ledger=adjudication_ledger,
            prior_revision_register=prior,
        )
    return register


def validate_edge_taxonomy_revision_register_bindings(
    *,
    register_payload: dict[str, object],
    adjudication_ledger: SymbolEdgeAdjudicationLedger,
    prior_revision_register: EdgeTaxonomyRevisionRegister | dict[str, object] | None = None,
) -> EdgeTaxonomyRevisionRegister:
    register = EdgeTaxonomyRevisionRegister.model_validate(register_payload)
    prior = _normalize_prior_register(prior_revision_register)

    if register.bound_edge_class_catalog_ref != adjudication_ledger.bound_edge_class_catalog_ref:
        raise ValueError("register must preserve bound_edge_class_catalog_ref from the ledger")
    if (
        register.bound_probe_template_catalog_ref
        != adjudication_ledger.bound_probe_template_catalog_ref
    ):
        raise ValueError("register must preserve bound_probe_template_catalog_ref from the ledger")
    if register.bound_adjudication_ledger_ref != adjudication_ledger.ledger_id:
        raise ValueError("register must bind the current released adjudication ledger")

    if prior is None:
        if register.prior_revision_register_ref is not None:
            raise ValueError(
                "register prior_revision_register_ref requires the bound prior revision register"
            )
    else:
        if register.prior_revision_register_ref != prior.register_id:
            raise ValueError(
                "register prior_revision_register_ref must match the bound prior register"
            )
        if prior.bound_adjudication_ledger_ref != adjudication_ledger.ledger_id:
            raise ValueError(
                "prior revision register must bind the exact same current adjudication ledger"
            )
        if prior.bound_edge_class_catalog_ref != register.bound_edge_class_catalog_ref:
            raise ValueError("prior revision register must preserve bound_edge_class_catalog_ref")
        if prior.bound_probe_template_catalog_ref != register.bound_probe_template_catalog_ref:
            raise ValueError(
                "prior revision register must preserve bound_probe_template_catalog_ref"
            )

        prior_entries = [
            entry.model_dump(mode="json", exclude_none=True) for entry in prior.revision_entries
        ]
        emitted_prefix = [
            entry.model_dump(mode="json", exclude_none=True)
            for entry in register.revision_entries[: len(prior.revision_entries)]
        ]
        if emitted_prefix != prior_entries:
            raise ValueError("register must preserve prior revision entry order exactly")

    _validate_entry_support_rows(register=register, adjudication_ledger=adjudication_ledger)
    return register


__all__ = [
    "derive_edge_taxonomy_revision_register",
    "validate_edge_taxonomy_revision_register_bindings",
]
