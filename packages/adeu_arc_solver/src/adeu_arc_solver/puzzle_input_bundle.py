from __future__ import annotations

from typing import Any, Literal

from adeu_arc_agi import derive_v42g1_arc_puzzle_input_bundle


def derive_v42g1_puzzle_input_bundle(
    *,
    selection_register_ref: str,
    selection_basis: str,
    selected_puzzle_ids: list[str],
    source_profile: str,
    puzzle_entries: list[dict[str, Any]],
    provenance_refs: list[str],
    evidence_refs: list[str],
    source_precedence_policy: list[
        Literal[
            "official_toolkit_local_export",
            "repo_frozen_fixture",
            "approved_imported_local_copy",
        ]
    ]
    | None = None,
    no_retrospective_swap_posture: bool = True,
    summary_non_authoritative: bool = True,
) -> dict[str, Any]:
    return derive_v42g1_arc_puzzle_input_bundle(
        selection_register_ref=selection_register_ref,
        selection_basis=selection_basis,
        selected_puzzle_ids=selected_puzzle_ids,
        source_profile=source_profile,
        puzzle_entries=puzzle_entries,
        provenance_refs=provenance_refs,
        evidence_refs=evidence_refs,
        source_precedence_policy=source_precedence_policy,
        no_retrospective_swap_posture=no_retrospective_swap_posture,
        summary_non_authoritative=summary_non_authoritative,
    )
