from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from adeu_arc_solver import derive_v42g1_puzzle_input_bundle
from adeu_ir.repo import repo_root


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_solver_helper_replays_v95_reference_bundle() -> None:
    root = _repo_root()
    bundle = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus95"
        / "adeu_arc_puzzle_input_bundle_v95_reference.json"
    )
    entry_inputs: list[dict[str, Any]] = []
    for entry in bundle["puzzle_entries"]:
        entry_inputs.append(
            {
                "puzzle_id": entry["puzzle_id"],
                "source_kind": entry["source_kind"],
                "source_ref": entry["source_ref"],
                "normalized_payload_ref": entry["normalized_payload_ref"],
                "normalized_payload": entry["normalized_payload"],
                "provenance_refs": entry["provenance_refs"],
            }
        )

    derived = derive_v42g1_puzzle_input_bundle(
        selection_register_ref=bundle["selection_register_ref"],
        selection_basis=bundle["selection_basis"],
        selected_puzzle_ids=bundle["selected_puzzle_ids"],
        source_profile=bundle["source_profile"],
        puzzle_entries=entry_inputs,
        provenance_refs=bundle["provenance_refs"],
        evidence_refs=bundle["evidence_refs"],
        source_precedence_policy=bundle["source_precedence_policy"],
        no_retrospective_swap_posture=bundle["no_retrospective_swap_posture"],
        summary_non_authoritative=bundle["summary_non_authoritative"],
    )

    assert derived == bundle
