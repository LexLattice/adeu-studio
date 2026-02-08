from __future__ import annotations

import json
from pathlib import Path

from adeu_api.concept_id_canonicalization import canonicalize_concept_ids
from adeu_concepts import ConceptIR
from adeu_ir.models import JsonPatchOp
from adeu_ir.repo import repo_root


def _fixture_payload(name: str) -> dict:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / "bank_sense_coherence" / "proposals" / name
    return json.loads(path.read_text(encoding="utf-8"))


def test_concept_canonicalization_remaps_ambiguity_option_metadata() -> None:
    concept = ConceptIR.model_validate(_fixture_payload("var1.json"))
    ambiguity = concept.ambiguity[0]
    option = ambiguity.option_details_by_id["s_bank_fin"].model_copy(
        update={
            "patch": [
                JsonPatchOp(op="replace", path="/claims/0/sense_id", value="s_bank_river"),
            ]
        }
    )
    ambiguity = ambiguity.model_copy(
        update={
            "option_details_by_id": {
                "s_bank_fin": option,
                "s_bank_river": ambiguity.option_details_by_id["s_bank_river"],
            }
        }
    )
    concept = concept.model_copy(update={"ambiguity": [ambiguity]})

    canonical = canonicalize_concept_ids(concept)
    canonical_ambiguity = canonical.ambiguity[0]
    assert canonical_ambiguity.options == ["sense_1", "sense_2"]
    assert set(canonical_ambiguity.option_details_by_id.keys()) == {"sense_1", "sense_2"}
    assert canonical_ambiguity.option_details_by_id["sense_1"].option_id == "sense_1"
    assert canonical_ambiguity.option_labels_by_id is not None
    assert set(canonical_ambiguity.option_labels_by_id.keys()) == {"sense_1", "sense_2"}
    assert (
        canonical_ambiguity.option_details_by_id["sense_1"].patch[0].value
        == "sense_2"
    )
