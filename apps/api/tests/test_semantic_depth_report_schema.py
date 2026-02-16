from __future__ import annotations

import json
from pathlib import Path

from adeu_concepts import ConceptIR
from adeu_semantic_depth import build_semantic_depth_report_from_concept_pair
from jsonschema import Draft202012Validator


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _load_schema() -> dict[str, object]:
    schema_path = _repo_root() / "spec" / "semantic_depth_report.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


def _concept_ir(doc_id: str, *, gloss: str, claim_text: str, link_kind: str) -> ConceptIR:
    return ConceptIR.model_validate(
        {
            "schema_version": "adeu.concepts.v0",
            "concept_id": f"concept:{doc_id}",
            "context": {"doc_id": doc_id},
            "terms": [{"id": "term_pay", "label": "Payment"}],
            "senses": [{"id": "sense_pay", "term_id": "term_pay", "gloss": gloss}],
            "claims": [{"id": "claim_pay", "sense_id": "sense_pay", "text": claim_text}],
            "links": [
                {
                    "id": "link_pay",
                    "kind": link_kind,
                    "src_sense_id": "sense_pay",
                    "dst_sense_id": "sense_pay",
                }
            ],
        }
    )


def test_semantic_depth_schema_accepts_normalized_payload() -> None:
    payload = build_semantic_depth_report_from_concept_pair(
        left_ir=_concept_ir(
            "doc:left",
            gloss="pay within 5 days",
            claim_text="must pay in 5 days",
            link_kind="incompatibility",
        ),
        right_ir=_concept_ir(
            "doc:right",
            gloss="pay within 10 days",
            claim_text="must pay in 10 days",
            link_kind="commitment",
        ),
        input_artifact_refs=["artifact:left", "artifact:right"],
    )
    validator = Draft202012Validator(_load_schema())
    errors = sorted(validator.iter_errors(payload), key=lambda err: err.path)
    assert errors == []
