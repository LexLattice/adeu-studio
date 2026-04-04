from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_paper_semantics import (
    INTERPRETATION_AUTHORITY_POSTURE,
    SOURCE_AUTHORITY_POSTURE,
    PaperSemanticArtifact,
    PaperSemanticWorkerRequest,
    compute_paper_artifact_id,
)
from adeu_semantic_forms import sha256_canonical_json
from pydantic import ValidationError

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v52a"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _recompute_artifact_identity(payload: dict[str, object]) -> None:
    basis = {
        "schema": payload["schema"],
        "source": {
            "artifact_kind": payload["source"]["artifact_kind"],
            "paragraph_index": payload["source"].get("paragraph_index"),
            "source_text_hash": payload["source"]["source_text_hash"],
        },
        "spans": [
            {
                "start": item["start"],
                "end": item["end"],
                "quote": item["quote"],
                "sentence_index": item["sentence_index"],
                "paragraph_index": item["paragraph_index"],
            }
            for item in sorted(
                payload["spans"],
                key=lambda item: (item["start"], item["end"], item["span_id"]),
            )
        ],
        "claims": [
            {
                "claim_text": item["claim_text"],
                "lane_fragment_ids": item["lane_fragment_ids"],
                "span_ids": item["span_ids"],
                "status": item["status"],
            }
            for item in sorted(payload["claims"], key=lambda item: item["claim_id"])
        ],
        "lane_fragments": [
            {
                "bridge_ids": item["bridge_ids"],
                "claim_id": item["claim_id"],
                "fragment_text": item["fragment_text"],
                "lane_id": item["lane_id"],
                "source_kind": item["source_kind"],
                "span_ids": item["span_ids"],
                "status": item["status"],
            }
            for item in sorted(
                payload["lane_fragments"],
                key=lambda item: (item["claim_id"], item["lane_id"], item["fragment_id"]),
            )
        ],
        "inference_bridges": [
            {
                "bridge_kind": item["bridge_kind"],
                "from_fragment_ids": item["from_fragment_ids"],
                "to_fragment_ids": item["to_fragment_ids"],
            }
            for item in sorted(payload["inference_bridges"], key=lambda item: item["bridge_id"])
        ],
        "source_authority_posture": payload["source_authority_posture"],
        "interpretation_authority_posture": payload["interpretation_authority_posture"],
        "semantic_identity_mode": payload["semantic_identity_mode"],
    }
    semantic_hash = sha256_canonical_json(basis)
    payload["semantic_hash"] = semantic_hash
    payload["artifact_id"] = compute_paper_artifact_id(semantic_hash)


def test_reference_worker_requests_validate() -> None:
    abstract_request = PaperSemanticWorkerRequest.model_validate(
        _load_json("reference_paper_semantic_worker_request_abstract.json")
    )
    paragraph_request = PaperSemanticWorkerRequest.model_validate(
        _load_json("reference_paper_semantic_worker_request_paragraph.json")
    )

    assert abstract_request.source_kind == "paper.abstract"
    assert paragraph_request.source_kind == "pasted.paragraph"
    assert abstract_request.operator_posture.analysis_mode == "evidence-first"
    assert paragraph_request.operator_posture.authority_mode == "advisory-only"


def test_reference_artifacts_validate() -> None:
    abstract_artifact = PaperSemanticArtifact.model_validate(
        _load_json("reference_paper_semantic_artifact_abstract.json")
    )
    paragraph_artifact = PaperSemanticArtifact.model_validate(
        _load_json("reference_paper_semantic_artifact_paragraph.json")
    )

    assert abstract_artifact.source_authority_posture == SOURCE_AUTHORITY_POSTURE
    assert paragraph_artifact.interpretation_authority_posture == INTERPRETATION_AUTHORITY_POSTURE
    assert abstract_artifact.source.artifact_kind == "paper.abstract"
    assert paragraph_artifact.source.artifact_kind == "pasted.paragraph"


def test_projection_only_mutation_preserves_semantic_hash() -> None:
    reference_artifact = PaperSemanticArtifact.model_validate(
        _load_json("reference_paper_semantic_artifact_abstract.json")
    )
    projection_only_artifact = PaperSemanticArtifact.model_validate(
        _load_json("mutation_paper_semantic_artifact_projection_only.json")
    )

    assert projection_only_artifact.semantic_hash == reference_artifact.semantic_hash
    assert projection_only_artifact.artifact_id == reference_artifact.artifact_id


def test_identity_change_mutation_changes_semantic_hash() -> None:
    reference_artifact = PaperSemanticArtifact.model_validate(
        _load_json("reference_paper_semantic_artifact_abstract.json")
    )
    identity_change_artifact = PaperSemanticArtifact.model_validate(
        _load_json("mutation_paper_semantic_artifact_identity_change.json")
    )

    assert identity_change_artifact.semantic_hash != reference_artifact.semantic_hash
    assert identity_change_artifact.artifact_id != reference_artifact.artifact_id


def test_claim_fragment_ownership_must_be_bidirectionally_consistent() -> None:
    payload = _load_json("reference_paper_semantic_artifact_abstract.json")
    assert isinstance(payload, dict)

    second_claim = dict(payload["claims"][0])
    second_claim["claim_text"] = "Secondary claim about transparent evidence practice."
    second_claim["lane_fragment_ids"] = [payload["lane_fragments"][0]["fragment_id"]]
    second_claim["span_ids"] = [payload["spans"][0]["span_id"]]
    second_claim["claim_id"] = (
        "claim:"
        + sha256_canonical_json(
            {
                "claim_text": second_claim["claim_text"],
                "lane_fragment_ids": second_claim["lane_fragment_ids"],
                "span_ids": second_claim["span_ids"],
                "status": second_claim["status"],
            }
        )[:16]
    )

    payload["claims"].append(second_claim)
    payload["lane_fragments"][0]["claim_id"] = second_claim["claim_id"]
    _recompute_artifact_identity(payload)

    with pytest.raises(ValidationError):
        PaperSemanticArtifact.model_validate(payload)


@pytest.mark.parametrize(
    "fixture_name, model",
    [
        ("reject_invalid_diagnostic_kind.json", PaperSemanticArtifact),
        ("reject_malformed_span_anchor.json", PaperSemanticArtifact),
        ("reject_invalid_worker_request_posture.json", PaperSemanticWorkerRequest),
    ],
)
def test_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[PaperSemanticArtifact] | type[PaperSemanticWorkerRequest],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_json(fixture_name))
