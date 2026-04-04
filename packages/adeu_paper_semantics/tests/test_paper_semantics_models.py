from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_paper_semantics import (
    INTERPRETATION_AUTHORITY_POSTURE,
    SOURCE_AUTHORITY_POSTURE,
    PaperSemanticArtifact,
    PaperSemanticWorkerRequest,
)
from pydantic import ValidationError

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v52a"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


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


@pytest.mark.parametrize(
    "fixture_name, model",
    [
        ("reject_invalid_diagnostic_kind.json", PaperSemanticArtifact),
        ("reject_malformed_span_anchor.json", PaperSemanticArtifact),
        ("reject_invalid_worker_request_posture.json", PaperSemanticWorkerRequest),
    ],
)
def test_reject_fixtures_fail_closed(fixture_name: str, model: type[object]) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_json(fixture_name))  # type: ignore[attr-defined]
