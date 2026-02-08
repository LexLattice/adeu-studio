from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_api.main import (
    ConceptAlignRequest,
    ConceptArtifactCreateRequest,
    align_concepts_endpoint,
    create_concept_artifact_endpoint,
)
from adeu_concepts import ConceptIR
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode
from fastapi import HTTPException


def _fixture_payload(name: str) -> dict:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / "bank_sense_coherence" / "proposals" / name
    return json.loads(path.read_text(encoding="utf-8"))


def _fixture_source() -> str:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / "bank_sense_coherence" / "source.txt"
    return path.read_text(encoding="utf-8").strip()


def _coherent_ir() -> ConceptIR:
    return ConceptIR.model_validate(_fixture_payload("var1.json"))


def test_concepts_align_is_deterministic_and_emits_merge_candidate(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    source_text = _fixture_source()
    base = _coherent_ir()
    left_ir = base.model_copy(
        update={
            "concept_id": "concept_align_left",
            "context": base.context.model_copy(update={"doc_id": "doc:align:left"}),
        }
    )
    right_ir = base.model_copy(
        update={
            "concept_id": "concept_align_right",
            "context": base.context.model_copy(update={"doc_id": "doc:align:right"}),
        }
    )

    left = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=source_text,
            ir=left_ir,
            mode=KernelMode.LAX,
        )
    )
    right = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=source_text,
            ir=right_ir,
            mode=KernelMode.LAX,
        )
    )

    one = align_concepts_endpoint(
        ConceptAlignRequest(
            artifact_ids=[right.artifact_id, left.artifact_id],
            max_suggestions=50,
        )
    )
    two = align_concepts_endpoint(
        ConceptAlignRequest(
            artifact_ids=[left.artifact_id, right.artifact_id],
            max_suggestions=50,
        )
    )

    assert one == two
    assert one.alignment_stats.merge_candidate_count >= 1
    assert one.alignment_stats.conflict_candidate_count >= 0
    merge_keys = {item.vocabulary_key for item in one.suggestions if item.kind == "merge_candidate"}
    assert "bank" in merge_keys
    assert all(len(item.suggestion_fingerprint) == 12 for item in one.suggestions)
    assert all(item.suggestion_fingerprint for item in one.suggestions)


def test_concepts_align_emits_conflict_candidate_for_divergent_glosses(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    source_text = _fixture_source()
    base = _coherent_ir()
    left_ir = base.model_copy(
        update={
            "concept_id": "concept_align_conflict_left",
            "context": base.context.model_copy(update={"doc_id": "doc:align:conflict:left"}),
        }
    )

    changed_senses = []
    for sense in base.senses:
        if sense.id == "s_bank_fin":
            changed_senses.append(sense.model_copy(update={"gloss": "shoreline formation"}))
        else:
            changed_senses.append(sense)
    right_ir = base.model_copy(
        update={
            "concept_id": "concept_align_conflict_right",
            "context": base.context.model_copy(update={"doc_id": "doc:align:conflict:right"}),
            "senses": changed_senses,
        }
    )

    left = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=source_text,
            ir=left_ir,
            mode=KernelMode.LAX,
        )
    )
    right = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=source_text,
            ir=right_ir,
            mode=KernelMode.LAX,
        )
    )

    aligned = align_concepts_endpoint(
        ConceptAlignRequest(
            artifact_ids=[left.artifact_id, right.artifact_id],
            max_suggestions=50,
        )
    )

    conflict_keys = {
        item.vocabulary_key for item in aligned.suggestions if item.kind == "conflict_candidate"
    }
    assert "bank" in conflict_keys
    assert aligned.alignment_stats.conflict_candidate_count >= 1


def test_concepts_align_doc_scope_and_missing_errors(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    source_text = _fixture_source()
    base = _coherent_ir()
    scoped_ir = base.model_copy(
        update={
            "concept_id": "concept_align_scope",
            "context": base.context.model_copy(update={"doc_id": "doc:align:scope"}),
        }
    )
    created = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=source_text,
            ir=scoped_ir,
            mode=KernelMode.LAX,
        )
    )

    scoped = align_concepts_endpoint(
        ConceptAlignRequest(
            doc_ids=["doc:align:scope"],
            max_suggestions=50,
        )
    )
    assert [item.artifact_id for item in scoped.artifacts] == [created.artifact_id]
    assert scoped.suggestion_count == 0

    with pytest.raises(HTTPException) as missing_doc_error:
        align_concepts_endpoint(
            ConceptAlignRequest(
                doc_ids=["doc:align:missing"],
            )
        )
    assert missing_doc_error.value.status_code == 404
    assert missing_doc_error.value.detail["code"] == "ALIGNMENT_DOC_NO_ARTIFACT"

    with pytest.raises(HTTPException) as missing_artifact_error:
        align_concepts_endpoint(
            ConceptAlignRequest(
                artifact_ids=["artifact-does-not-exist"],
            )
        )
    assert missing_artifact_error.value.status_code == 404
    assert missing_artifact_error.value.detail["code"] == "ALIGNMENT_ARTIFACT_NOT_FOUND"


def test_concepts_align_mixed_scope_uses_doc_latest_and_union(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    source_text = _fixture_source()
    base = _coherent_ir()
    left_doc_old = base.model_copy(
        update={
            "concept_id": "concept_align_mixed_left_old",
            "context": base.context.model_copy(update={"doc_id": "doc:align:mixed:left"}),
        }
    )
    left_doc_latest = base.model_copy(
        update={
            "concept_id": "concept_align_mixed_left_latest",
            "context": base.context.model_copy(update={"doc_id": "doc:align:mixed:left"}),
        }
    )
    explicit_doc = base.model_copy(
        update={
            "concept_id": "concept_align_mixed_explicit",
            "context": base.context.model_copy(update={"doc_id": "doc:align:mixed:explicit"}),
        }
    )

    left_old = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=source_text,
            ir=left_doc_old,
            mode=KernelMode.LAX,
        )
    )
    left_latest = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=source_text,
            ir=left_doc_latest,
            mode=KernelMode.LAX,
        )
    )
    explicit = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=source_text,
            ir=explicit_doc,
            mode=KernelMode.LAX,
        )
    )

    aligned = align_concepts_endpoint(
        ConceptAlignRequest(
            doc_ids=["doc:align:mixed:left"],
            artifact_ids=[explicit.artifact_id],
            max_suggestions=50,
        )
    )
    aligned_ids = [item.artifact_id for item in aligned.artifacts]
    assert aligned_ids == sorted([left_latest.artifact_id, explicit.artifact_id])
    assert left_old.artifact_id not in aligned_ids


def test_concepts_align_scope_too_large_error(monkeypatch, tmp_path: Path) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    oversized_scope = [f"artifact_{idx:03d}" for idx in range(201)]
    with pytest.raises(HTTPException) as scope_error:
        align_concepts_endpoint(ConceptAlignRequest(artifact_ids=oversized_scope))

    assert scope_error.value.status_code == 400
    assert scope_error.value.detail["code"] == "ALIGNMENT_SCOPE_TOO_LARGE"
    assert scope_error.value.detail["max_artifacts"] == 200
    assert scope_error.value.detail["actual_artifacts"] == 201
