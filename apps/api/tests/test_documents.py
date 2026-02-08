from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_api.main import (
    ConceptArtifactCreateRequest,
    ConceptCheckRequest,
    ConceptQuestionsRequest,
    DocumentCreateRequest,
    check_concept_variant,
    concept_questions_endpoint,
    create_concept_artifact_endpoint,
    create_document_endpoint,
    get_document_endpoint,
    list_concept_artifacts_endpoint,
    list_documents_endpoint,
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


def test_documents_create_get_list_and_immutable(monkeypatch, tmp_path: Path) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    first = create_document_endpoint(
        DocumentCreateRequest(
            doc_id="doc:concepts:bank:v1",
            domain="concepts",
            source_text="A bank can refer to a financial institution.",
            metadata={"author": "test"},
        )
    )
    second = create_document_endpoint(
        DocumentCreateRequest(
            doc_id="doc:concepts:bank:v2",
            domain="concepts",
            source_text="A river bank is the land by a river.",
        )
    )

    assert first.doc_id == "doc:concepts:bank:v1"
    assert first.metadata == {"author": "test"}
    assert second.doc_id == "doc:concepts:bank:v2"

    fetched = get_document_endpoint("doc:concepts:bank:v1")
    assert fetched.source_text == "A bank can refer to a financial institution."

    listed = list_documents_endpoint(domain="concepts", limit=50, offset=0)
    listed_ids = {item.doc_id for item in listed.items}
    assert {"doc:concepts:bank:v1", "doc:concepts:bank:v2"}.issubset(listed_ids)

    with pytest.raises(HTTPException) as duplicate_error:
        create_document_endpoint(
            DocumentCreateRequest(
                doc_id="doc:concepts:bank:v1",
                domain="concepts",
                source_text="changed text",
            )
        )
    assert duplicate_error.value.status_code == 409
    assert duplicate_error.value.detail["code"] == "DOC_ALREADY_EXISTS"


def test_doc_id_authoritative_and_mismatch_guard(monkeypatch, tmp_path: Path) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    source_text = _fixture_source()
    create_document_endpoint(
        DocumentCreateRequest(
            doc_id="doc:concepts:fixture",
            domain="concepts",
            source_text=source_text,
        )
    )
    concept = _coherent_ir()

    with pytest.raises(HTTPException) as mismatch_error:
        check_concept_variant(
            ConceptCheckRequest(
                ir=concept,
                doc_id="doc:concepts:fixture",
                source_text="this text does not match the stored document",
                mode=KernelMode.LAX,
            )
        )
    assert mismatch_error.value.status_code == 400
    assert mismatch_error.value.detail["code"] == "DOC_TEXT_MISMATCH"

    from_doc = check_concept_variant(
        ConceptCheckRequest(
            ir=concept,
            doc_id="doc:concepts:fixture",
            mode=KernelMode.LAX,
        )
    )
    from_text = check_concept_variant(
        ConceptCheckRequest(
            ir=concept,
            source_text=source_text,
            mode=KernelMode.LAX,
        )
    )
    assert from_doc == from_text


def test_doc_id_source_used_for_provenance_span_bounds(monkeypatch, tmp_path: Path) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    create_document_endpoint(
        DocumentCreateRequest(
            doc_id="doc:concepts:short",
            domain="concepts",
            source_text="short text",
        )
    )

    base = _coherent_ir()
    first_claim = base.claims[0]
    first_provenance = first_claim.provenance
    assert first_provenance is not None
    assert first_provenance.span is not None
    stretched_claim = first_claim.model_copy(
        update={
            "provenance": first_provenance.model_copy(
                update={
                    "span": first_provenance.span.model_copy(
                        update={"start": 0, "end": 999}
                    )
                }
            )
        }
    )
    concept = base.model_copy(update={"claims": [stretched_claim, *base.claims[1:]]})

    without_source = check_concept_variant(ConceptCheckRequest(ir=concept, mode=KernelMode.LAX))
    with_doc = check_concept_variant(
        ConceptCheckRequest(ir=concept, doc_id="doc:concepts:short", mode=KernelMode.LAX)
    )

    assert not any("out of bounds" in reason.message for reason in without_source.reason_codes)
    assert any("out of bounds" in reason.message for reason in with_doc.reason_codes)


def test_concept_endpoints_accept_doc_id_without_source_text(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    source_text = _fixture_source()
    doc_id = "doc:concepts:artifact"
    create_document_endpoint(
        DocumentCreateRequest(
            doc_id=doc_id,
            domain="concepts",
            source_text=source_text,
        )
    )

    base_ir = _coherent_ir()
    concept = base_ir.model_copy(
        update={
            "context": base_ir.context.model_copy(
                update={"doc_id": "doc:concepts:different-context"}
            )
        }
    )

    artifact = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=None,
            doc_id=doc_id,
            ir=concept,
            mode=KernelMode.LAX,
        )
    )
    listed = list_concept_artifacts_endpoint(doc_id=doc_id, limit=50, offset=0)
    assert any(item.artifact_id == artifact.artifact_id for item in listed.items)

    from_doc = concept_questions_endpoint(
        ConceptQuestionsRequest(
            ir=concept,
            doc_id=doc_id,
            mode=KernelMode.LAX,
            include_forced_details=True,
        )
    )
    from_text = concept_questions_endpoint(
        ConceptQuestionsRequest(
            ir=concept,
            source_text=source_text,
            mode=KernelMode.LAX,
            include_forced_details=True,
        )
    )
    assert from_doc.question_count == from_text.question_count
