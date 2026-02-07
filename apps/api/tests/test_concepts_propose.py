from __future__ import annotations

import os
from pathlib import Path

import pytest
from adeu_api.main import ConceptProposeRequest, propose_concept
from adeu_api.scoring import ranking_sort_key, score_key
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode


def _fixture_source_text(*, name: str) -> str:
    root = repo_root(anchor=Path(__file__))
    source_path = root / "examples" / "concepts" / "fixtures" / name / "source.txt"
    return source_path.read_text(encoding="utf-8").strip()


def test_concepts_propose_mock_returns_ranked_candidates_with_reports() -> None:
    source_text = _fixture_source_text(name="bank_sense_coherence")
    resp = propose_concept(
        ConceptProposeRequest(
            source_text=source_text,
            provider="mock",
            mode=KernelMode.STRICT,
        )
    )

    assert resp.provider.kind == "mock"
    assert resp.provider.api == "mock"
    assert len(resp.candidates) == 2
    assert [candidate.check_report.status for candidate in resp.candidates] == ["PASS", "REFUSE"]
    assert [candidate.rank for candidate in resp.candidates] == [0, 1]

    first = resp.candidates[0].ir
    assert [term.id for term in first.terms] == ["term_1", "term_2"]
    assert [sense.id for sense in first.senses] == ["sense_1", "sense_2", "sense_3"]
    assert [claim.id for claim in first.claims] == ["claim_1"]
    assert [link.id for link in first.links] == ["link_1", "link_2"]
    assert [ambiguity.id for ambiguity in first.ambiguity] == ["amb_1"]

    actual_order = [
        (score_key(candidate.check_report), candidate.ir.concept_id)
        for candidate in resp.candidates
    ]
    expected_order = sorted(actual_order, key=lambda item: ranking_sort_key(item[0], item[1]))
    assert actual_order == expected_order

    assert resp.proposer_log.source_features is not None
    assert resp.proposer_log.source_features["has_ambiguity_cue"] is True


def test_concepts_propose_mock_unknown_text_returns_empty() -> None:
    resp = propose_concept(
        ConceptProposeRequest(
            source_text="This source text does not exist in concept fixtures.",
            provider="mock",
            mode=KernelMode.LAX,
        )
    )
    assert resp.provider.kind == "mock"
    assert resp.candidates == []


@pytest.mark.skipif(
    not os.environ.get("OPENAI_API_KEY"),
    reason="OPENAI_API_KEY not set; skipping OpenAI concept propose smoke test",
)
def test_concepts_propose_openai_smoke() -> None:
    source_text = _fixture_source_text(name="bank_sense_coherence")
    resp = propose_concept(
        ConceptProposeRequest(
            source_text=source_text,
            provider="openai",
            mode=KernelMode.LAX,
            max_candidates=1,
            max_repairs=1,
        )
    )

    assert resp.provider.kind == "openai"
    assert resp.provider.api in {"responses", "chat"}
    assert resp.proposer_log is not None
    assert resp.proposer_log.source_features is not None
    assert resp.proposer_log.raw_prompt is None
    assert resp.proposer_log.raw_response is None
    if resp.candidates:
        for candidate in resp.candidates:
            assert candidate.check_report.status in {"PASS", "WARN", "REFUSE"}
            assert candidate.check_report.metrics.num_statements >= 0
    else:
        assert resp.proposer_log.attempts
