from __future__ import annotations

import os
from datetime import datetime, timezone
from pathlib import Path

import pytest
from adeu_api.main import ProposeRequest, propose
from adeu_api.openai_provider import ProposerLog as OpenAIProposerLog
from adeu_api.scoring import ranking_sort_key, score_key
from adeu_ir import Context
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode


def _fixture_clause(*, name: str) -> str:
    root = repo_root(anchor=Path(__file__))
    clause_path = root / "examples" / "fixtures" / name / "clause.txt"
    return clause_path.read_text(encoding="utf-8").strip()


def test_propose_mock_returns_checked_candidates() -> None:
    clause = _fixture_clause(name="modality_requires_ambiguity")
    resp = propose(
        ProposeRequest(
            clause_text=clause,
            provider="mock",
            mode=KernelMode.LAX,
        )
    )

    assert resp.provider.kind == "mock"
    assert resp.provider.api == "mock"
    assert resp.candidates, "Expected at least one fixture-backed candidate"
    assert resp.candidates[0].rank == 0
    for candidate in resp.candidates:
        assert candidate.check_report.status in {"PASS", "WARN", "REFUSE"}
        assert candidate.check_report.metrics.num_statements >= 0
        assert candidate.check_report.metrics.num_bridges >= 0

    # API should deterministically populate source_features from the clause text.
    modals = resp.candidates[0].ir.context.source_features.modals
    assert modals == ["may"]
    assert resp.proposer_log.source_features is not None
    assert resp.proposer_log.source_features.get("modals") == ["may"]

    assert resp.proposer_log.provider == "mock"
    assert resp.proposer_log.attempts, "Mock proposer should emit attempt summaries"


def test_propose_mock_uses_canonical_score_for_ranking_and_logs() -> None:
    clause = _fixture_clause(name="modality_requires_ambiguity")
    resp = propose(
        ProposeRequest(
            clause_text=clause,
            provider="mock",
            mode=KernelMode.LAX,
        )
    )

    actual_order = [(score_key(c.check_report), c.ir.ir_id) for c in resp.candidates]
    expected_order = sorted(
        actual_order,
        key=lambda item: ranking_sort_key(item[0], item[1]),
    )
    assert actual_order == expected_order

    for attempt, candidate in zip(resp.proposer_log.attempts, resp.candidates, strict=True):
        assert attempt.score_key == score_key(candidate.check_report)
        assert attempt.candidate_rank == candidate.rank


def test_propose_mock_respects_context_but_overwrites_source_features() -> None:
    clause = _fixture_clause(name="modality_requires_ambiguity")
    ctx = Context(
        doc_id="doc:custom",
        jurisdiction="US-NY",
        time_eval=datetime(2026, 2, 5, tzinfo=timezone.utc),
        source_features={"modals": ["shall"]},
    )
    resp = propose(
        ProposeRequest(
            clause_text=clause,
            provider="mock",
            mode=KernelMode.LAX,
            context=ctx,
        )
    )
    assert resp.candidates
    assert resp.candidates[0].ir.context.doc_id == "doc:custom"
    assert resp.candidates[0].ir.context.jurisdiction == "US-NY"
    assert resp.candidates[0].ir.context.time_eval == ctx.time_eval

    # But source_features is deterministic from the clause text.
    assert resp.candidates[0].ir.context.source_features.modals == ["may"]
    assert resp.proposer_log.source_features is not None
    assert resp.proposer_log.source_features.get("modals") == ["may"]


def test_propose_mock_unknown_clause_returns_empty() -> None:
    resp = propose(
        ProposeRequest(
            clause_text="This is not a fixture clause.",
            provider="mock",
            mode=KernelMode.LAX,
        )
    )
    assert resp.candidates == []


def test_propose_codex_provider_branch(monkeypatch: pytest.MonkeyPatch) -> None:
    clause = _fixture_clause(name="modality_requires_ambiguity")

    def _fake_propose_codex(**kwargs):
        del kwargs
        return (
            [],
            OpenAIProposerLog(
                provider="codex",
                api="codex_exec",
                model="codex-cli-default",
                created_at=datetime.now(tz=timezone.utc).isoformat(),
                k=1,
                n=1,
                attempts=[],
            ),
            "codex-cli-default",
        )

    monkeypatch.setattr("adeu_api.openai_provider.propose_codex", _fake_propose_codex)
    resp = propose(
        ProposeRequest(
            clause_text=clause,
            provider="codex",
            mode=KernelMode.LAX,
            max_candidates=1,
            max_repairs=1,
        )
    )

    assert resp.provider.kind == "codex"
    assert resp.provider.api == "codex_exec"
    assert resp.provider.model == "codex-cli-default"


@pytest.mark.skipif(
    not os.environ.get("OPENAI_API_KEY"),
    reason="OPENAI_API_KEY not set; skipping OpenAI smoke test",
)
def test_propose_openai_smoke() -> None:
    clause = _fixture_clause(name="modality_requires_ambiguity")
    resp = propose(
        ProposeRequest(
            clause_text=clause,
            provider="openai",
            mode=KernelMode.LAX,
            max_candidates=1,
            max_repairs=1,
        )
    )
    assert resp.provider.kind == "openai"
    assert resp.provider.api in {"responses", "chat"}
    assert resp.proposer_log is not None

    # Logging should be minimal by default (raw logs are opt-in via ADEU_LOG_RAW_LLM=1).
    assert resp.proposer_log.raw_prompt is None
    assert resp.proposer_log.raw_response is None
    if resp.candidates:
        for candidate in resp.candidates:
            assert candidate.check_report.status in {"PASS", "WARN", "REFUSE"}
            assert candidate.check_report.metrics.num_statements >= 0
    else:
        assert resp.proposer_log.attempts
