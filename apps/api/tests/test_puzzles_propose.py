from __future__ import annotations

import os
from datetime import datetime, timezone
from pathlib import Path

import pytest
from adeu_api.main import PuzzleProposeRequest, propose_puzzle
from adeu_api.openai_puzzle_provider import PuzzleProposerLog
from adeu_api.scoring import ranking_sort_key, score_key
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode


def _fixture_puzzle_text(*, name: str) -> str:
    root = repo_root(anchor=Path(__file__))
    puzzle_path = root / "examples" / "puzzles" / "fixtures" / name / "puzzle.txt"
    return puzzle_path.read_text(encoding="utf-8").strip()


def test_puzzles_propose_mock_returns_ranked_candidates_with_reports() -> None:
    puzzle_text = _fixture_puzzle_text(name="knights_knaves_basic")
    resp = propose_puzzle(
        PuzzleProposeRequest(
            puzzle_text=puzzle_text,
            provider="mock",
            mode=KernelMode.STRICT,
        )
    )

    assert resp.provider.kind == "mock"
    assert resp.provider.api == "mock"
    assert len(resp.candidates) == 2
    assert resp.candidates[0].rank == 0
    assert resp.candidates[0].ir.puzzle_id == "fixture_sat_two_person"
    assert [candidate.check_report.status for candidate in resp.candidates] == ["PASS", "REFUSE"]

    # Canonicalized IDs keep diffs and atom mapping deterministic.
    assert [person.id for person in resp.candidates[0].ir.people] == ["p1", "p2"]
    assert [statement.id for statement in resp.candidates[0].ir.statements] == ["s1", "s2"]
    assert [assumption.id for assumption in resp.candidates[0].ir.assumptions] == ["a1"]

    actual_order = [(score_key(c.check_report), c.ir.puzzle_id) for c in resp.candidates]
    expected_order = sorted(actual_order, key=lambda item: ranking_sort_key(item[0], item[1]))
    assert actual_order == expected_order

    assert resp.proposer_log.source_features is not None
    assert resp.proposer_log.source_features["mentions_knight"] is True
    assert resp.proposer_log.source_features["mentions_knave"] is True


def test_puzzles_propose_mock_unknown_text_returns_empty() -> None:
    resp = propose_puzzle(
        PuzzleProposeRequest(
            puzzle_text="This puzzle text does not exist in fixtures.",
            provider="mock",
            mode=KernelMode.LAX,
        )
    )
    assert resp.provider.kind == "mock"
    assert resp.candidates == []


def test_puzzles_propose_codex_provider_branch(monkeypatch: pytest.MonkeyPatch) -> None:
    puzzle_text = _fixture_puzzle_text(name="knights_knaves_basic")

    def _fake_propose_puzzle_codex(**kwargs):
        del kwargs
        return (
            [],
            PuzzleProposerLog(
                provider="codex",
                api="codex_exec",
                model="codex-cli-default",
                created_at=datetime.now(tz=timezone.utc).isoformat(),
                k=1,
                n=1,
                source_features={},
                attempts=[],
            ),
            "codex-cli-default",
        )

    monkeypatch.setattr(
        "adeu_api.openai_puzzle_provider.propose_puzzle_codex",
        _fake_propose_puzzle_codex,
    )
    resp = propose_puzzle(
        PuzzleProposeRequest(
            puzzle_text=puzzle_text,
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
    reason="OPENAI_API_KEY not set; skipping OpenAI puzzle propose smoke test",
)
def test_puzzles_propose_openai_smoke() -> None:
    puzzle_text = _fixture_puzzle_text(name="knights_knaves_basic")
    resp = propose_puzzle(
        PuzzleProposeRequest(
            puzzle_text=puzzle_text,
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
