from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from adeu_concepts import ConceptIR, ConceptQuestion
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode

import adeu_api.main as api_main
from adeu_api.hashing import canonical_json, sha256_canonical_json

DASHBOARD_VERSION = "quality.dashboard.v1"
DEFAULT_QUESTION_REPEATS = 20
DEFAULT_SESSION_STEPS = 10

QUESTIONS_ACTION = "concepts.questions"
TOURNAMENT_REPLAY_ACTION = "concepts.tournament.replay_candidates"
TOURNAMENT_LIVE_ACTION = "concepts.tournament.live_generation"

QUESTIONS_FIXTURE_ROOT = Path("examples/eval/questions")
TOURNAMENT_FIXTURE_ROOT = Path("examples/eval/tournament")


@dataclass(frozen=True)
class EvalFixture:
    name: str
    source_text: str
    ir: ConceptIR
    request: dict[str, Any]


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_fixture(path: Path) -> EvalFixture:
    payload = json.loads(path.read_text(encoding="utf-8"))
    fixture = payload.get("fixture")
    request = payload.get("request")
    if not isinstance(fixture, dict):
        raise ValueError(f"fixture block missing in {path}")
    if not isinstance(request, dict):
        raise ValueError(f"request block missing in {path}")

    root = _repo_root()
    source_text_rel = fixture.get("source_text_path")
    ir_rel = fixture.get("ir_path")
    if not isinstance(source_text_rel, str) or not source_text_rel:
        raise ValueError(f"fixture.source_text_path missing in {path}")
    if not isinstance(ir_rel, str) or not ir_rel:
        raise ValueError(f"fixture.ir_path missing in {path}")

    source_text_path = root / source_text_rel
    ir_path = root / ir_rel
    if not source_text_path.is_file():
        raise FileNotFoundError(f"missing source text: {source_text_path}")
    if not ir_path.is_file():
        raise FileNotFoundError(f"missing ir fixture: {ir_path}")

    source_text = source_text_path.read_text(encoding="utf-8").strip()
    ir = ConceptIR.model_validate(json.loads(ir_path.read_text(encoding="utf-8")))
    return EvalFixture(name=path.name, source_text=source_text, ir=ir, request=request)


def _load_fixtures(relative_dir: Path) -> list[EvalFixture]:
    root = _repo_root()
    directory = root / relative_dir
    if not directory.exists():
        return []
    return [_load_fixture(path) for path in sorted(directory.glob("*.json"))]


def _p95(values: list[float]) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    idx = max(0, math.ceil(0.95 * len(ordered)) - 1)
    return float(ordered[idx])


def _avg(values: list[float | int]) -> float:
    if not values:
        return 0.0
    return float(sum(values)) / len(values)


def _question_signature(response: api_main.ConceptQuestionsResponse) -> str:
    payload = [
        question.model_dump(mode="json", by_alias=True, exclude_none=True)
        for question in response.questions
    ]
    return sha256_canonical_json(payload)


def _question_resolution_key(question: ConceptQuestion, option_id: str) -> str:
    anchor_object_ids = sorted(
        {
            anchor.object_id
            for anchor in question.anchors
            if isinstance(anchor.object_id, str) and anchor.object_id
        }
    )
    anchor_json_paths = sorted(
        {
            anchor.json_path
            for anchor in question.anchors
            if isinstance(anchor.json_path, str) and anchor.json_path
        }
    )
    return sha256_canonical_json(
        {
            "signal_kind": question.signal,
            "anchor_object_ids": anchor_object_ids,
            "anchor_json_paths": anchor_json_paths,
            "selected_option_id": option_id,
        }
    )[:12]


def _make_questions_request(
    fixture: EvalFixture,
    ir: ConceptIR,
) -> api_main.ConceptQuestionsRequest:
    mode = KernelMode(str(fixture.request.get("mode", "LAX")))
    include_forced = bool(fixture.request.get("include_forced_details", False))
    return api_main.ConceptQuestionsRequest(
        ir=ir,
        source_text=fixture.source_text,
        mode=mode,
        include_forced_details=include_forced,
        expected_ir_hash=api_main._concept_ir_hash(ir),
    )


def _make_tournament_request(
    fixture: EvalFixture,
    ir: ConceptIR,
) -> api_main.ConceptTournamentRequest:
    payload = dict(fixture.request)
    payload.setdefault("mode", "LAX")
    payload.setdefault("tournament_mode", "replay_candidates")
    payload.setdefault("provider", "mock")
    payload["ir"] = ir
    payload["source_text"] = fixture.source_text
    payload["expected_ir_hash"] = api_main._concept_ir_hash(ir)
    return api_main.ConceptTournamentRequest.model_validate(payload)


def _simulate_resolved_session(*, fixture: EvalFixture, max_steps: int) -> int:
    current_ir = fixture.ir.model_copy(deep=True)
    mode = KernelMode(str(fixture.request.get("mode", "LAX")))
    include_forced = bool(fixture.request.get("include_forced_details", False))
    resolved_count = 0

    for _ in range(max_steps):
        questions_response = api_main.concept_questions_endpoint(
            _make_questions_request(fixture, current_ir)
        )

        selected_question: ConceptQuestion | None = None
        selected_answer: Any = None
        for question in questions_response.questions:
            for answer in question.answers:
                if answer.patch:
                    selected_question = question
                    selected_answer = answer
                    break
            if selected_answer is not None:
                break

        if selected_question is None or selected_answer is None:
            break

        selected_key = _question_resolution_key(
            selected_question, str(selected_answer.option_id)
        )
        apply_request = api_main.ConceptApplyPatchRequest(
            ir=current_ir,
            ir_hash=api_main._concept_ir_hash(current_ir),
            patch_ops=selected_answer.patch,
            source_text=fixture.source_text,
            mode=mode,
            dry_run=False,
            include_validator_runs=False,
        )
        try:
            apply_response = api_main.apply_concept_patch_endpoint(apply_request)
        except api_main.HTTPException:
            break

        current_ir = apply_response.patched_ir
        after_response = api_main.concept_questions_endpoint(
            api_main.ConceptQuestionsRequest(
                ir=current_ir,
                source_text=fixture.source_text,
                mode=mode,
                include_forced_details=include_forced,
                expected_ir_hash=api_main._concept_ir_hash(current_ir),
            )
        )

        after_keys = {
            _question_resolution_key(question, str(answer.option_id))
            for question in after_response.questions
            for answer in question.answers
        }
        if selected_key not in after_keys:
            resolved_count += 1

    return resolved_count


def build_quality_dashboard(
    *,
    question_repeats: int = DEFAULT_QUESTION_REPEATS,
    session_steps: int = DEFAULT_SESSION_STEPS,
) -> dict[str, Any]:
    question_fixtures = _load_fixtures(QUESTIONS_FIXTURE_ROOT)
    tournament_fixtures = _load_fixtures(TOURNAMENT_FIXTURE_ROOT)
    if not question_fixtures:
        raise RuntimeError("no question eval fixtures found under examples/eval/questions")
    if not tournament_fixtures:
        raise RuntimeError(
            "no tournament eval fixtures found under examples/eval/tournament"
        )

    latency_by_action: dict[str, list[float]] = {
        QUESTIONS_ACTION: [],
        TOURNAMENT_REPLAY_ACTION: [],
        TOURNAMENT_LIVE_ACTION: [],
    }
    solver_calls_by_action: dict[str, list[int]] = {
        QUESTIONS_ACTION: [],
        TOURNAMENT_REPLAY_ACTION: [],
        TOURNAMENT_LIVE_ACTION: [],
    }

    stable_matches = 0
    stable_total = 0
    question_counts: list[int] = []
    resolved_counts: list[int] = []
    question_fixture_details: list[dict[str, Any]] = []

    for fixture in question_fixtures:
        baseline_signature: str | None = None
        baseline_question_count = 0

        for repeat_idx in range(question_repeats):
            ir = fixture.ir.model_copy(deep=True)
            request = _make_questions_request(fixture, ir)

            started = time.perf_counter()
            response = api_main.concept_questions_endpoint(request)
            elapsed_ms = (time.perf_counter() - started) * 1000.0

            latency_by_action[QUESTIONS_ACTION].append(elapsed_ms)
            solver_calls_by_action[QUESTIONS_ACTION].append(
                response.budget_report.used_solver_calls
            )

            signature = _question_signature(response)
            if repeat_idx == 0:
                baseline_signature = signature
                baseline_question_count = response.question_count
                question_counts.append(response.question_count)
            else:
                stable_total += 1
                if signature == baseline_signature:
                    stable_matches += 1

        resolved = _simulate_resolved_session(
            fixture=fixture,
            max_steps=session_steps,
        )
        resolved_counts.append(resolved)
        question_fixture_details.append(
            {
                "fixture": fixture.name,
                "mode": str(fixture.request.get("mode", "LAX")),
                "include_forced_details": bool(
                    fixture.request.get("include_forced_details", False)
                ),
                "question_count": baseline_question_count,
                "resolved_in_session": resolved,
            }
        )

    tournament_fixture_details: list[dict[str, Any]] = []
    for fixture in tournament_fixtures:
        ir = fixture.ir.model_copy(deep=True)
        request = _make_tournament_request(fixture, ir)

        started = time.perf_counter()
        response = api_main.concept_tournament_endpoint(request)
        elapsed_ms = (time.perf_counter() - started) * 1000.0

        action = (
            TOURNAMENT_REPLAY_ACTION
            if response.tournament_mode == "replay_candidates"
            else TOURNAMENT_LIVE_ACTION
        )
        latency_by_action[action].append(elapsed_ms)
        solver_calls_by_action[action].append(response.budget_report.used_solver_calls)

        tournament_fixture_details.append(
            {
                "fixture": fixture.name,
                "mode": str(fixture.request.get("mode", "LAX")),
                "tournament_mode": response.tournament_mode,
                "candidate_count": response.candidate_count,
                "evaluated_count": response.evaluated_count,
                "no_safe_improvement": response.no_safe_improvement,
            }
        )

    all_solver_calls = [
        value for values in solver_calls_by_action.values() for value in values
    ]
    p95_latency_ms = {
        action: round(_p95(values), 3)
        for action, values in latency_by_action.items()
        if values
    }
    avg_latency_ms = {
        action: round(_avg(values), 3)
        for action, values in latency_by_action.items()
        if values
    }
    avg_solver_calls_by_action = {
        action: round(_avg(values), 3)
        for action, values in solver_calls_by_action.items()
        if values
    }

    stability_pct = 100.0 if stable_total == 0 else (stable_matches / stable_total) * 100.0

    dashboard = {
        "dashboard_version": DASHBOARD_VERSION,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "fixture_roots": {
            "questions": str(QUESTIONS_FIXTURE_ROOT),
            "tournament": str(TOURNAMENT_FIXTURE_ROOT),
        },
        "fixture_counts": {
            "questions": len(question_fixtures),
            "tournament": len(tournament_fixtures),
        },
        "metrics": {
            "question_stability_pct": round(stability_pct, 3),
            "avg_questions_per_ir": round(_avg(question_counts), 3),
            "avg_resolved_per_session": round(_avg(resolved_counts), 3),
            "avg_solver_calls_per_action": round(_avg(all_solver_calls), 3),
            "p95_latency_ms": p95_latency_ms,
        },
        "actions": {
            action: {
                "sample_count": len(latency_by_action[action]),
                "avg_latency_ms": avg_latency_ms.get(action, 0.0),
                "p95_latency_ms": p95_latency_ms.get(action, 0.0),
                "avg_solver_calls": avg_solver_calls_by_action.get(action, 0.0),
            }
            for action in sorted(set(latency_by_action) | set(solver_calls_by_action))
            if latency_by_action.get(action) or solver_calls_by_action.get(action)
        },
        "question_fixtures": question_fixture_details,
        "tournament_fixtures": tournament_fixture_details,
        "config": {
            "question_repeats": question_repeats,
            "session_steps": session_steps,
            "question_rank_version": api_main.CONCEPTS_QUESTION_RANK_VERSION,
            "tournament_score_version": api_main.TOURNAMENT_SCORE_VERSION,
            "budget_version": api_main.QUESTIONS_BUDGET_VERSION,
        },
    }
    return json.loads(canonical_json(dashboard))


def write_quality_dashboard(
    output_path: Path,
    *,
    question_repeats: int = DEFAULT_QUESTION_REPEATS,
    session_steps: int = DEFAULT_SESSION_STEPS,
) -> dict[str, Any]:
    dashboard = build_quality_dashboard(
        question_repeats=question_repeats,
        session_steps=session_steps,
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(dashboard, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return dashboard
