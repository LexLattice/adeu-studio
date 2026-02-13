from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from adeu_concepts import ConceptIR, ConceptQuestion
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode

import adeu_api.main as api_main
from adeu_api.concepts_coherence import build_concepts_coherence_artifact
from adeu_api.hashing import canonical_json, sha256_canonical_json

DASHBOARD_VERSION = "quality.dashboard.v1"
DELTA_REPORT_VERSION = "quality.dashboard.delta.v1"
INPUT_MANIFEST_VERSION = "quality.dashboard.inputs.v1"
DETERMINISTIC_EVALUATION_TS = "1970-01-01T00:00:00Z"
DEFAULT_QUESTION_REPEATS = 20
DEFAULT_SESSION_STEPS = 10

QUESTIONS_ACTION = "concepts.questions"
TOURNAMENT_REPLAY_ACTION = "concepts.tournament.replay_candidates"
TOURNAMENT_LIVE_ACTION = "concepts.tournament.live_generation"

QUESTIONS_FIXTURE_ROOT = Path("examples/eval/questions")
TOURNAMENT_FIXTURE_ROOT = Path("examples/eval/tournament")

FROZEN_QUALITY_METRIC_RULES: dict[str, str] = {
    "redundancy_rate": "non_increasing",
    "top_k_stability@10": "non_decreasing",
    "evidence_coverage_rate": "non_decreasing",
    "bridge_loss_utilization_rate": "non_decreasing",
    "coherence_alert_count": "non_increasing",
}


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


def _question_dedupe_signature(question: ConceptQuestion) -> str:
    signal, target_entity_ids, polarity, normalized_text_hash = api_main._question_dedupe_key(
        question
    )
    payload = {
        "question_type": signal,
        "target_entity_ids_canonical": list(target_entity_ids),
        "polarity": polarity,
        "normalized_text_hash": normalized_text_hash,
    }
    return sha256_canonical_json(payload)


def _top_k_question_ids(response: api_main.ConceptQuestionsResponse, *, k: int) -> set[str]:
    return {
        question.question_id
        for question in response.questions[:k]
        if isinstance(question.question_id, str) and question.question_id
    }


def _has_required_evidence_refs(refs: list[api_main.EvidenceRef]) -> bool:
    has_event = any(ref.kind == "event" for ref in refs)
    has_linked_ref = any(ref.kind in {"artifact", "validator"} for ref in refs)
    return has_event and has_linked_ref


def _read_json_object(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"baseline payload must be a JSON object: {path}")
    return payload


def _quality_metric_deltas(
    *,
    current_metrics: Mapping[str, Any],
    baseline_metrics: Mapping[str, Any],
) -> tuple[dict[str, float], bool]:
    deltas: dict[str, float] = {}
    all_passed = True
    for metric_name, rule in FROZEN_QUALITY_METRIC_RULES.items():
        current_value = current_metrics.get(metric_name)
        baseline_value = baseline_metrics.get(metric_name)
        if not isinstance(current_value, (int, float)) or not isinstance(
            baseline_value, (int, float)
        ):
            raise ValueError(f"missing numeric metric for delta comparison: {metric_name}")
        delta = round(float(current_value) - float(baseline_value), 6)
        deltas[metric_name] = delta
        if rule == "non_decreasing" and delta < 0.0:
            all_passed = False
        elif rule == "non_increasing" and delta > 0.0:
            all_passed = False
    return {key: deltas[key] for key in sorted(deltas)}, all_passed


def _build_delta_report(
    *,
    current_dashboard: Mapping[str, Any],
    baseline_dashboard: Mapping[str, Any],
) -> dict[str, Any]:
    current_metrics = current_dashboard.get("metrics")
    baseline_metrics = baseline_dashboard.get("metrics")
    if not isinstance(current_metrics, Mapping) or not isinstance(baseline_metrics, Mapping):
        raise ValueError("dashboard payload missing metrics object")

    deltas, non_negative_quality = _quality_metric_deltas(
        current_metrics=current_metrics,
        baseline_metrics=baseline_metrics,
    )
    baseline_hash = sha256_canonical_json(baseline_dashboard)
    current_hash = sha256_canonical_json(current_dashboard)
    return {
        "schema": DELTA_REPORT_VERSION,
        "baseline": {
            "dashboard_version": baseline_dashboard.get("dashboard_version"),
            "artifact_hash": baseline_hash,
            "artifact_ref": f"artifact:quality_dashboard:{baseline_hash}",
        },
        "current": {
            "dashboard_version": current_dashboard.get("dashboard_version"),
            "artifact_hash": current_hash,
            "artifact_ref": f"artifact:quality_dashboard:{current_hash}",
        },
        "metric_deltas": deltas,
        "delta_rules": {
            key: FROZEN_QUALITY_METRIC_RULES[key]
            for key in sorted(FROZEN_QUALITY_METRIC_RULES)
        },
        "non_negative_quality": non_negative_quality,
    }


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
    evaluation_ts: str = DETERMINISTIC_EVALUATION_TS,
) -> dict[str, Any]:
    question_fixtures = _load_fixtures(QUESTIONS_FIXTURE_ROOT)
    tournament_fixtures = _load_fixtures(TOURNAMENT_FIXTURE_ROOT)
    if not question_fixtures:
        raise RuntimeError("no question eval fixtures found under examples/eval/questions")
    if not tournament_fixtures:
        raise RuntimeError(
            "no tournament eval fixtures found under examples/eval/tournament"
        )

    solver_calls_by_action: dict[str, list[int]] = {
        QUESTIONS_ACTION: [],
        TOURNAMENT_REPLAY_ACTION: [],
        TOURNAMENT_LIVE_ACTION: [],
    }

    stable_matches = 0
    stable_total = 0
    top_k_stability_samples: list[float] = []
    total_questions = 0
    unique_questions = 0
    evidence_covered_questions = 0
    evidence_total_questions = 0
    bridge_loss_present_cases = 0
    bridge_loss_referenced_cases = 0
    question_counts: list[int] = []
    resolved_counts: list[int] = []
    question_fixture_details: list[dict[str, Any]] = []

    for fixture in question_fixtures:
        baseline_signature: str | None = None
        baseline_question_count = 0
        baseline_top_k_ids: set[str] = set()
        fixture_unique_questions = 0
        fixture_redundancy_rate = 0.0

        for repeat_idx in range(question_repeats):
            ir = fixture.ir.model_copy(deep=True)
            request = _make_questions_request(fixture, ir)
            response = api_main.concept_questions_endpoint(request)
            solver_calls_by_action[QUESTIONS_ACTION].append(
                response.budget_report.used_solver_calls
            )

            signature = _question_signature(response)
            if repeat_idx == 0:
                baseline_signature = signature
                baseline_question_count = response.question_count
                baseline_top_k_ids = _top_k_question_ids(response, k=10)
                question_counts.append(response.question_count)
                dedupe_signatures = {
                    _question_dedupe_signature(question) for question in response.questions
                }
                fixture_unique_questions = len(dedupe_signatures)
                fixture_redundancy_rate = round(
                    1.0
                    - (
                        fixture_unique_questions
                        / max(response.question_count, 1)
                    ),
                    6,
                )
                total_questions += response.question_count
                unique_questions += fixture_unique_questions
                evidence_total_questions += response.question_count
                if _has_required_evidence_refs(response.evidence_refs):
                    evidence_covered_questions += response.question_count
                bridge_loss_present = bool(response.bridge_loss_signals)
                if bridge_loss_present:
                    bridge_loss_present_cases += 1
                    if response.bridge_loss_signals:
                        bridge_loss_referenced_cases += 1
            else:
                stable_total += 1
                if signature == baseline_signature:
                    stable_matches += 1
                overlap = len(
                    baseline_top_k_ids
                    & _top_k_question_ids(response, k=10)
                )
                top_k_stability_samples.append(overlap / 10.0)

        resolved = _simulate_resolved_session(
            fixture=fixture,
            max_steps=session_steps,
        )
        resolved_counts.append(resolved)
        question_fixture_details.append(
            {
                "fixture": fixture.name,
                "fixture_ref": str(QUESTIONS_FIXTURE_ROOT / fixture.name),
                "mode": str(fixture.request.get("mode", "LAX")),
                "include_forced_details": bool(
                    fixture.request.get("include_forced_details", False)
                ),
                "question_count": baseline_question_count,
                "unique_questions": fixture_unique_questions,
                "redundancy_rate": fixture_redundancy_rate,
                "resolved_in_session": resolved,
            }
        )

    coherence_alert_count = 0
    tournament_fixture_details: list[dict[str, Any]] = []
    for fixture in tournament_fixtures:
        ir = fixture.ir.model_copy(deep=True)
        question_response = api_main.concept_questions_endpoint(
            _make_questions_request(fixture, ir.model_copy(deep=True))
        )
        request = _make_tournament_request(fixture, ir)
        response = api_main.concept_tournament_endpoint(request)

        action = (
            TOURNAMENT_REPLAY_ACTION
            if response.tournament_mode == "replay_candidates"
            else TOURNAMENT_LIVE_ACTION
        )
        solver_calls_by_action[action].append(response.budget_report.used_solver_calls)
        coherence = build_concepts_coherence_artifact(
            run_id=f"quality_dashboard:{fixture.name}",
            question_artifact=question_response.model_dump(
                mode="json", by_alias=True, exclude_none=True
            ),
            tournament_artifact=response.model_dump(
                mode="json", by_alias=True, exclude_none=True
            ),
        )
        fixture_coherence_alert_count = int(coherence.get("coherence_alert_count", 0))
        coherence_alert_count += fixture_coherence_alert_count

        tournament_fixture_details.append(
            {
                "fixture": fixture.name,
                "fixture_ref": str(TOURNAMENT_FIXTURE_ROOT / fixture.name),
                "mode": str(fixture.request.get("mode", "LAX")),
                "tournament_mode": response.tournament_mode,
                "candidate_count": response.candidate_count,
                "evaluated_count": response.evaluated_count,
                "no_safe_improvement": response.no_safe_improvement,
                "coherence_alert_count": fixture_coherence_alert_count,
            }
        )

    all_solver_calls = [
        value for values in solver_calls_by_action.values() for value in values
    ]
    avg_solver_calls_by_action = {
        action: round(_avg(values), 3)
        for action, values in solver_calls_by_action.items()
        if values
    }

    stability_pct = 100.0 if stable_total == 0 else (stable_matches / stable_total) * 100.0
    redundancy_rate = 1.0 - (unique_questions / max(total_questions, 1))
    top_k_stability = 1.0 if not top_k_stability_samples else _avg(top_k_stability_samples)
    evidence_coverage_rate = evidence_covered_questions / max(evidence_total_questions, 1)
    bridge_loss_utilization_rate = bridge_loss_referenced_cases / max(
        bridge_loss_present_cases, 1
    )

    dashboard = {
        "dashboard_version": DASHBOARD_VERSION,
        "generated_at": evaluation_ts,
        "fixture_roots": {
            "questions": str(QUESTIONS_FIXTURE_ROOT),
            "tournament": str(TOURNAMENT_FIXTURE_ROOT),
        },
        "fixture_counts": {
            "questions": len(question_fixtures),
            "tournament": len(tournament_fixtures),
        },
        "metrics": {
            "redundancy_rate": round(redundancy_rate, 6),
            "top_k_stability@10": round(top_k_stability, 6),
            "evidence_coverage_rate": round(evidence_coverage_rate, 6),
            "bridge_loss_utilization_rate": round(bridge_loss_utilization_rate, 6),
            "coherence_alert_count": coherence_alert_count,
            "question_stability_pct": round(stability_pct, 3),
            "avg_questions_per_ir": round(_avg(question_counts), 3),
            "avg_resolved_per_session": round(_avg(resolved_counts), 3),
            "avg_solver_calls_per_action": round(_avg(all_solver_calls), 3),
        },
        "actions": {
            action: {
                "sample_count": len(solver_calls_by_action[action]),
                "avg_solver_calls": avg_solver_calls_by_action.get(action, 0.0),
            }
            for action in sorted(solver_calls_by_action)
            if solver_calls_by_action.get(action)
        },
        "question_fixtures": question_fixture_details,
        "tournament_fixtures": tournament_fixture_details,
        "config": {
            "question_repeats": question_repeats,
            "session_steps": session_steps,
            "evaluation_ts": evaluation_ts,
            "question_rank_version": api_main.CONCEPTS_QUESTION_RANK_VERSION,
            "tournament_score_version": api_main.TOURNAMENT_SCORE_VERSION,
            "coherence_schema_version": "concepts.coherence.v1",
            "budget_version": api_main.QUESTIONS_BUDGET_VERSION,
        },
    }
    return json.loads(canonical_json(dashboard))


def write_quality_dashboard(
    output_path: Path,
    *,
    question_repeats: int = DEFAULT_QUESTION_REPEATS,
    session_steps: int = DEFAULT_SESSION_STEPS,
    baseline_path: Path | None = None,
    evaluation_ts: str = DETERMINISTIC_EVALUATION_TS,
) -> dict[str, Any]:
    current_dashboard = build_quality_dashboard(
        question_repeats=question_repeats,
        session_steps=session_steps,
        evaluation_ts=evaluation_ts,
    )

    if baseline_path is None:
        baseline_dashboard = current_dashboard
        baseline_source = "self"
    else:
        baseline_dashboard = _read_json_object(baseline_path)
        baseline_source = "file"

    delta_report = _build_delta_report(
        current_dashboard=current_dashboard,
        baseline_dashboard=baseline_dashboard,
    )
    dashboard = {
        **current_dashboard,
        "input_manifest": {
            "schema": INPUT_MANIFEST_VERSION,
            "baseline": {
                "source": baseline_source,
                "artifact_hash": delta_report["baseline"]["artifact_hash"],
                "artifact_ref": delta_report["baseline"]["artifact_ref"],
            },
            "current": {
                "source": "generated",
                "artifact_hash": delta_report["current"]["artifact_hash"],
                "artifact_ref": delta_report["current"]["artifact_ref"],
            },
        },
        "delta_report": delta_report,
        "quality_metric_rules": {
            key: FROZEN_QUALITY_METRIC_RULES[key]
            for key in sorted(FROZEN_QUALITY_METRIC_RULES)
        },
    }

    dashboard = json.loads(canonical_json(dashboard))
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(dashboard, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return dashboard
