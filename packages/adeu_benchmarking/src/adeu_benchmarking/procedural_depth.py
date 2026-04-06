from __future__ import annotations

from typing import Any

from .models import (
    BenchmarkExecutionContext,
    ProceduralDepthGoldTrace,
    ProceduralDepthInstance,
    ProceduralDepthPerturbationCase,
    ProceduralDepthRunTrace,
    ProceduralDepthStepSpec,
    ProceduralDepthTraceEvent,
    _canonical_model_payload,
    canonicalize_benchmark_execution_context_payload,
    canonicalize_procedural_depth_gold_trace_payload,
    canonicalize_procedural_depth_instance_payload,
    canonicalize_procedural_depth_perturbation_case_payload,
    canonicalize_procedural_depth_run_trace_payload,
    materialize_procedural_depth_benchmark_validation_report_payload,
    materialize_procedural_depth_diagnostic_report_payload,
    materialize_procedural_depth_failure_topology_payload,
    materialize_procedural_depth_gold_trace_payload,
    materialize_procedural_depth_metrics_payload,
    materialize_procedural_depth_non_regression_report_payload,
    materialize_procedural_depth_perturbation_case_payload,
    materialize_procedural_depth_run_trace_payload,
)

_SCORING_NOTES = [
    "component fidelities are exact boolean checks in the V46-B starter scorer",
    (
        "dominant failure family derives from the starter boolean component "
        "pattern plus terminal status"
    ),
]
_DIAGNOSTIC_LIMITATIONS = [
    "Diagnostic interpretation remains bounded to one tiny hierarchical_3x3 reference chain only.",
    (
        "Perturbation, non-regression, cross-subject comparison, and downstream "
        "consumer seams remain deferred from V46-B."
    ),
]
_V46C_FAILURE_TOPOLOGY_NOTES = [
    "Failure topology is bundle-scoped over the bounded V46-C perturbation set only.",
    "Cross-subject topology widening remains deferred to V46-D.",
]
_V46C_NON_REGRESSION_NOTES = [
    (
        "Non-regression is exact-match over run-trace id, metrics id, "
        "diagnostic-report id, dominant failure family, and terminal trace status."
    ),
    "No stochastic tolerance or variance-floor doctrine is selected in the V46-C starter lane.",
]
_V46C_VALIDATION_LIMITATIONS = [
    (
        "Validation remains bounded to one tiny deterministic perturbation bundle "
        "over hierarchical_3x3 only."
    ),
    "Cross-subject comparison and downstream consumer seams remain deferred from V46-C.",
]


def _step_map(
    instance: ProceduralDepthInstance,
) -> dict[str, ProceduralDepthStepSpec]:
    return {step.step_ref: step for step in instance.step_specs}


def _active_parent(instance: ProceduralDepthInstance) -> ProceduralDepthStepSpec:
    roots = [step for step in instance.step_specs if step.parent_step_ref is None]
    active_parents = [step for step in roots if step.step_role == "active_parent"]
    if len(active_parents) != 1:
        raise ValueError("instance must contain exactly one active_parent step")
    return active_parents[0]


def _trace_signature(event: ProceduralDepthTraceEvent) -> tuple[str, str, str, str | None]:
    return (
        event.event_kind,
        event.step_ref,
        event.step_role,
        event.return_target_step_ref,
    )


def _first_mismatch_refs(
    *,
    expected_events: list[ProceduralDepthTraceEvent],
    observed_events: list[ProceduralDepthTraceEvent],
    gold_trace_ref: str,
    run_trace_ref: str,
) -> list[dict[str, Any]]:
    index = 0
    while index < len(expected_events) and index < len(observed_events):
        if _trace_signature(expected_events[index]) != _trace_signature(observed_events[index]):
            break
        index += 1
    refs: list[dict[str, Any]] = []
    if index < len(expected_events):
        refs.append(
            {
                "trace_role": "gold",
                "trace_ref": gold_trace_ref,
                "event_index": expected_events[index].event_index,
            }
        )
    if index < len(observed_events):
        refs.append(
            {
                "trace_role": "run",
                "trace_ref": run_trace_ref,
                "event_index": observed_events[index].event_index,
            }
        )
    if not refs and expected_events and observed_events:
        refs.extend(
            [
                {
                    "trace_role": "gold",
                    "trace_ref": gold_trace_ref,
                    "event_index": expected_events[-1].event_index,
                },
                {
                    "trace_role": "run",
                    "trace_ref": run_trace_ref,
                    "event_index": observed_events[-1].event_index,
                },
            ]
        )
    return refs


def _ordered_supporting_refs(
    refs: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    unique: dict[tuple[str, str, int], dict[str, Any]] = {}
    for ref in refs:
        key = (ref["trace_role"], ref["trace_ref"], ref["event_index"])
        unique[key] = ref
    return sorted(
        unique.values(),
        key=lambda row: (
            0 if row["trace_role"] == "gold" else 1,
            row["event_index"],
            row["trace_ref"],
        ),
    )


def derive_procedural_depth_gold_trace(
    *,
    instance_payload: dict[str, Any],
) -> dict[str, Any]:
    instance = ProceduralDepthInstance.model_validate(instance_payload)
    step_map = _step_map(instance)
    events: list[dict[str, Any]] = []

    def _emit(step_ref: str, event_kind: str) -> None:
        step = step_map[step_ref]
        payload: dict[str, Any] = {
            "event_index": len(events),
            "event_kind": event_kind,
            "step_ref": step.step_ref,
            "step_role": step.step_role,
        }
        if step.parent_step_ref is not None:
            payload["parent_step_ref"] = step.parent_step_ref
        if event_kind == "return":
            assert step.return_target_step_ref is not None
            payload["return_target_step_ref"] = step.return_target_step_ref
        events.append(payload)

    for step_ref in instance.top_level_plan_spine:
        step = step_map[step_ref]
        _emit(step_ref, "activate")
        if step.step_role == "active_parent":
            for child_ref in step.required_child_step_refs:
                _emit(child_ref, "activate")
                _emit(child_ref, "complete")
                _emit(child_ref, "return")
        _emit(step_ref, "complete")

    return materialize_procedural_depth_gold_trace_payload(
        {
            "procedural_depth_instance_ref": instance.procedural_depth_instance_id,
            "gold_events": events,
            "terminal_trace_status": "completed_clean",
            "derivation_notes": [
                "gold trace is deterministically derived from the hierarchical_3x3 instance",
            ],
        }
    )


def _validate_trace_events_against_instance(
    *,
    instance: ProceduralDepthInstance,
    trace_ref: str,
    events: list[ProceduralDepthTraceEvent],
) -> None:
    step_map = _step_map(instance)
    for event in events:
        step = step_map.get(event.step_ref)
        if step is None:
            raise ValueError(f"{trace_ref} event step_ref must resolve inside the instance")
        if event.step_role != step.step_role:
            raise ValueError(f"{trace_ref} event step_role must match the bound step")
        if step.parent_step_ref != event.parent_step_ref:
            raise ValueError(f"{trace_ref} event parent_step_ref must match the bound step")
        if event.event_kind == "return":
            if event.return_target_step_ref != step.return_target_step_ref:
                raise ValueError(
                    f"{trace_ref} return event must target the bound step return_target_step_ref"
                )


def validate_procedural_depth_gold_trace_against_instance(
    *,
    instance_payload: dict[str, Any],
    gold_trace_payload: dict[str, Any],
) -> tuple[ProceduralDepthInstance, ProceduralDepthGoldTrace]:
    instance = ProceduralDepthInstance.model_validate(instance_payload)
    gold_trace = ProceduralDepthGoldTrace.model_validate(gold_trace_payload)
    if gold_trace.procedural_depth_instance_ref != instance.procedural_depth_instance_id:
        raise ValueError("gold trace must reference the supplied procedural depth instance")
    _validate_trace_events_against_instance(
        instance=instance,
        trace_ref=gold_trace.procedural_depth_gold_trace_id,
        events=gold_trace.gold_events,
    )
    expected_gold = ProceduralDepthGoldTrace.model_validate(
        derive_procedural_depth_gold_trace(instance_payload=_canonical_model_payload(instance))
    )
    if gold_trace.gold_events != expected_gold.gold_events:
        raise ValueError("gold trace events must match deterministic derivation from the instance")
    if gold_trace.terminal_trace_status != "completed_clean":
        raise ValueError("gold trace terminal_trace_status must equal completed_clean")
    return instance, gold_trace


def validate_procedural_depth_run_trace_against_instance(
    *,
    instance_payload: dict[str, Any],
    run_trace_payload: dict[str, Any],
) -> tuple[ProceduralDepthInstance, ProceduralDepthRunTrace]:
    instance = ProceduralDepthInstance.model_validate(instance_payload)
    run_trace = ProceduralDepthRunTrace.model_validate(run_trace_payload)
    if run_trace.procedural_depth_instance_ref != instance.procedural_depth_instance_id:
        raise ValueError("run trace must reference the supplied procedural depth instance")
    _validate_trace_events_against_instance(
        instance=instance,
        trace_ref=run_trace.procedural_depth_run_trace_id,
        events=run_trace.observed_events,
    )
    return instance, run_trace


def score_procedural_depth_run(
    *,
    instance_payload: dict[str, Any],
    gold_trace_payload: dict[str, Any],
    run_trace_payload: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    instance, gold_trace = validate_procedural_depth_gold_trace_against_instance(
        instance_payload=instance_payload,
        gold_trace_payload=gold_trace_payload,
    )
    _, run_trace = validate_procedural_depth_run_trace_against_instance(
        instance_payload=_canonical_model_payload(instance),
        run_trace_payload=run_trace_payload,
    )
    active_parent = _active_parent(instance)

    gold_plan_events = [event for event in gold_trace.gold_events if event.step_role != "child"]
    run_plan_events = [event for event in run_trace.observed_events if event.step_role != "child"]
    plan_spine_fidelity = [
        _trace_signature(event) for event in gold_plan_events
    ] == [_trace_signature(event) for event in run_plan_events]
    plan_support = [] if plan_spine_fidelity else _first_mismatch_refs(
        expected_events=gold_plan_events,
        observed_events=run_plan_events,
        gold_trace_ref=gold_trace.procedural_depth_gold_trace_id,
        run_trace_ref=run_trace.procedural_depth_run_trace_id,
    )

    gold_vertical_events = [
        event
        for event in gold_trace.gold_events
        if event.step_role == "child" and event.event_kind in {"activate", "complete"}
    ]
    run_vertical_events = [
        event
        for event in run_trace.observed_events
        if event.step_role == "child" and event.event_kind in {"activate", "complete"}
    ]
    active_step_compilation_fidelity = [
        _trace_signature(event) for event in gold_vertical_events
    ] == [_trace_signature(event) for event in run_vertical_events]
    vertical_support = [] if active_step_compilation_fidelity else _first_mismatch_refs(
        expected_events=gold_vertical_events,
        observed_events=run_vertical_events,
        gold_trace_ref=gold_trace.procedural_depth_gold_trace_id,
        run_trace_ref=run_trace.procedural_depth_run_trace_id,
    )

    gold_reintegration_events = [
        event
        for event in gold_trace.gold_events
        if event.event_kind == "return"
        or (
            event.event_kind == "complete"
            and event.step_ref == active_parent.step_ref
            and event.step_role == "active_parent"
        )
    ]
    run_reintegration_events = [
        event
        for event in run_trace.observed_events
        if event.event_kind == "return"
        or (
            event.event_kind == "complete"
            and event.step_ref == active_parent.step_ref
            and event.step_role == "active_parent"
        )
    ]
    reintegration_fidelity = [
        _trace_signature(event) for event in gold_reintegration_events
    ] == [_trace_signature(event) for event in run_reintegration_events]
    reintegration_support = [] if reintegration_fidelity else _first_mismatch_refs(
        expected_events=gold_reintegration_events,
        observed_events=run_reintegration_events,
        gold_trace_ref=gold_trace.procedural_depth_gold_trace_id,
        run_trace_ref=run_trace.procedural_depth_run_trace_id,
    )

    if (
        plan_spine_fidelity
        and active_step_compilation_fidelity
        and reintegration_fidelity
    ):
        if run_trace.terminal_trace_status != "completed_clean":
            raise ValueError(
                "completed_clean terminal status is required when all starter "
                "component fidelities are true"
            )
        dominant_failure_family = "clean_success"
        supporting_event_refs = [
            {
                "trace_role": "gold",
                "trace_ref": gold_trace.procedural_depth_gold_trace_id,
                "event_index": gold_trace.gold_events[-1].event_index,
            },
            {
                "trace_role": "run",
                "trace_ref": run_trace.procedural_depth_run_trace_id,
                "event_index": run_trace.observed_events[-1].event_index,
            },
        ]
        diagnostic_summary = (
            "Run preserved the top-level plan spine, active-step compilation, "
            "and reintegration over the tiny hierarchical_3x3 reference chain."
        )
    else:
        if run_trace.terminal_trace_status != "completed_with_structural_break":
            raise ValueError(
                "completed_with_structural_break terminal status is required "
                "when any starter component fidelity is false"
            )
        supporting_event_refs = _ordered_supporting_refs(
            plan_support + vertical_support + reintegration_support
        )
        false_count = sum(
            [
                not plan_spine_fidelity,
                not active_step_compilation_fidelity,
                not reintegration_fidelity,
            ]
        )
        if false_count >= 2:
            dominant_failure_family = "mixed"
            diagnostic_summary = (
                "Run introduced more than one structural break family over the "
                "tiny hierarchical_3x3 reference chain."
            )
        elif not plan_spine_fidelity:
            dominant_failure_family = "horizontal_plan_spine"
            diagnostic_summary = (
                "Run drifted from the expected top-level plan spine while "
                "leaving child-step compilation and reintegration otherwise intact."
            )
        elif not active_step_compilation_fidelity:
            dominant_failure_family = "vertical_active_step_compilation"
            diagnostic_summary = (
                "Run degraded inside the active parent step by failing to "
                "preserve the expected child activation/completion pattern."
            )
        else:
            dominant_failure_family = "reintegration"
            diagnostic_summary = (
                "Run completed child work but failed to return and continue "
                "lawfully at the parent-plan boundary."
            )

    metrics_payload = materialize_procedural_depth_metrics_payload(
        {
            "procedural_depth_run_trace_ref": run_trace.procedural_depth_run_trace_id,
            "procedural_depth_gold_trace_ref": gold_trace.procedural_depth_gold_trace_id,
            "plan_spine_fidelity": plan_spine_fidelity,
            "active_step_compilation_fidelity": active_step_compilation_fidelity,
            "reintegration_fidelity": reintegration_fidelity,
            "dominant_failure_family": dominant_failure_family,
            "supporting_event_refs": supporting_event_refs,
            "scoring_notes": list(_SCORING_NOTES),
        }
    )
    diagnostic_payload = materialize_procedural_depth_diagnostic_report_payload(
        {
            "procedural_depth_run_trace_ref": run_trace.procedural_depth_run_trace_id,
            "procedural_depth_metrics_ref": metrics_payload["procedural_depth_metrics_id"],
            "dominant_failure_family": dominant_failure_family,
            "supporting_event_refs": supporting_event_refs,
            "benchmark_output_epistemic_posture": "inferred_interpretively",
            "limitations": list(_DIAGNOSTIC_LIMITATIONS),
            "diagnostic_summary": diagnostic_summary,
        }
    )
    return metrics_payload, diagnostic_payload


def _validate_deterministic_context(
    *,
    benchmark_execution_context_payload: dict[str, Any],
    instance_payload: dict[str, Any],
) -> BenchmarkExecutionContext:
    context = BenchmarkExecutionContext.model_validate(
        canonicalize_benchmark_execution_context_payload(
            benchmark_execution_context_payload
        )
    )
    instance = ProceduralDepthInstance.model_validate(instance_payload)
    if context.determinism_posture != "deterministic_fixed_context":
        raise ValueError("V46-C starter evaluation requires deterministic_fixed_context")
    if instance.benchmark_execution_context_ref != context.benchmark_execution_context_id:
        raise ValueError(
            "procedural depth instance must reference the supplied benchmark execution context"
        )
    return context


def _default_output_summary(case: ProceduralDepthPerturbationCase) -> str:
    if case.output_summary_override is not None:
        return case.output_summary_override
    if case.perturbation_kind == "branch_shift":
        return "Shifted the top-level plan spine while preserving child execution."
    if case.perturbation_kind == "delayed_constraint":
        return "Completed child work but delayed the required return to the parent plan."
    raise NotImplementedError(
        f"Missing default output summary for perturbation kind {case.perturbation_kind!r}"
    )


def materialize_procedural_depth_run_trace_from_perturbation_case(
    *,
    instance_payload: dict[str, Any],
    perturbation_case_payload: dict[str, Any],
    run_trace_override_payload: dict[str, Any] | None = None,
) -> dict[str, Any]:
    instance = ProceduralDepthInstance.model_validate(instance_payload)
    case = ProceduralDepthPerturbationCase.model_validate(perturbation_case_payload)
    if case.baseline_instance_ref != instance.procedural_depth_instance_id:
        raise ValueError("perturbation case must reference the supplied baseline instance")

    payload = {
        "procedural_depth_instance_ref": instance.procedural_depth_instance_id,
        "observed_events": [
            _canonical_model_payload(event) for event in case.perturbation_overlay_events
        ],
        "terminal_trace_status": case.expected_terminal_trace_status,
        "observed_output_summary": _default_output_summary(case),
        "trace_notes": [
            "starter v46c deterministic perturbation replay",
            f"perturbation_case_ref={case.procedural_depth_perturbation_case_id}",
            f"perturbation_kind={case.perturbation_kind}",
        ],
    }
    if run_trace_override_payload is not None:
        payload.update(run_trace_override_payload)
    return materialize_procedural_depth_run_trace_payload(payload)


def evaluate_procedural_depth_perturbation_case(
    *,
    benchmark_execution_context_payload: dict[str, Any],
    instance_payload: dict[str, Any],
    gold_trace_payload: dict[str, Any],
    perturbation_case_payload: dict[str, Any],
    replay_count: int = 3,
    replay_run_trace_payloads: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    if replay_count != 3:
        raise ValueError("V46-C starter replay_count must equal 3")
    context = _validate_deterministic_context(
        benchmark_execution_context_payload=benchmark_execution_context_payload,
        instance_payload=instance_payload,
    )
    instance = canonicalize_procedural_depth_instance_payload(instance_payload)
    gold_trace = canonicalize_procedural_depth_gold_trace_payload(gold_trace_payload)
    perturbation_case = materialize_procedural_depth_perturbation_case_payload(
        perturbation_case_payload
    )
    if replay_run_trace_payloads is None:
        replay_run_trace_payloads = [None] * replay_count
    if len(replay_run_trace_payloads) != replay_count:
        raise ValueError("replay_run_trace_payloads must match replay_count exactly")

    replay_results: list[dict[str, Any]] = []
    for replay_index, run_trace_override in enumerate(replay_run_trace_payloads):
        run_trace = materialize_procedural_depth_run_trace_from_perturbation_case(
            instance_payload=instance,
            perturbation_case_payload=perturbation_case,
            run_trace_override_payload=run_trace_override,
        )
        metrics, diagnostic = score_procedural_depth_run(
            instance_payload=instance,
            gold_trace_payload=gold_trace,
            run_trace_payload=run_trace,
        )
        replay_results.append(
            {
                "replay_index": replay_index,
                "run_trace": run_trace,
                "metrics": metrics,
                "diagnostic_report": diagnostic,
                "observed_dominant_failure_family": metrics["dominant_failure_family"],
                "observed_terminal_trace_status": run_trace["terminal_trace_status"],
            }
        )

    first_replay = replay_results[0]
    observed_dominant_failure_family = first_replay["observed_dominant_failure_family"]
    observed_terminal_trace_status = first_replay["observed_terminal_trace_status"]
    deterministic_replay_confirmed = all(
        replay["run_trace"]["procedural_depth_run_trace_id"]
        == first_replay["run_trace"]["procedural_depth_run_trace_id"]
        and replay["metrics"]["procedural_depth_metrics_id"]
        == first_replay["metrics"]["procedural_depth_metrics_id"]
        and replay["diagnostic_report"]["procedural_depth_diagnostic_report_id"]
        == first_replay["diagnostic_report"]["procedural_depth_diagnostic_report_id"]
        and replay["observed_dominant_failure_family"]
        == observed_dominant_failure_family
        and replay["observed_terminal_trace_status"] == observed_terminal_trace_status
        for replay in replay_results[1:]
    )

    return {
        "perturbation_case": perturbation_case,
        "evaluation_context_posture": context.determinism_posture,
        "replay_count": replay_count,
        "observed_dominant_failure_family": observed_dominant_failure_family,
        "observed_terminal_trace_status": observed_terminal_trace_status,
        "deterministic_replay_confirmed": deterministic_replay_confirmed,
        "regression_detected": not deterministic_replay_confirmed,
        "replay_results": replay_results,
    }


def derive_procedural_depth_failure_topology(
    *,
    case_evaluations: list[dict[str, Any]],
) -> dict[str, Any]:
    if not case_evaluations:
        raise ValueError("case_evaluations must not be empty")
    observed_families = sorted(
        {
            evaluation["observed_dominant_failure_family"]
            for evaluation in case_evaluations
        }
    )
    family_text = ", ".join(observed_families)
    return materialize_procedural_depth_failure_topology_payload(
        {
            "evaluated_cases": [
                {
                    "perturbation_case_ref": evaluation["perturbation_case"][
                        "procedural_depth_perturbation_case_id"
                    ],
                    "observed_dominant_failure_family": evaluation[
                        "observed_dominant_failure_family"
                    ],
                    "supporting_replay_refs": [
                        {
                            "replay_index": replay["replay_index"],
                            "run_trace_ref": replay["run_trace"][
                                "procedural_depth_run_trace_id"
                            ],
                        }
                        for replay in evaluation["replay_results"]
                    ],
                }
                for evaluation in case_evaluations
            ],
            "topology_summary": (
                "Starter V46-C failure topology aggregated the bounded perturbation bundle "
                f"under deterministic fixed context and observed: {family_text}."
            ),
            "notes": list(_V46C_FAILURE_TOPOLOGY_NOTES),
        }
    )


def derive_procedural_depth_non_regression_report(
    *,
    baseline_instance_payload: dict[str, Any],
    case_evaluations: list[dict[str, Any]],
) -> dict[str, Any]:
    if not case_evaluations:
        raise ValueError("case_evaluations must not be empty")
    baseline_instance = ProceduralDepthInstance.model_validate(baseline_instance_payload)
    replay_count_values = {evaluation["replay_count"] for evaluation in case_evaluations}
    if replay_count_values != {3}:
        raise ValueError("all case evaluations must carry replay_count 3")
    context_values = {
        evaluation["evaluation_context_posture"] for evaluation in case_evaluations
    }
    if context_values != {"deterministic_fixed_context"}:
        raise ValueError("all case evaluations must carry deterministic_fixed_context")
    regression_detected = any(
        evaluation["regression_detected"] for evaluation in case_evaluations
    )
    report_summary = (
        "At least one perturbation case drifted across the frozen three-replay "
        "exact-match subjects."
        if regression_detected
        else (
            "All perturbation cases stayed exact-match stable across the frozen "
            "three-replay starter law."
        )
    )
    return materialize_procedural_depth_non_regression_report_payload(
        {
            "baseline_instance_ref": baseline_instance.procedural_depth_instance_id,
            "evaluation_context_posture": "deterministic_fixed_context",
            "replay_count": 3,
            "regression_detected": regression_detected,
            "evaluated_cases": [
                {
                    "perturbation_case_ref": evaluation["perturbation_case"][
                        "procedural_depth_perturbation_case_id"
                    ],
                    "replay_indexes": [
                        replay["replay_index"] for replay in evaluation["replay_results"]
                    ],
                    "regression_detected": evaluation["regression_detected"],
                    "supporting_metric_refs": [
                        {
                            "replay_index": replay["replay_index"],
                            "metric_ref": replay["metrics"][
                                "procedural_depth_metrics_id"
                            ],
                        }
                        for replay in evaluation["replay_results"]
                    ],
                }
                for evaluation in case_evaluations
            ],
            "report_summary": report_summary,
            "notes": list(_V46C_NON_REGRESSION_NOTES),
        }
    )


def derive_procedural_depth_benchmark_validation_report(
    *,
    case_evaluations: list[dict[str, Any]],
) -> dict[str, Any]:
    if not case_evaluations:
        raise ValueError("case_evaluations must not be empty")
    replay_count_values = {evaluation["replay_count"] for evaluation in case_evaluations}
    if replay_count_values != {3}:
        raise ValueError("all case evaluations must carry replay_count 3")
    context_values = {
        evaluation["evaluation_context_posture"] for evaluation in case_evaluations
    }
    if context_values != {"deterministic_fixed_context"}:
        raise ValueError("all case evaluations must carry deterministic_fixed_context")
    validation_case_results = [
        {
            "perturbation_case_ref": evaluation["perturbation_case"][
                "procedural_depth_perturbation_case_id"
            ],
            "expected_dominant_failure_family": evaluation["perturbation_case"][
                "expected_dominant_failure_family"
            ],
            "observed_dominant_failure_family": evaluation[
                "observed_dominant_failure_family"
            ],
            "expected_terminal_trace_status": evaluation["perturbation_case"][
                "expected_terminal_trace_status"
            ],
            "observed_terminal_trace_status": evaluation[
                "observed_terminal_trace_status"
            ],
            "deterministic_replay_confirmed": evaluation[
                "deterministic_replay_confirmed"
            ],
            "replay_results": [
                {
                    "replay_index": replay["replay_index"],
                    "run_trace_ref": replay["run_trace"][
                        "procedural_depth_run_trace_id"
                    ],
                    "metric_ref": replay["metrics"][
                        "procedural_depth_metrics_id"
                    ],
                    "diagnostic_report_ref": replay["diagnostic_report"][
                        "procedural_depth_diagnostic_report_id"
                    ],
                }
                for replay in evaluation["replay_results"]
            ],
        }
        for evaluation in case_evaluations
    ]
    deterministic_replay_confirmed = all(
        case_result["deterministic_replay_confirmed"]
        and case_result["expected_dominant_failure_family"]
        == case_result["observed_dominant_failure_family"]
        and case_result["expected_terminal_trace_status"]
        == case_result["observed_terminal_trace_status"]
        for case_result in validation_case_results
    )
    return materialize_procedural_depth_benchmark_validation_report_payload(
        {
            "evaluation_context_posture": "deterministic_fixed_context",
            "replay_count": 3,
            "deterministic_replay_confirmed": deterministic_replay_confirmed,
            "validation_case_results": validation_case_results,
            "limitations": list(_V46C_VALIDATION_LIMITATIONS),
        }
    )


def evaluate_procedural_depth_perturbation_bundle(
    *,
    benchmark_execution_context_payload: dict[str, Any],
    instance_payload: dict[str, Any],
    gold_trace_payload: dict[str, Any],
    perturbation_case_payloads: list[dict[str, Any]],
    replay_run_trace_payloads_by_case_ref: dict[str, list[dict[str, Any]]] | None = None,
) -> dict[str, Any]:
    _validate_deterministic_context(
        benchmark_execution_context_payload=benchmark_execution_context_payload,
        instance_payload=instance_payload,
    )
    if not perturbation_case_payloads:
        raise ValueError("perturbation_case_payloads must not be empty")
    replay_run_trace_payloads_by_case_ref = replay_run_trace_payloads_by_case_ref or {}
    perturbation_cases = [
        materialize_procedural_depth_perturbation_case_payload(case_payload)
        for case_payload in perturbation_case_payloads
    ]
    known_case_refs = {
        case["procedural_depth_perturbation_case_id"] for case in perturbation_cases
    }
    unknown_case_refs = sorted(
        set(replay_run_trace_payloads_by_case_ref) - known_case_refs
    )
    if unknown_case_refs:
        raise ValueError(
            "replay_run_trace_payloads_by_case_ref contains unknown perturbation case refs: "
            f"{unknown_case_refs}"
        )
    case_evaluations = []
    for case in perturbation_cases:
        case_evaluations.append(
            evaluate_procedural_depth_perturbation_case(
                benchmark_execution_context_payload=benchmark_execution_context_payload,
                instance_payload=instance_payload,
                gold_trace_payload=gold_trace_payload,
                perturbation_case_payload=case,
                replay_run_trace_payloads=replay_run_trace_payloads_by_case_ref.get(
                    case["procedural_depth_perturbation_case_id"]
                ),
            )
        )
    return {
        "case_evaluations": case_evaluations,
        "failure_topology": derive_procedural_depth_failure_topology(
            case_evaluations=case_evaluations
        ),
        "non_regression_report": derive_procedural_depth_non_regression_report(
            baseline_instance_payload=instance_payload,
            case_evaluations=case_evaluations,
        ),
        "benchmark_validation_report": derive_procedural_depth_benchmark_validation_report(
            case_evaluations=case_evaluations
        ),
    }


__all__ = [
    "canonicalize_benchmark_execution_context_payload",
    "canonicalize_procedural_depth_gold_trace_payload",
    "canonicalize_procedural_depth_instance_payload",
    "canonicalize_procedural_depth_perturbation_case_payload",
    "canonicalize_procedural_depth_run_trace_payload",
    "derive_procedural_depth_gold_trace",
    "derive_procedural_depth_benchmark_validation_report",
    "derive_procedural_depth_failure_topology",
    "derive_procedural_depth_non_regression_report",
    "evaluate_procedural_depth_perturbation_bundle",
    "evaluate_procedural_depth_perturbation_case",
    "materialize_procedural_depth_diagnostic_report_payload",
    "materialize_procedural_depth_benchmark_validation_report_payload",
    "materialize_procedural_depth_failure_topology_payload",
    "materialize_procedural_depth_gold_trace_payload",
    "materialize_procedural_depth_metrics_payload",
    "materialize_procedural_depth_non_regression_report_payload",
    "materialize_procedural_depth_perturbation_case_payload",
    "materialize_procedural_depth_run_trace_from_perturbation_case",
    "score_procedural_depth_run",
    "validate_procedural_depth_gold_trace_against_instance",
    "validate_procedural_depth_run_trace_against_instance",
]
