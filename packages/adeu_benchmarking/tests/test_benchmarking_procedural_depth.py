from __future__ import annotations

import json
import re
from pathlib import Path

import pytest
from adeu_benchmarking import (
    ADEU_PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_INSTANCE_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_METRICS_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA,
    ProceduralDepthGoldTrace,
    ProceduralDepthInstance,
    ProceduralDepthRunTrace,
    derive_procedural_depth_gold_trace,
    materialize_procedural_depth_instance_payload,
    score_procedural_depth_run,
    validate_procedural_depth_run_trace_against_instance,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from pydantic import ValidationError

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46b"
V46A_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46a"
_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _reference_run_fixture_name(case_label: str) -> str:
    return f"reference_procedural_depth_run_trace_{case_label}.json"


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            ADEU_PROCEDURAL_DEPTH_INSTANCE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_instance.v1.json",
            root / "spec" / "adeu_procedural_depth_instance.schema.json",
        ),
        (
            ADEU_PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_gold_trace.v1.json",
            root / "spec" / "adeu_procedural_depth_gold_trace.schema.json",
        ),
        (
            ADEU_PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_run_trace.v1.json",
            root / "spec" / "adeu_procedural_depth_run_trace.schema.json",
        ),
        (
            ADEU_PROCEDURAL_DEPTH_METRICS_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_metrics.v1.json",
            root / "spec" / "adeu_procedural_depth_metrics.schema.json",
        ),
        (
            ADEU_PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_diagnostic_report.v1.json",
            root / "spec" / "adeu_procedural_depth_diagnostic_report.schema.json",
        ),
    ]


def test_reference_instance_and_gold_trace_validate_and_bind_released_v46a_refs() -> None:
    instance = ProceduralDepthInstance.model_validate(
        _load_json(FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    )
    gold = ProceduralDepthGoldTrace.model_validate(
        _load_json(FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    )
    projection = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_projection_spec.json")
    context = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_execution_context.json")

    assert isinstance(projection, dict)
    assert isinstance(context, dict)
    assert instance.benchmark_projection_spec_ref == projection["benchmark_projection_spec_id"]
    assert instance.benchmark_execution_context_ref == context["benchmark_execution_context_id"]
    assert gold.procedural_depth_instance_ref == instance.procedural_depth_instance_id
    assert instance.reference_chain_key == "hierarchical_3x3"
    assert gold.terminal_trace_status == "completed_clean"


def test_materialize_instance_canonicalizes_step_order_before_id_assignment() -> None:
    payload = _load_json(FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    expected = _load_json(FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    assert isinstance(payload, dict)
    assert isinstance(expected, dict)

    unordered = dict(payload)
    unordered.pop("procedural_depth_instance_id")
    unordered["step_specs"] = list(reversed(payload["step_specs"]))

    materialized = materialize_procedural_depth_instance_payload(unordered)

    assert materialized == expected


def test_derive_gold_trace_replays_reference_fixture() -> None:
    instance = _load_json(FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    expected_gold = _load_json(FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    assert isinstance(instance, dict)

    derived = derive_procedural_depth_gold_trace(instance_payload=instance)

    assert derived == expected_gold


def test_clean_success_metrics_and_diagnostic_fixtures_replay() -> None:
    instance = _load_json(FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    run = _load_json(FIXTURE_ROOT, "reference_procedural_depth_run_trace_clean_success.json")
    expected_metrics = _load_json(
        FIXTURE_ROOT, "reference_procedural_depth_metrics_clean_success.json"
    )
    expected_diag = _load_json(
        FIXTURE_ROOT, "reference_procedural_depth_diagnostic_report_clean_success.json"
    )
    assert isinstance(instance, dict)
    assert isinstance(gold, dict)
    assert isinstance(run, dict)

    metrics, diagnostic = score_procedural_depth_run(
        instance_payload=instance,
        gold_trace_payload=gold,
        run_trace_payload=run,
    )

    assert metrics == expected_metrics
    assert diagnostic == expected_diag


def test_reference_degraded_runs_match_scoring_matrix() -> None:
    instance = _load_json(FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    matrix = _load_json(FIXTURE_ROOT, "reference_v46b_scoring_matrix.json")
    assert isinstance(instance, dict)
    assert isinstance(gold, dict)
    assert isinstance(matrix, dict)

    for row in matrix["scoring_rows"]:
        run_fixture = _reference_run_fixture_name(row["case_label"])
        run = _load_json(FIXTURE_ROOT, run_fixture)
        metrics, diagnostic = score_procedural_depth_run(
            instance_payload=instance,
            gold_trace_payload=gold,
            run_trace_payload=run,
        )

        assert metrics["procedural_depth_run_trace_ref"] == row["run_trace_ref"]
        assert metrics["dominant_failure_family"] == row["expected_dominant_failure_family"]
        assert metrics["plan_spine_fidelity"] == row["plan_spine_fidelity"]
        assert (
            metrics["active_step_compilation_fidelity"]
            == row["active_step_compilation_fidelity"]
        )
        assert metrics["reintegration_fidelity"] == row["reintegration_fidelity"]
        assert metrics["supporting_event_refs"] == row["supporting_event_refs"]
        assert diagnostic["dominant_failure_family"] == row["expected_dominant_failure_family"]
        assert diagnostic["supporting_event_refs"] == row["supporting_event_refs"]


@pytest.mark.parametrize(
    "fixture_name",
    [
        "reject_procedural_depth_run_trace_unsupported_event_vocabulary.json",
        "reject_procedural_depth_run_trace_invalid_terminal_status.json",
    ],
)
def test_reject_run_trace_model_fixtures_fail_closed(fixture_name: str) -> None:
    with pytest.raises(ValidationError):
        ProceduralDepthRunTrace.model_validate(_load_json(FIXTURE_ROOT, fixture_name))


def test_reject_mismatched_instance_ref_fails_closed() -> None:
    instance = _load_json(FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    reject_run = _load_json(
        FIXTURE_ROOT, "reject_procedural_depth_run_trace_mismatched_instance_ref.json"
    )
    assert isinstance(instance, dict)
    assert isinstance(reject_run, dict)

    with pytest.raises(ValueError, match="must reference the supplied procedural depth instance"):
        validate_procedural_depth_run_trace_against_instance(
            instance_payload=instance,
            run_trace_payload=reject_run,
        )


def test_export_schema_replays_authoritative_and_mirror_outputs_for_v46b() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert repo_root(anchor=Path(__file__)).as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
