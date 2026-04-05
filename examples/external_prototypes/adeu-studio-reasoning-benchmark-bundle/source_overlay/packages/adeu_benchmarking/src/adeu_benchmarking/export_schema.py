from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .family import (
    BENCHMARK_EXECUTION_CONTEXT_SCHEMA,
    BENCHMARK_FAMILY_SPEC_SCHEMA,
    BENCHMARK_PROJECTION_SPEC_SCHEMA,
    BENCHMARK_VALIDATION_REPORT_SCHEMA,
    BenchmarkExecutionContext,
    BenchmarkFamilySpec,
    BenchmarkProjectionSpec,
    BenchmarkValidationReport,
)
from .procedural_depth import (
    PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA,
    PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA,
    PROCEDURAL_DEPTH_INSTANCE_SCHEMA,
    PROCEDURAL_DEPTH_METRICS_SCHEMA,
    PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA,
    ProceduralDepthDiagnosticReport,
    ProceduralDepthGoldTrace,
    ProceduralDepthInstance,
    ProceduralDepthMetrics,
    ProceduralDepthRunTrace,
)


def _write_schema(path: Path, schema: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    family_schema = BenchmarkFamilySpec.model_json_schema(by_alias=True)
    if family_schema["properties"]["schema"]["const"] != BENCHMARK_FAMILY_SPEC_SCHEMA:
        raise ValueError("exported schema marker drift for benchmark_family_spec@1")
    projection_schema = BenchmarkProjectionSpec.model_json_schema(by_alias=True)
    if (
        projection_schema["properties"]["schema"]["const"]
        != BENCHMARK_PROJECTION_SPEC_SCHEMA
    ):
        raise ValueError("exported schema marker drift for benchmark_projection_spec@1")
    context_schema = BenchmarkExecutionContext.model_json_schema(by_alias=True)
    if (
        context_schema["properties"]["schema"]["const"]
        != BENCHMARK_EXECUTION_CONTEXT_SCHEMA
    ):
        raise ValueError("exported schema marker drift for benchmark_execution_context@1")
    validation_schema = BenchmarkValidationReport.model_json_schema(by_alias=True)
    if (
        validation_schema["properties"]["schema"]["const"]
        != BENCHMARK_VALIDATION_REPORT_SCHEMA
    ):
        raise ValueError("exported schema marker drift for benchmark_validation_report@1")
    instance_schema = ProceduralDepthInstance.model_json_schema(by_alias=True)
    if (
        instance_schema["properties"]["schema"]["const"]
        != PROCEDURAL_DEPTH_INSTANCE_SCHEMA
    ):
        raise ValueError("exported schema marker drift for procedural_depth_instance@1")
    gold_schema = ProceduralDepthGoldTrace.model_json_schema(by_alias=True)
    if (
        gold_schema["properties"]["schema"]["const"]
        != PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA
    ):
        raise ValueError("exported schema marker drift for procedural_depth_gold_trace@1")
    run_schema = ProceduralDepthRunTrace.model_json_schema(by_alias=True)
    if run_schema["properties"]["schema"]["const"] != PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA:
        raise ValueError("exported schema marker drift for procedural_depth_run_trace@1")
    metrics_schema = ProceduralDepthMetrics.model_json_schema(by_alias=True)
    if (
        metrics_schema["properties"]["schema"]["const"]
        != PROCEDURAL_DEPTH_METRICS_SCHEMA
    ):
        raise ValueError("exported schema marker drift for procedural_depth_metrics@1")
    diagnostic_schema = ProceduralDepthDiagnosticReport.model_json_schema(by_alias=True)
    if (
        diagnostic_schema["properties"]["schema"]["const"]
        != PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA
    ):
        raise ValueError(
            "exported schema marker drift for procedural_depth_diagnostic_report@1"
        )

    schema_root = root / "packages" / "adeu_benchmarking" / "schema"
    _write_schema(schema_root / "benchmark_family_spec.v1.json", family_schema)
    _write_schema(schema_root / "benchmark_projection_spec.v1.json", projection_schema)
    _write_schema(schema_root / "benchmark_execution_context.v1.json", context_schema)
    _write_schema(schema_root / "benchmark_validation_report.v1.json", validation_schema)
    _write_schema(schema_root / "procedural_depth_instance.v1.json", instance_schema)
    _write_schema(schema_root / "procedural_depth_gold_trace.v1.json", gold_schema)
    _write_schema(schema_root / "procedural_depth_run_trace.v1.json", run_schema)
    _write_schema(schema_root / "procedural_depth_metrics.v1.json", metrics_schema)
    _write_schema(
        schema_root / "procedural_depth_diagnostic_report.v1.json",
        diagnostic_schema,
    )


if __name__ == "__main__":
    main()
