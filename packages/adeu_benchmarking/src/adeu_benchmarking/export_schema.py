from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root

from .models import (
    ADEU_BENCHMARK_EXECUTION_CONTEXT_SCHEMA,
    ADEU_BENCHMARK_FAMILY_SPEC_SCHEMA,
    ADEU_BENCHMARK_PROJECTION_SPEC_SCHEMA,
    ADEU_BENCHMARK_VALIDATION_REPORT_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_INSTANCE_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_METRICS_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA,
    BenchmarkExecutionContext,
    BenchmarkFamilySpec,
    BenchmarkProjectionSpec,
    BenchmarkValidationReport,
    ProceduralDepthDiagnosticReport,
    ProceduralDepthGoldTrace,
    ProceduralDepthInstance,
    ProceduralDepthMetrics,
    ProceduralDepthRunTrace,
)

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _write_schema(path: Path, schema: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(schema, indent=2, sort_keys=True) + "\n"
    path.write_text(payload, encoding="utf-8")


def _assert_no_absolute_path_material(
    value: Any,
    *,
    repo_root_path: Path,
    node_path: str = "$",
) -> None:
    if isinstance(value, dict):
        for key in sorted(value):
            _assert_no_absolute_path_material(
                value[key],
                repo_root_path=repo_root_path,
                node_path=f"{node_path}.{key}",
            )
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _assert_no_absolute_path_material(
                item,
                repo_root_path=repo_root_path,
                node_path=f"{node_path}[{index}]",
            )
        return
    if not isinstance(value, str):
        return

    normalized = value.replace("\\", "/")
    root_text = repo_root_path.as_posix()
    if root_text in normalized:
        raise RuntimeError(
            f"schema export contains repository absolute path material at {node_path}: {value!r}"
        )
    if _WINDOWS_ABSOLUTE_PATH_RE.search(value):
        raise RuntimeError(
            f"schema export contains Windows absolute path material at {node_path}: {value!r}"
        )
    if normalized.startswith("/home/") or normalized.startswith("/Users/"):
        raise RuntimeError(
            f"schema export contains user-home absolute path material at {node_path}: {value!r}"
        )


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    schema_outputs = [
        (
            BenchmarkFamilySpec,
            ADEU_BENCHMARK_FAMILY_SPEC_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_family_spec.v1.json",
            root / "spec" / "adeu_benchmark_family_spec.schema.json",
        ),
        (
            BenchmarkProjectionSpec,
            ADEU_BENCHMARK_PROJECTION_SPEC_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_projection_spec.v1.json",
            root / "spec" / "adeu_benchmark_projection_spec.schema.json",
        ),
        (
            BenchmarkExecutionContext,
            ADEU_BENCHMARK_EXECUTION_CONTEXT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_execution_context.v1.json",
            root / "spec" / "adeu_benchmark_execution_context.schema.json",
        ),
        (
            BenchmarkValidationReport,
            ADEU_BENCHMARK_VALIDATION_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_validation_report.v1.json",
            root / "spec" / "adeu_benchmark_validation_report.schema.json",
        ),
        (
            ProceduralDepthInstance,
            ADEU_PROCEDURAL_DEPTH_INSTANCE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_instance.v1.json",
            root / "spec" / "adeu_procedural_depth_instance.schema.json",
        ),
        (
            ProceduralDepthGoldTrace,
            ADEU_PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_gold_trace.v1.json",
            root / "spec" / "adeu_procedural_depth_gold_trace.schema.json",
        ),
        (
            ProceduralDepthRunTrace,
            ADEU_PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_run_trace.v1.json",
            root / "spec" / "adeu_procedural_depth_run_trace.schema.json",
        ),
        (
            ProceduralDepthMetrics,
            ADEU_PROCEDURAL_DEPTH_METRICS_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_metrics.v1.json",
            root / "spec" / "adeu_procedural_depth_metrics.schema.json",
        ),
        (
            ProceduralDepthDiagnosticReport,
            ADEU_PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_diagnostic_report.v1.json",
            root / "spec" / "adeu_procedural_depth_diagnostic_report.schema.json",
        ),
    ]

    for model, expected_schema, authoritative_path, mirror_path in schema_outputs:
        schema = model.model_json_schema(by_alias=True)
        if schema["properties"]["schema"]["const"] != expected_schema:
            raise RuntimeError(f"schema marker drift for {expected_schema}")
        _assert_no_absolute_path_material(schema, repo_root_path=root)
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
