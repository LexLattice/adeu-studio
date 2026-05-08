from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root

from .cleanroom_reconstruction import (
    CONCEPT_REALIZATION_RECORD_SCHEMA,
    PROGRAM_ODEU_CONCEPT_BOUNDARY_SEED_SCHEMA,
    PROGRAMBENCH_CLEANROOM_EVIDENCE_SOURCE_INDEX_SCHEMA,
    PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_PROFILE_SCHEMA,
    PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_CONTRACT_SCHEMA,
    PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_SCHEMA,
    PROGRAMBENCH_PROBE_EQUIVALENCE_AUDIT_SCHEMA,
    PROGRAMBENCH_REALIZATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_COMPARISON_PACKET_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PYTHON_REALIZATION_WITNESS_TEMPLATE_SCHEMA,
    PYTHON_RECONSTRUCTION_PLAN_SCHEMA,
    PYTHON_RECONSTRUCTION_REALIZATION_PACK_SCHEMA,
    ConceptRealizationRecord,
    ProgrambenchCleanroomEvidenceSourceIndex,
    ProgrambenchCleanroomReconstructionProfile,
    ProgrambenchLocalCleanroomFixture,
    ProgrambenchLocalCleanroomFixtureContract,
    ProgrambenchProbeEquivalenceAudit,
    ProgrambenchRealizationFamilyCloseoutAlignment,
    ProgrambenchReconstructionComparisonPacket,
    ProgrambenchReconstructionNonAuthorityGuardrail,
    ProgramOdeuConceptBoundarySeed,
    PythonRealizationWitnessTemplate,
    PythonReconstructionPlan,
    PythonReconstructionRealizationPack,
)
from .models import (
    ADEU_BENCHMARK_CONSUMER_ADVISORY_REPORT_SCHEMA,
    ADEU_BENCHMARK_CONSUMER_CASE_SCHEMA,
    ADEU_BENCHMARK_CONSUMER_VALIDATION_REPORT_SCHEMA,
    ADEU_BENCHMARK_EXECUTION_CONTEXT_SCHEMA,
    ADEU_BENCHMARK_FAMILY_SPEC_SCHEMA,
    ADEU_BENCHMARK_PROJECTION_SPEC_SCHEMA,
    ADEU_BENCHMARK_SUBJECT_RECORD_SCHEMA,
    ADEU_BENCHMARK_VALIDATION_REPORT_SCHEMA,
    ADEU_CROSS_SUBJECT_COMPARISON_CASE_SCHEMA,
    ADEU_CROSS_SUBJECT_COMPARISON_REPORT_SCHEMA,
    ADEU_CROSS_SUBJECT_COMPARISON_VALIDATION_REPORT_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_BENCHMARK_VALIDATION_REPORT_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_FAILURE_TOPOLOGY_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_INSTANCE_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_METRICS_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_NON_REGRESSION_REPORT_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_PERTURBATION_CASE_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA,
    BenchmarkConsumerAdvisoryReport,
    BenchmarkConsumerCase,
    BenchmarkConsumerValidationReport,
    BenchmarkExecutionContext,
    BenchmarkFamilySpec,
    BenchmarkProjectionSpec,
    BenchmarkSubjectRecord,
    BenchmarkValidationReport,
    CrossSubjectComparisonCase,
    CrossSubjectComparisonReport,
    CrossSubjectComparisonValidationReport,
    ProceduralDepthBenchmarkValidationReport,
    ProceduralDepthDiagnosticReport,
    ProceduralDepthFailureTopology,
    ProceduralDepthGoldTrace,
    ProceduralDepthInstance,
    ProceduralDepthMetrics,
    ProceduralDepthNonRegressionReport,
    ProceduralDepthPerturbationCase,
    ProceduralDepthRunTrace,
)
from .programbench_cleanroom_adapter import (
    PROGRAMBENCH_ADAPTER_HANDOFF_SCHEMA,
    PROGRAMBENCH_ADAPTER_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PROGRAMBENCH_ADAPTER_PROBE_PLAN_SCHEMA,
    PROGRAMBENCH_ADAPTER_READINESS_SUMMARY_SCHEMA,
    PROGRAMBENCH_ADAPTER_WORKER_ACCESS_CONTRACT_SCHEMA,
    PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    PROGRAMBENCH_CLEANROOM_TASK_INTAKE_SCHEMA,
    PROGRAMBENCH_FILESYSTEM_SIDE_EFFECT_OBSERVATION_SCHEMA,
    PROGRAMBENCH_IO_ARTIFACT_OBSERVATION_INDEX_SCHEMA,
    PROGRAMBENCH_PROBE_OBSERVATION_LOG_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_CASE_PACKET_SCHEMA,
    PROGRAMBENCH_TASK_ARTIFACT_MANIFEST_SCHEMA,
    PROGRAMBENCH_TASK_VISIBILITY_MANIFEST_SCHEMA,
    ProgrambenchAdapterHandoff,
    ProgrambenchAdapterNonAuthorityGuardrail,
    ProgrambenchAdapterProbePlan,
    ProgrambenchAdapterReadinessSummary,
    ProgrambenchAdapterWorkerAccessContract,
    ProgrambenchCleanroomAdapterFamilyCloseoutAlignment,
    ProgrambenchCleanroomTaskIntake,
    ProgrambenchFilesystemSideEffectObservation,
    ProgrambenchIOArtifactObservationIndex,
    ProgrambenchProbeObservationLog,
    ProgrambenchReconstructionCasePacket,
    ProgrambenchTaskArtifactManifest,
    ProgrambenchTaskVisibilityManifest,
)
from .programbench_cleanroom_reconstruction import (
    PROGRAMBENCH_RECONSTRUCTION_CANDIDATE_ARTIFACT_MANIFEST_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_CONTEXT_EXCLUSION_MANIFEST_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_LOCAL_RUN_TRACE_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_PROBE_RESULT_LOG_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_REMAND_CORRECTION_RECORD_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_RUN_BUDGET_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_SANDBOX_POLICY_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_WORK_ORDER_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_WORKER_CONTEXT_PACKET_SCHEMA,
    ProgrambenchReconstructionCandidateArtifactManifest,
    ProgrambenchReconstructionContextExclusionManifest,
    ProgrambenchReconstructionLocalRunTrace,
    ProgrambenchReconstructionProbeResultLog,
    ProgrambenchReconstructionRemandCorrectionRecord,
    ProgrambenchReconstructionRunBudget,
    ProgrambenchReconstructionSandboxPolicy,
    ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
    ProgrambenchReconstructionWorkerContextPacket,
    ProgrambenchReconstructionWorkOrder,
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
            BenchmarkSubjectRecord,
            ADEU_BENCHMARK_SUBJECT_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_subject_record.v1.json",
            root / "spec" / "adeu_benchmark_subject_record.schema.json",
        ),
        (
            BenchmarkConsumerCase,
            ADEU_BENCHMARK_CONSUMER_CASE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_consumer_case.v1.json",
            root / "spec" / "adeu_benchmark_consumer_case.schema.json",
        ),
        (
            BenchmarkConsumerAdvisoryReport,
            ADEU_BENCHMARK_CONSUMER_ADVISORY_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_consumer_advisory_report.v1.json",
            root / "spec" / "adeu_benchmark_consumer_advisory_report.schema.json",
        ),
        (
            BenchmarkConsumerValidationReport,
            ADEU_BENCHMARK_CONSUMER_VALIDATION_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_consumer_validation_report.v1.json",
            root / "spec" / "adeu_benchmark_consumer_validation_report.schema.json",
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
        (
            ProceduralDepthPerturbationCase,
            ADEU_PROCEDURAL_DEPTH_PERTURBATION_CASE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_perturbation_case.v1.json",
            root / "spec" / "adeu_procedural_depth_perturbation_case.schema.json",
        ),
        (
            ProceduralDepthFailureTopology,
            ADEU_PROCEDURAL_DEPTH_FAILURE_TOPOLOGY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_failure_topology.v1.json",
            root / "spec" / "adeu_procedural_depth_failure_topology.schema.json",
        ),
        (
            ProceduralDepthNonRegressionReport,
            ADEU_PROCEDURAL_DEPTH_NON_REGRESSION_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_non_regression_report.v1.json",
            root / "spec" / "adeu_procedural_depth_non_regression_report.schema.json",
        ),
        (
            ProceduralDepthBenchmarkValidationReport,
            ADEU_PROCEDURAL_DEPTH_BENCHMARK_VALIDATION_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_benchmark_validation_report.v1.json",
            root / "spec" / "adeu_procedural_depth_benchmark_validation_report.schema.json",
        ),
        (
            CrossSubjectComparisonCase,
            ADEU_CROSS_SUBJECT_COMPARISON_CASE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_cross_subject_comparison_case.v1.json",
            root / "spec" / "adeu_cross_subject_comparison_case.schema.json",
        ),
        (
            CrossSubjectComparisonReport,
            ADEU_CROSS_SUBJECT_COMPARISON_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_cross_subject_comparison_report.v1.json",
            root / "spec" / "adeu_cross_subject_comparison_report.schema.json",
        ),
        (
            CrossSubjectComparisonValidationReport,
            ADEU_CROSS_SUBJECT_COMPARISON_VALIDATION_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_cross_subject_comparison_validation_report.v1.json",
            root / "spec" / "adeu_cross_subject_comparison_validation_report.schema.json",
        ),
        (
            ProgrambenchCleanroomReconstructionProfile,
            PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_PROFILE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_cleanroom_reconstruction_profile.v1.json",
            root / "spec" / "programbench_cleanroom_reconstruction_profile.schema.json",
        ),
        (
            ProgramOdeuConceptBoundarySeed,
            PROGRAM_ODEU_CONCEPT_BOUNDARY_SEED_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "program_odeu_concept_boundary_seed.v1.json",
            root / "spec" / "program_odeu_concept_boundary_seed.schema.json",
        ),
        (
            ProgrambenchCleanroomEvidenceSourceIndex,
            PROGRAMBENCH_CLEANROOM_EVIDENCE_SOURCE_INDEX_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_cleanroom_evidence_source_index.v1.json",
            root / "spec" / "programbench_cleanroom_evidence_source_index.schema.json",
        ),
        (
            ProgrambenchReconstructionNonAuthorityGuardrail,
            PROGRAMBENCH_RECONSTRUCTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_non_authority_guardrail.v1.json",
            root / "spec" / "programbench_reconstruction_non_authority_guardrail.schema.json",
        ),
        (
            ProgrambenchLocalCleanroomFixtureContract,
            PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_CONTRACT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_cleanroom_fixture_contract.v1.json",
            root / "spec" / "programbench_local_cleanroom_fixture_contract.schema.json",
        ),
        (
            ConceptRealizationRecord,
            CONCEPT_REALIZATION_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "concept_realization_record.v1.json",
            root / "spec" / "concept_realization_record.schema.json",
        ),
        (
            PythonReconstructionRealizationPack,
            PYTHON_RECONSTRUCTION_REALIZATION_PACK_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "python_reconstruction_realization_pack.v1.json",
            root / "spec" / "python_reconstruction_realization_pack.schema.json",
        ),
        (
            PythonReconstructionPlan,
            PYTHON_RECONSTRUCTION_PLAN_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "python_reconstruction_plan.v1.json",
            root / "spec" / "python_reconstruction_plan.schema.json",
        ),
        (
            PythonRealizationWitnessTemplate,
            PYTHON_REALIZATION_WITNESS_TEMPLATE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "python_realization_witness_template.v1.json",
            root / "spec" / "python_realization_witness_template.schema.json",
        ),
        (
            ProgrambenchLocalCleanroomFixture,
            PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_cleanroom_fixture.v1.json",
            root / "spec" / "programbench_local_cleanroom_fixture.schema.json",
        ),
        (
            ProgrambenchReconstructionComparisonPacket,
            PROGRAMBENCH_RECONSTRUCTION_COMPARISON_PACKET_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_comparison_packet.v1.json",
            root / "spec" / "programbench_reconstruction_comparison_packet.schema.json",
        ),
        (
            ProgrambenchProbeEquivalenceAudit,
            PROGRAMBENCH_PROBE_EQUIVALENCE_AUDIT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_probe_equivalence_audit.v1.json",
            root / "spec" / "programbench_probe_equivalence_audit.schema.json",
        ),
        (
            ProgrambenchRealizationFamilyCloseoutAlignment,
            PROGRAMBENCH_REALIZATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_realization_family_closeout_alignment.v1.json",
            root / "spec" / "programbench_realization_family_closeout_alignment.schema.json",
        ),
        (
            ProgrambenchCleanroomTaskIntake,
            PROGRAMBENCH_CLEANROOM_TASK_INTAKE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_cleanroom_task_intake.v1.json",
            root / "spec" / "programbench_cleanroom_task_intake.schema.json",
        ),
        (
            ProgrambenchTaskArtifactManifest,
            PROGRAMBENCH_TASK_ARTIFACT_MANIFEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_task_artifact_manifest.v1.json",
            root / "spec" / "programbench_task_artifact_manifest.schema.json",
        ),
        (
            ProgrambenchTaskVisibilityManifest,
            PROGRAMBENCH_TASK_VISIBILITY_MANIFEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_task_visibility_manifest.v1.json",
            root / "spec" / "programbench_task_visibility_manifest.schema.json",
        ),
        (
            ProgrambenchAdapterWorkerAccessContract,
            PROGRAMBENCH_ADAPTER_WORKER_ACCESS_CONTRACT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_adapter_worker_access_contract.v1.json",
            root / "spec" / "programbench_adapter_worker_access_contract.schema.json",
        ),
        (
            ProgrambenchAdapterNonAuthorityGuardrail,
            PROGRAMBENCH_ADAPTER_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_adapter_non_authority_guardrail.v1.json",
            root / "spec" / "programbench_adapter_non_authority_guardrail.schema.json",
        ),
        (
            ProgrambenchAdapterProbePlan,
            PROGRAMBENCH_ADAPTER_PROBE_PLAN_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_adapter_probe_plan.v1.json",
            root / "spec" / "programbench_adapter_probe_plan.schema.json",
        ),
        (
            ProgrambenchProbeObservationLog,
            PROGRAMBENCH_PROBE_OBSERVATION_LOG_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_probe_observation_log.v1.json",
            root / "spec" / "programbench_probe_observation_log.schema.json",
        ),
        (
            ProgrambenchIOArtifactObservationIndex,
            PROGRAMBENCH_IO_ARTIFACT_OBSERVATION_INDEX_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_io_artifact_observation_index.v1.json",
            root / "spec" / "programbench_io_artifact_observation_index.schema.json",
        ),
        (
            ProgrambenchFilesystemSideEffectObservation,
            PROGRAMBENCH_FILESYSTEM_SIDE_EFFECT_OBSERVATION_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_filesystem_side_effect_observation.v1.json",
            root / "spec" / "programbench_filesystem_side_effect_observation.schema.json",
        ),
        (
            ProgrambenchReconstructionCasePacket,
            PROGRAMBENCH_RECONSTRUCTION_CASE_PACKET_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_case_packet.v1.json",
            root / "spec" / "programbench_reconstruction_case_packet.schema.json",
        ),
        (
            ProgrambenchAdapterReadinessSummary,
            PROGRAMBENCH_ADAPTER_READINESS_SUMMARY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_adapter_readiness_summary.v1.json",
            root / "spec" / "programbench_adapter_readiness_summary.schema.json",
        ),
        (
            ProgrambenchAdapterHandoff,
            PROGRAMBENCH_ADAPTER_HANDOFF_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_adapter_handoff.v1.json",
            root / "spec" / "programbench_adapter_handoff.schema.json",
        ),
        (
            ProgrambenchCleanroomAdapterFamilyCloseoutAlignment,
            PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_cleanroom_adapter_family_closeout_alignment.v1.json",
            root
            / "spec"
            / "programbench_cleanroom_adapter_family_closeout_alignment.schema.json",
        ),
        (
            ProgrambenchReconstructionWorkOrder,
            PROGRAMBENCH_RECONSTRUCTION_WORK_ORDER_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_work_order.v1.json",
            root / "spec" / "programbench_reconstruction_work_order.schema.json",
        ),
        (
            ProgrambenchReconstructionWorkerContextPacket,
            PROGRAMBENCH_RECONSTRUCTION_WORKER_CONTEXT_PACKET_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_worker_context_packet.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_worker_context_packet.schema.json",
        ),
        (
            ProgrambenchReconstructionContextExclusionManifest,
            PROGRAMBENCH_RECONSTRUCTION_CONTEXT_EXCLUSION_MANIFEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_context_exclusion_manifest.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_context_exclusion_manifest.schema.json",
        ),
        (
            ProgrambenchReconstructionSandboxPolicy,
            PROGRAMBENCH_RECONSTRUCTION_SANDBOX_POLICY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_sandbox_policy.v1.json",
            root / "spec" / "programbench_reconstruction_sandbox_policy.schema.json",
        ),
        (
            ProgrambenchReconstructionRunBudget,
            PROGRAMBENCH_RECONSTRUCTION_RUN_BUDGET_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_run_budget.v1.json",
            root / "spec" / "programbench_reconstruction_run_budget.schema.json",
        ),
        (
            ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
            PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_workbench_non_authority_guardrail.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_workbench_non_authority_guardrail.schema.json",
        ),
        (
            ProgrambenchReconstructionCandidateArtifactManifest,
            PROGRAMBENCH_RECONSTRUCTION_CANDIDATE_ARTIFACT_MANIFEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_candidate_artifact_manifest.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_candidate_artifact_manifest.schema.json",
        ),
        (
            ProgrambenchReconstructionLocalRunTrace,
            PROGRAMBENCH_RECONSTRUCTION_LOCAL_RUN_TRACE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_local_run_trace.v1.json",
            root / "spec" / "programbench_reconstruction_local_run_trace.schema.json",
        ),
        (
            ProgrambenchReconstructionProbeResultLog,
            PROGRAMBENCH_RECONSTRUCTION_PROBE_RESULT_LOG_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_probe_result_log.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_probe_result_log.schema.json",
        ),
        (
            ProgrambenchReconstructionRemandCorrectionRecord,
            PROGRAMBENCH_RECONSTRUCTION_REMAND_CORRECTION_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_remand_correction_record.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_remand_correction_record.schema.json",
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
