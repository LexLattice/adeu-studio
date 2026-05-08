# LOCKED_CONTINUATION_vNEXT_PLUS253

## Status

Bounded starter lock draft for `PB-ATTEMPT-0-C` (workbench evidence export,
attempt result review, remand queue, and attempt family closeout alignment).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-ATTEMPT-0-C` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-ATTEMPT-0`
- slice: `PB-ATTEMPT-0-C`
- branch-local execution target: `arc/pb-attempt-0-c`

## Purpose

Freeze the bounded `PB-ATTEMPT-0-C` starter slice so the repo can make local
attempt evidence export, local attempt result review, remand queue pressure,
and family closeout alignment reviewable under the released
`PB-ATTEMPT-0-A/B` attempt lifecycle rows and released `PB-RECON-0`
workbench validators.

`vNext+253` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, generated official submissions, official submission authority,
worker invocation, command execution, candidate materialization outside the
already released B rows, retry dispatch authority, runtime transition,
product authorization, graph-memory authority, recursive policy amendment, or
future-family selection.

Controlling invariant:

```text
PB-ATTEMPT-0-C may export a captured local attempt into released PB-RECON-0
workbench evidence vocabulary, review local attempt posture, queue local
remand pressure, and close PB-ATTEMPT-0, but it may not turn attempt output
or exported workbench evidence into official ProgramBench truth, hidden-test
equivalence, benchmark score, model ranking, retry authority, official
submission authority, or future-family selection.
```

## Instantiated Here

- `PB-ATTEMPT-0-C` instantiates the third and final local cleanroom
  reconstruction attempt seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-ATTEMPT-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS251.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS251.md`
    - `docs/ASSESSMENT_vNEXT_PLUS251_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_request_v251_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_worker_input_packet_v251_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_dispatch_preflight_v251_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_non_authority_guardrail_v251_reference.json`
  - consumed released `PB-ATTEMPT-0-B` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS252.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS252.md`
    - `docs/ASSESSMENT_vNEXT_PLUS252_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus252/programbench_reconstruction_attempt_worker_invocation_record_v252_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus252/programbench_reconstruction_attempt_output_capture_v252_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus252/programbench_reconstruction_attempt_candidate_materialization_v252_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus252/programbench_reconstruction_attempt_sandbox_application_trace_v252_reference.json`
  - consumed released `PB-RECON-0` workbench basis:
    - released workbench evidence schemas and validators
    - released `programbench_reconstruction_result_summary@1` rows
    - released `programbench_reconstruction_workbench_family_closeout_alignment@1`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v79.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted third-slice record shapes:
    - `programbench_reconstruction_attempt_workbench_evidence_export@1`
    - `programbench_reconstruction_attempt_result_review@1`
    - `programbench_reconstruction_attempt_remand_queue@1`
    - `programbench_reconstruction_attempt_family_closeout_alignment@1`

## Required Starter Vocabulary

Minimum `programbench_reconstruction_attempt_workbench_evidence_export@1`
fields:

- `workbench_evidence_export_ref`
- `attempt_request_ref`
- `worker_invocation_ref`
- `output_capture_ref`
- `candidate_materialization_ref`
- `sandbox_application_trace_ref`
- `exported_candidate_artifact_manifest_refs`
- `exported_local_run_trace_refs`
- `exported_probe_result_log_refs`
- `exported_remand_correction_record_refs`
- `exported_equivalence_audit_refs`
- `exported_result_summary_refs`
- `export_validation_posture`
- `pb_recon_validator_binding_refs`
- `pb_recon_validation_result_refs`
- `benchmark_truth_posture`
- `hidden_test_equivalence_posture`
- `official_submission_posture`
- `limitation_note`

Export rows must map into released `PB-RECON-0` evidence shapes and
validators. They must not redefine workbench evidence law.

Required export law:

```text
export_validation_posture = valid requires passing PB-RECON validation result
refs for every mapped workbench evidence row.
```

Minimum `programbench_reconstruction_attempt_result_review@1` fields:

- `attempt_result_review_ref`
- `attempt_request_ref`
- `workbench_evidence_export_ref`
- `result_summary_refs`
- `local_attempt_posture`
- `carried_blocker_refs`
- `carried_warning_refs`
- `local_acceptance_scope_posture`
- `hidden_test_equivalence_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `official_submission_posture`
- `limitation_note`

Allowed `local_attempt_posture` values:

- `attempt_locally_accepted`
- `attempt_remand_required`
- `attempt_blocked_by_contamination`
- `attempt_blocked_by_sandbox_violation`
- `attempt_blocked_by_export_gap`
- `attempt_inconclusive_local_only`
- `future_family_only`

Required local acceptance law:

```text
local_attempt_posture = attempt_locally_accepted requires exported workbench
result summaries that are local_accepted under released PB-RECON-0 law,
passing PB-RECON validator result refs, no contamination blockers, no sandbox
violation blockers, no export gaps, no hidden-test equivalence posture, no
official submission posture, and no model-ranking or benchmark-truth claim.
```

Minimum `programbench_reconstruction_attempt_remand_queue@1` fields:

- `remand_queue_ref`
- `attempt_request_ref`
- `attempt_result_review_ref`
- `remand_queue_rows`
- `retry_budget_ref`
- `remand_row_source_kinds`
- `remand_source_posture`
- `hidden_test_diagnostic_posture`
- `source_lookup_posture`
- `queue_authority_posture`
- `limitation_note`

Allowed remand row source kinds:

- `local_probe_failure`
- `local_output_capture_gap`
- `materialization_gap`
- `sandbox_application_failure`
- `exported_workbench_gap`
- `worker_declared_uncertainty`

Required queue law:

```text
remand queues may record local retry pressure only. They do not grant retry
dispatch authority and may not cite hidden tests, official evaluator output,
original source, decompilation, internet lookup, or external repo diagnostics.
```

Minimum `programbench_reconstruction_attempt_family_closeout_alignment@1`
fields:

- `family_closeout_ref`
- `closed_family_ref`
- `closed_slice_refs`
- `attempt_request_refs`
- `worker_invocation_refs`
- `workbench_evidence_export_refs`
- `attempt_result_review_refs`
- `remand_queue_refs`
- `family_alignment_posture`
- `official_programbench_non_authority_posture`
- `hidden_test_non_inference_posture`
- `benchmark_truth_non_authority_posture`
- `model_ranking_non_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

Family closeout closes only `PB-ATTEMPT-0`.

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_reconstruction_attempt_workbench_evidence_export@1`
  - `programbench_reconstruction_attempt_result_review@1`
  - `programbench_reconstruction_attempt_remand_queue@1`
  - `programbench_reconstruction_attempt_family_closeout_alignment@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released `PB-ATTEMPT-0-A` attempt request, worker input
  packet, dispatch preflight, and non-authority guardrail refs;
- validators requiring released `PB-ATTEMPT-0-B` worker invocation, output
  capture, candidate materialization, and sandbox application trace refs;
- validators requiring export rows to bind to released `PB-RECON-0` validator
  binding refs and validation result refs;
- validators rejecting export laundering where attempt output is treated as
  accepted workbench evidence without released `PB-RECON-0` validation;
- validators rejecting benchmark truth, hidden-test equivalence, official
  evaluator result, benchmark score, model ranking, official submission, and
  official ProgramBench participation posture;
- validators requiring local accepted attempt review to cite exported
  workbench result summaries accepted under released `PB-RECON-0` law;
- validators requiring non-accepted attempt reviews to carry blocker or
  limitation refs;
- validators requiring remand queues to cite only local attempt/workbench
  evidence source kinds and to carry no retry authority;
- validators requiring family closeout alignment to close exactly
  `PB-ATTEMPT-0-A`, `PB-ATTEMPT-0-B`, and `PB-ATTEMPT-0-C`;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus253/`;
- focused tests for `PB-ATTEMPT-0-C` plus schema export coverage.

Expected implementation scope:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_attempt.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_workbench_evidence_export.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_result_review.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_remand_queue.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_family_closeout_alignment.v1.json`
- `spec/programbench_reconstruction_attempt_workbench_evidence_export.schema.json`
- `spec/programbench_reconstruction_attempt_result_review.schema.json`
- `spec/programbench_reconstruction_attempt_remand_queue.schema.json`
- `spec/programbench_reconstruction_attempt_family_closeout_alignment.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_attempt_pb_attempt_0c.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus253/`

## Explicit Non-Outputs

`PB-ATTEMPT-0-C` must not output:

- worker invocation;
- new command execution;
- new candidate materialization outside released B rows;
- retry dispatch authority;
- official ProgramBench runner/evaluator integration;
- official task execution;
- official submission artifact;
- hidden-test handling;
- hidden-test equivalence;
- benchmark score;
- benchmark truth;
- model ranking or leaderboard row;
- source lookup, decompilation, internet lookup, or external repo diagnostic;
- product, graph-memory, release, recursive-policy, or future-family
  selection.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+253",
  "target_path": "PB-ATTEMPT-0-C",
  "authority_layer": "lock",
  "selected_family": "PB-ATTEMPT-0",
  "selected_slice": "PB-ATTEMPT-0-C",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS253.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_reconstruction_attempt_workbench_evidence_export@1",
    "programbench_reconstruction_attempt_result_review@1",
    "programbench_reconstruction_attempt_remand_queue@1",
    "programbench_reconstruction_attempt_family_closeout_alignment@1"
  ],
  "local_gate": "make arc-start-check ARC=253",
  "non_authority_summary": "No official ProgramBench participation, hidden-test handling, benchmark truth, model ranking, official submission, retry dispatch authority, worker invocation, command execution, new candidate materialization, or future-family selection is authorized by this lock."
}
```

## Verification Plan

- run `make arc-start-check ARC=253` while this bundle remains docs-only;
- during implementation, run the focused `PB-ATTEMPT-0-C` tests and
  `make check` before opening a PR.
