# LOCKED_CONTINUATION_vNEXT_PLUS255

## Status

Bounded starter lock draft for `PB-TRIAL-0-B` (one local dispatch specimen,
execution capture, candidate artifact snapshot, and lifecycle projection).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-TRIAL-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-TRIAL-0`
- slice: `PB-TRIAL-0-B`
- branch-local execution target: `arc/pb-trial-0-b`

## Purpose

Freeze the bounded `PB-TRIAL-0-B` starter slice so the repo can make one local
cleanroom worker dispatch specimen, local execution capture, candidate
artifact snapshot, and lifecycle projection reviewable under released
`PB-TRIAL-0-A` trial-preflight law.

`vNext+255` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize trial
outcome audit, observation summary, remand decision, retry dispatch authority,
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, generated official submissions, official submission authority,
unbounded command execution, target mutation outside released local
sandbox/write scope, runtime transition, product authorization, graph-memory
authority, recursive policy amendment, or future-family selection.

Controlling invariant:

```text
PB-TRIAL-0-B may record one local dispatch specimen and its local evidence
under released A trial-preflight rows, but it may not turn that specimen into
official ProgramBench execution, hidden-test equivalence, benchmark truth,
retry authority, model ranking, official submission authority, outcome
acceptance, remand authority, or future-family selection.
```

## Instantiated Here

- `PB-TRIAL-0-B` instantiates the second local cleanroom reconstruction trial
  seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-TRIAL-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS254.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS254.md`
    - `docs/ASSESSMENT_vNEXT_PLUS254_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus254/programbench_local_reconstruction_trial_docket_v254_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus254/programbench_local_trial_execution_runbook_v254_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus254/programbench_local_trial_sandbox_readiness_review_v254_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus254/programbench_local_trial_non_authority_guardrail_v254_reference.json`
  - inherited released `PB-ATTEMPT-0` basis through A:
    - attempt request
    - worker input packet
    - dispatch preflight
    - attempt guardrail
    - attempt result-review context
    - attempt family closeout alignment
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v80.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0B_IMPLEMENTATION_MAPPING_v0.md`
  - emitted second-slice record shapes:
    - `programbench_local_trial_worker_dispatch_record@1`
    - `programbench_local_trial_execution_capture@1`
    - `programbench_local_trial_candidate_artifact_snapshot@1`
    - `programbench_local_trial_lifecycle_projection@1`

## Required Starter Vocabulary

Minimum `programbench_local_trial_worker_dispatch_record@1` fields:

- `trial_worker_dispatch_ref`
- `trial_docket_ref`
- `trial_runbook_ref`
- `sandbox_readiness_review_ref`
- `worker_profile_ref`
- `dispatch_index`
- `dispatch_authority_ref`
- `sandbox_instance_ref`
- `sandbox_attestation_bundle_ref`
- `input_packet_materialization_hash`
- `worker_input_packet_hash`
- `worker_visible_context_hash`
- `tool_manifest_ref`
- `allowed_tool_manifest_hash`
- `forbidden_tool_manifest_hash`
- `dispatch_start_posture`
- `dispatch_completion_posture`
- `tool_access_posture`
- `network_access_posture`
- `source_lookup_posture`
- `hidden_test_access_posture`
- `retry_authority_posture`
- `limitation_note`

Required dispatch posture:

- one local dispatch specimen per trial docket;
- dispatch requires released A readiness posture
  `ready_for_later_local_trial_execution_review`;
- dispatch requires a `dispatch_authority_ref` tied to this B lock;
- no hidden-test access, source lookup, official ProgramBench runner/evaluator
  contact, benchmark score, model ranking, official submission, or retry
  authority.

Minimum `programbench_local_trial_execution_capture@1` fields:

- `trial_execution_capture_ref`
- `trial_worker_dispatch_ref`
- `trial_docket_ref`
- `captured_transcript_hash`
- `bounded_transcript_excerpt`
- `stdout_hash`
- `stdout_excerpt_bounded`
- `stderr_hash`
- `stderr_excerpt_bounded`
- `exit_code`
- `duration_ms`
- `timeout_status`
- `full_output_capture_policy_ref`
- `worker_tool_call_manifest_ref`
- `declared_uncertainty_rows`
- `forbidden_content_screening_rows`
- `forbidden_content_screen_verdict`
- `forbidden_content_screening_posture`
- `sandbox_witness_refs`
- `execution_capture_posture`
- `limitation_note`

Minimum `programbench_local_trial_candidate_artifact_snapshot@1` fields:

- `candidate_artifact_snapshot_ref`
- `trial_execution_capture_ref`
- `trial_docket_ref`
- `write_scope_ref`
- `pre_state_manifest_ref`
- `post_state_manifest_ref`
- `fs_diff_ref`
- `snapshot_manifest_hash`
- `materialized_file_rows`
- `generated_file_hash_rows`
- `official_submission_posture`
- `benchmark_truth_posture`
- `snapshot_inside_write_scope`
- `snapshot_posture`
- `limitation_note`

Minimum `programbench_local_trial_lifecycle_projection@1` fields:

- `trial_lifecycle_projection_ref`
- `trial_docket_ref`
- `trial_worker_dispatch_ref`
- `trial_execution_capture_ref`
- `candidate_artifact_snapshot_ref`
- `mapped_attempt_invocation_refs`
- `mapped_attempt_output_capture_refs`
- `mapped_attempt_materialization_refs`
- `mapped_attempt_sandbox_trace_refs`
- `projection_validation_rows`
- `projection_posture`
- `new_evidence_law_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_trial_worker_dispatch_record@1`
  - `programbench_local_trial_execution_capture@1`
  - `programbench_local_trial_candidate_artifact_snapshot@1`
  - `programbench_local_trial_lifecycle_projection@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released A trial docket, runbook, sandbox readiness
  review, and non-authority guardrail refs;
- validators rejecting dispatch when A readiness is blocked or missing;
- validators requiring `dispatch_authority_ref` from this B lock;
- validators enforcing one dispatch specimen per trial docket;
- validators binding dispatch to worker input packet hash, worker-visible
  context hash, tool manifest ref, allowed tool manifest hash, forbidden tool
  manifest hash, sandbox instance ref, sandbox attestation bundle ref, and
  input packet materialization hash;
- validators rejecting hidden-test access, source lookup, internet lookup,
  decompilation, external repo access, Docker socket access, host-secret
  access, official runner/evaluator contact, benchmark score, model ranking,
  official submission, and retry authority posture;
- validators requiring execution capture hashes and bounded excerpts;
- validators requiring full output capture policy refs, worker tool-call
  manifest refs, sandbox witness refs, and forbidden-content screen verdict;
- validators blocking candidate snapshots unless forbidden-content screening
  passes;
- validators requiring candidate snapshots to stay inside released write scope
  with pre/post filesystem manifests, fs diff refs, snapshot manifest hash,
  generated file hashes, and `snapshot_inside_write_scope = true`;
- validators requiring lifecycle projections to map to released
  `PB-ATTEMPT-0` lifecycle refs without defining new evidence law;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus255/`;
- focused tests for `PB-TRIAL-0-B` plus schema export coverage;
- no C-slice artifact kinds.

Expected implementation scope:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_trial.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_trial_worker_dispatch_record.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_execution_capture.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_candidate_artifact_snapshot.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_lifecycle_projection.v1.json`
- `spec/programbench_local_trial_worker_dispatch_record.schema.json`
- `spec/programbench_local_trial_execution_capture.schema.json`
- `spec/programbench_local_trial_candidate_artifact_snapshot.schema.json`
- `spec/programbench_local_trial_lifecycle_projection.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_trial_pb_trial_0b.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus255/`

## Explicit Non-Outputs

`PB-TRIAL-0-B` must not output:

- outcome audit;
- trial observation summary;
- remand decision;
- family closeout alignment;
- official ProgramBench runner/evaluator integration;
- official task execution;
- hidden-test handling;
- hidden-test equivalence;
- benchmark score;
- model ranking;
- retry authority;
- official submission or generated official submission;
- future-family selection.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+255",
  "target_path": "PB-TRIAL-0-B",
  "authority_layer": "lock",
  "selected_family": "PB-TRIAL-0",
  "selected_slice": "PB-TRIAL-0-B",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS255.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_trial_worker_dispatch_record@1",
    "programbench_local_trial_execution_capture@1",
    "programbench_local_trial_candidate_artifact_snapshot@1",
    "programbench_local_trial_lifecycle_projection@1"
  ],
  "local_gate": "make arc-start-check ARC=255",
  "non_authority_summary": "No official ProgramBench participation, hidden-test handling, benchmark truth, model ranking, retry authority, official submission, outcome audit, remand decision, or future-family selection is authorized by this lock."
}
```

## Verification Plan

- run `make arc-start-check ARC=255` while this bundle remains docs-only;
- during implementation, run the focused `PB-TRIAL-0-B` tests and
  `make check` before opening a PR.
