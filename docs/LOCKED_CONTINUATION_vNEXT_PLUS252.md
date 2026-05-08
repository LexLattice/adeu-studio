# LOCKED_CONTINUATION_vNEXT_PLUS252

## Status

Bounded starter lock draft for `PB-ATTEMPT-0-B` (worker invocation record,
output capture, candidate materialization, and sandbox application trace).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-ATTEMPT-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-ATTEMPT-0`
- slice: `PB-ATTEMPT-0-B`
- branch-local execution target: `arc/pb-attempt-0-b`

## Purpose

Freeze the bounded `PB-ATTEMPT-0-B` starter slice so the repo can make one
local cleanroom worker invocation, worker output capture, local candidate
materialization, and sandbox application trace reviewable under released
`PB-ATTEMPT-0-A` attempt-preflight law.

`vNext+252` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, generated official submissions, official submission authority,
unbounded command execution, target mutation outside the released local
sandbox/write scope, workbench evidence export, attempt result review, remand
queue, runtime transition, product authorization, graph-memory authority,
recursive policy amendment, or future-family selection.

Controlling invariant:

```text
PB-ATTEMPT-0-B may record a bounded local worker invocation and local
candidate materialization under released A attempt refs, but it may not turn
worker output, materialized files, local sandbox traces, or local command
evidence into official ProgramBench execution, benchmark truth, official
submission authority, model ranking, workbench evidence export, remand
authority, or future-family selection.
```

## Instantiated Here

- `PB-ATTEMPT-0-B` instantiates the second local cleanroom reconstruction
  attempt seam:
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
  - inherited released `PB-RECON-0` basis through A:
    - work order
    - worker context packet
    - context exclusion manifest
    - sandbox policy
    - run budget
    - workbench non-authority guardrail
    - result summary
    - workbench family closeout alignment
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v79.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0B_IMPLEMENTATION_MAPPING_v0.md`
  - emitted second-slice record shapes:
    - `programbench_reconstruction_attempt_worker_invocation_record@1`
    - `programbench_reconstruction_attempt_output_capture@1`
    - `programbench_reconstruction_attempt_candidate_materialization@1`
    - `programbench_reconstruction_attempt_sandbox_application_trace@1`

## Required Starter Vocabulary

Minimum `programbench_reconstruction_attempt_worker_invocation_record@1`
fields:

- `worker_invocation_ref`
- `attempt_request_ref`
- `worker_input_packet_ref`
- `dispatch_preflight_ref`
- `worker_profile_ref`
- `attempt_invocation_index`
- `input_packet_hash`
- `worker_visible_context_hash`
- `tool_manifest_ref`
- `allowed_tool_manifest_hash`
- `forbidden_tool_manifest_hash`
- `invocation_kind`
- `invocation_start_posture`
- `invocation_completion_posture`
- `tool_access_posture`
- `network_access_posture`
- `source_lookup_posture`
- `hidden_test_access_posture`
- `invocation_transcript_hash`
- `bounded_transcript_excerpt`
- `limitation_note`

Required invocation posture:

- local-only invocation;
- no hidden-test access;
- no source lookup;
- no official ProgramBench runner/evaluator contact;
- no benchmark score;
- no model ranking;
- no official submission.

Required cardinality:

- one worker invocation per attempt request unless a later lock introduces
  retry parent and retry authority rows.

Minimum `programbench_reconstruction_attempt_output_capture@1` fields:

- `output_capture_ref`
- `worker_invocation_ref`
- `attempt_request_ref`
- `captured_output_rows`
- `declared_uncertainty_rows`
- `forbidden_content_screening_rows`
- `forbidden_content_screening_posture`
- `output_hash_rows`
- `bounded_excerpt_rows`
- `output_capture_posture`
- `candidate_materialization_authority_posture`
- `limitation_note`

Allowed `forbidden_content_screening_posture` values:

- `passed`
- `blocked_hidden_evidence`
- `blocked_forbidden_source`
- `blocked_postmortem_only`
- `blocked_excluded_derived`
- `inconclusive_requires_review`

Candidate materialization is valid only when screening posture is `passed`.

Minimum `programbench_reconstruction_attempt_candidate_materialization@1`
fields:

- `candidate_materialization_ref`
- `attempt_request_ref`
- `output_capture_ref`
- `sandbox_policy_ref`
- `materialization_input_hash`
- `materialization_output_manifest_hash`
- `materialized_file_rows`
- `generated_file_hash_rows`
- `write_scope_ref`
- `write_scope_attestation_ref`
- `official_submission_posture`
- `benchmark_truth_posture`
- `materialized_inside_write_scope`
- `materialization_posture`
- `limitation_note`

Required materialization posture:

- local-only candidate materialization;
- inside released sandbox write scope;
- no official submission;
- no benchmark truth;
- generated file hashes present.

Minimum `programbench_reconstruction_attempt_sandbox_application_trace@1`
fields:

- `sandbox_application_trace_ref`
- `attempt_request_ref`
- `candidate_materialization_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `application_step_rows`
- `pre_state_manifest_ref`
- `post_state_manifest_ref`
- `fs_diff_ref`
- `network_attestation_ref`
- `secret_absence_attestation_ref`
- `docker_socket_absence_attestation_ref`
- `source_lookup_absence_attestation_ref`
- `application_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_reconstruction_attempt_worker_invocation_record@1`
  - `programbench_reconstruction_attempt_output_capture@1`
  - `programbench_reconstruction_attempt_candidate_materialization@1`
  - `programbench_reconstruction_attempt_sandbox_application_trace@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released A attempt request, worker input packet,
  dispatch preflight, and non-authority guardrail refs;
- validators rejecting invocation when preflight is blocked or missing;
- validators enforcing one invocation per attempt request;
- validators binding invocation records to input packet hash, visible context
  hash, tool manifest ref, allowed tool manifest hash, and forbidden tool
  manifest hash;
- validators rejecting hidden-test access, source lookup, internet lookup,
  decompilation, external repo access, Docker socket access, host-secret
  access, official runner/evaluator contact, benchmark score, model ranking,
  and official submission posture;
- validators requiring output hashes and bounded excerpts;
- validators blocking candidate materialization unless forbidden-content
  screening posture is `passed`;
- validators requiring materialization input hash, output manifest hash,
  generated file hashes, write-scope attestation, and
  `materialized_inside_write_scope = true`;
- validators requiring sandbox application traces to bind to sandbox policy
  and run budget refs and to carry network, secret, Docker socket, and source
  lookup absence attestations;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus252/`;
- focused tests for `PB-ATTEMPT-0-B` plus schema export coverage;
- no C-slice artifact kinds.

Expected implementation scope:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_attempt.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_worker_invocation_record.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_output_capture.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_candidate_materialization.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_sandbox_application_trace.v1.json`
- `spec/programbench_reconstruction_attempt_worker_invocation_record.schema.json`
- `spec/programbench_reconstruction_attempt_output_capture.schema.json`
- `spec/programbench_reconstruction_attempt_candidate_materialization.schema.json`
- `spec/programbench_reconstruction_attempt_sandbox_application_trace.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_attempt_pb_attempt_0b.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus252/`

## Explicit Non-Outputs

`PB-ATTEMPT-0-B` must not output:

- workbench evidence export;
- attempt result review;
- remand queue;
- family closeout alignment;
- official ProgramBench runner/evaluator integration;
- official task execution;
- hidden-test handling;
- hidden-test equivalence;
- benchmark score;
- model ranking;
- official submission or generated official submission;
- future-family selection.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+252",
  "target_path": "PB-ATTEMPT-0-B",
  "authority_layer": "lock",
  "selected_family": "PB-ATTEMPT-0",
  "selected_slice": "PB-ATTEMPT-0-B",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS252.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_reconstruction_attempt_worker_invocation_record@1",
    "programbench_reconstruction_attempt_output_capture@1",
    "programbench_reconstruction_attempt_candidate_materialization@1",
    "programbench_reconstruction_attempt_sandbox_application_trace@1"
  ],
  "local_gate": "make arc-start-check ARC=252",
  "non_authority_summary": "No official ProgramBench participation, hidden-test handling, benchmark truth, model ranking, official submission, workbench evidence export, attempt result review, remand queue, or future-family selection is authorized by this lock."
}
```

## Verification Plan

- run `make arc-start-check ARC=252` while this bundle remains docs-only;
- during implementation, run the focused `PB-ATTEMPT-0-B` tests and
  `make check` before opening a PR.
