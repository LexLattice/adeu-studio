# LOCKED_CONTINUATION_vNEXT_PLUS258

## Status

Bounded starter lock draft for `PB-RETRY-0-B` (one local retry dispatch
specimen, retry execution capture, retry candidate delta snapshot, retry
lifecycle projection, and retry sandbox application trace).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-RETRY-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-RETRY-0`
- slice: `PB-RETRY-0-B`
- branch-local execution target: `arc/pb-retry-0-b`

## Purpose

Freeze the bounded `PB-RETRY-0-B` starter slice so the repo can make exactly
one local retry dispatch specimen and its local execution, sandbox, output,
candidate-delta, and lifecycle-projection evidence reviewable under released
`PB-RETRY-0-A` retry-intake law.

`vNext+258` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize retry
outcome audit, retry delta observation summary, remand settlement, second
retry authority, multi-attempt comparison, official ProgramBench
participation, official task execution, official runner integration, official
evaluator integration, hidden-test handling, hidden-test inference,
hidden-test equivalence, original source lookup, decompilation, internet
lookup inside ProgramBench tasks, external repository lookup, benchmark
submission, benchmark scoring, benchmark truth, model ranking, generated
official submissions, official submission authority, unbounded command
execution, target mutation outside released local sandbox/write scope,
runtime transition outside the local retry specimen, product authorization,
graph-memory authority, recursive policy amendment, or future-family
selection.

Controlling invariant:

```text
PB-RETRY-0-B may record one local retry dispatch specimen under released
PB-RETRY-0-A eligibility and scope rows, but it may not turn that specimen
into official ProgramBench execution, hidden-test equivalence, benchmark
truth, model ranking, second retry authority, remand settlement, official
submission authority, or future-family selection.
```

## Instantiated Here

- `PB-RETRY-0-B` instantiates the second local cleanroom retry-governance seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-RETRY-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS257.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS257.md`
    - `docs/ASSESSMENT_vNEXT_PLUS257_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus257/programbench_local_retry_request_v257_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus257/programbench_local_retry_lineage_registry_v257_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus257/programbench_trial_remand_source_index_v257_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus257/programbench_local_retry_eligibility_review_v257_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus257/programbench_local_retry_scope_contract_v257_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus257/programbench_local_retry_non_authority_guardrail_v257_reference.json`
  - inherited released `PB-TRIAL-0` basis through A:
    - local trial outcome audit
    - local trial observation summary
    - local trial remand decision
    - local trial family closeout alignment
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v81.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0B_IMPLEMENTATION_MAPPING_v0.md`
  - emitted second-slice record shapes:
    - `programbench_local_retry_dispatch_record@1`
    - `programbench_local_retry_execution_capture@1`
    - `programbench_local_retry_candidate_delta_snapshot@1`
    - `programbench_local_retry_lifecycle_projection@1`
    - `programbench_local_retry_sandbox_application_trace@1`

## Required Starter Vocabulary

Minimum `programbench_local_retry_dispatch_record@1` fields:

- `retry_dispatch_record_ref`
- `retry_request_ref`
- `retry_lineage_ref`
- `source_trial_dispatch_ref`
- `retry_eligibility_review_ref`
- `retry_scope_contract_ref`
- `retry_dispatch_authority_ref`
- `retry_depth`
- `worker_profile_ref`
- `worker_input_packet_hash`
- `worker_visible_context_hash`
- `retry_scope_delta_hash`
- `retry_input_packet_hash`
- `retry_worker_visible_context_hash`
- `retry_scope_contract_hash`
- `retry_allowed_tool_manifest_hash`
- `retry_forbidden_tool_manifest_hash`
- `retry_sandbox_policy_hash`
- `retry_run_budget_hash`
- `tool_manifest_ref`
- `allowed_tool_manifest_hash`
- `forbidden_tool_manifest_hash`
- `sandbox_instance_ref`
- `sandbox_attestation_bundle_ref`
- `input_packet_materialization_hash`
- `dispatch_cardinality_posture`
- `official_programbench_posture`
- `limitation_note`

Required dispatch posture:

- one local retry dispatch specimen per retry request;
- retry depth remains within released A `retry_depth_limit`;
- dispatch requires released A eligibility posture
  `eligible_for_later_local_retry_dispatch_review`;
- dispatch requires a `retry_dispatch_authority_ref` tied to this B lock;
- A eligibility alone is not dispatch authority;
- no hidden-test access, source lookup, official ProgramBench runner/evaluator
  contact, benchmark score, model ranking, official submission, or second
  retry authority.

Minimum `programbench_local_retry_execution_capture@1` fields:

- `retry_execution_capture_ref`
- `retry_dispatch_record_ref`
- `stdout_hash`
- `stdout_excerpt_bounded`
- `stderr_hash`
- `stderr_excerpt_bounded`
- `transcript_hash`
- `transcript_excerpt_bounded`
- `exit_code`
- `duration_ms`
- `timeout_status`
- `worker_tool_call_manifest_ref`
- `full_output_capture_policy_ref`
- `forbidden_content_screen_verdict`
- `forbidden_content_screening_basis_refs`
- `screened_output_hashes`
- `screening_reviewer_or_policy_ref`
- `sandbox_violation_refs`
- `limitation_note`

Minimum `programbench_local_retry_candidate_delta_snapshot@1` fields:

- `retry_candidate_delta_snapshot_ref`
- `retry_execution_capture_ref`
- `source_trial_candidate_snapshot_ref`
- `generated_file_manifest_ref`
- `materialization_input_hash`
- `materialization_output_manifest_hash`
- `write_scope_ref`
- `inside_released_write_scope`
- `forbidden_content_screen_verdict`
- `official_submission_posture`
- `limitation_note`

Minimum `programbench_local_retry_lifecycle_projection@1` fields:

- `retry_lifecycle_projection_ref`
- `retry_request_ref`
- `retry_dispatch_record_ref`
- `retry_execution_capture_ref`
- `retry_candidate_delta_snapshot_ref`
- `trial_lifecycle_projection_ref`
- `attempt_lifecycle_projection_refs`
- `pb_trial_validator_binding_refs`
- `pb_attempt_validator_binding_refs`
- `projection_validation_posture`
- `new_evidence_law_posture`
- `limitation_note`

Minimum `programbench_local_retry_sandbox_application_trace@1` fields:

- `retry_sandbox_trace_ref`
- `retry_dispatch_record_ref`
- `sandbox_instance_ref`
- `sandbox_attestation_bundle_ref`
- `network_mode_witness_ref`
- `docker_socket_absence_witness_ref`
- `secret_absence_witness_ref`
- `source_lookup_absence_witness_ref`
- `decompilation_absence_witness_ref`
- `write_scope_attestation_ref`
- `resource_limit_attestation_ref`
- `tool_manifest_match_ref`
- `sandbox_violation_refs`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_retry_dispatch_record@1`
  - `programbench_local_retry_execution_capture@1`
  - `programbench_local_retry_candidate_delta_snapshot@1`
  - `programbench_local_retry_lifecycle_projection@1`
  - `programbench_local_retry_sandbox_application_trace@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released A retry request, lineage registry, remand
  source index, eligibility review, scope contract, and retry guardrail refs;
- validators rejecting dispatch when A eligibility is blocked, missing, stale,
  or not ready;
- validators requiring `retry_dispatch_authority_ref` from this B lock;
- validators enforcing exactly one retry dispatch specimen per retry request;
- validators preserving A retry depth and unchanged cleanroom boundary hashes;
- validators binding dispatch to retry input, worker-visible context, scope
  contract, allowed tool, forbidden tool, sandbox policy, run budget, sandbox
  instance, sandbox attestation bundle, and input materialization hashes;
- validators rejecting hidden-test access, source lookup, internet lookup,
  decompilation, external repo access, Docker socket access, host-secret
  access, official runner/evaluator contact, benchmark score, model ranking,
  official submission, and second retry authority posture;
- validators requiring execution capture hashes, bounded excerpts, timeout
  status, tool-call manifest, output-capture policy, screening basis refs, and
  screened output hashes;
- validators blocking candidate delta snapshots unless forbidden-content
  screening passes;
- validators requiring candidate delta snapshots to stay inside released write
  scope and to bind screened output hashes to materialization input hashes;
- validators requiring lifecycle projection to map to released trial/attempt
  lifecycle refs without defining new evidence law;
- validators requiring sandbox application traces to provide network, Docker
  socket, host secret, source lookup, decompilation, write scope, resource
  limit, and tool-manifest witness refs;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus258/`;
- focused tests for `PB-RETRY-0-B` plus schema export coverage;
- no C-slice artifact kinds.

Expected implementation scope:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_retry.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_retry_dispatch_record.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_execution_capture.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_candidate_delta_snapshot.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_lifecycle_projection.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_sandbox_application_trace.v1.json`
- `spec/programbench_local_retry_dispatch_record.schema.json`
- `spec/programbench_local_retry_execution_capture.schema.json`
- `spec/programbench_local_retry_candidate_delta_snapshot.schema.json`
- `spec/programbench_local_retry_lifecycle_projection.schema.json`
- `spec/programbench_local_retry_sandbox_application_trace.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_retry_pb_retry_0b.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus258/`

## Explicit Non-Outputs

`PB-RETRY-0-B` must not output:

- retry outcome audit;
- retry delta observation summary;
- remand settlement;
- family closeout alignment;
- benchmark score;
- model ranking;
- official ProgramBench submission;
- hidden-test equivalence;
- second-retry authority;
- future-family selection.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+258",
  "target_path": "PB-RETRY-0-B",
  "authority_layer": "lock",
  "selected_family": "PB-RETRY-0",
  "selected_slice": "PB-RETRY-0-B",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS258.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_retry_dispatch_record@1",
    "programbench_local_retry_execution_capture@1",
    "programbench_local_retry_candidate_delta_snapshot@1",
    "programbench_local_retry_lifecycle_projection@1",
    "programbench_local_retry_sandbox_application_trace@1"
  ],
  "local_gate": "make arc-start-check ARC=258",
  "non_authority_summary": "No retry outcome audit, remand settlement, second retry authority, official ProgramBench participation, hidden-test handling, benchmark truth, model ranking, official submission, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=258
```

For the implementation PR:

```text
.venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_retry_pb_retry_0b.py -q
make check
```
