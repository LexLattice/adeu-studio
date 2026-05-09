# Draft ADEU ProgramBench Local Cleanroom Single Case Run PB-SINGLE-CASE-RUN-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned
`PB-SINGLE-CASE-RUN-0-A`.

Authority layer: support.

This note maps the likely implementation for `PB-SINGLE-CASE-RUN-0-A`. It
does not authorize implementation by itself and does not replace a future
`vNext+<n>` lock, stop-gate decision, or edge assessment.

## Slice Intent

`PB-SINGLE-CASE-RUN-0-A` should make one local cleanroom run candidate
reviewable without executing it. It should not dispatch a worker, run
commands, capture output, create candidate artifacts, audit outcomes, score
benchmarks, compare baselines, or rank models.

This slice is not a second trial-start surface. It prepares one selected
case-lineage run wrapper under prior lifecycle law, with matrix-member origin
as the default route.

The slice should answer:

```text
Which one released local cleanroom case lineage is selected for later local
run review, and under what preflighted run controls?
```

It must not answer:

```text
Did the worker run?
Did the case pass?
What score did the benchmark get?
How does this compare to a baseline?
Should we submit officially?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_single_case_run_request@1`
- `programbench_single_case_target_selection@1`
- `programbench_single_case_execution_preflight@1`
- `programbench_single_case_run_control_contract@1`
- `programbench_single_case_run_non_authority_guardrail@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_single_case_run.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_single_case_run_pb_single_case_run_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus269/`

## Consumed Lineage

`PB-SINGLE-CASE-RUN-0-A` should require one released local cleanroom target
case lineage from:

- a released `PB-MATRIX-INCLUSION-0-C` revised local matrix membership; or
- a released `PB-CASE-EXPANSION-0-C` ready local case lineage; or
- a released `PB-ADAPTER-0-C` reconstruction case packet when direct
  single-case intake is explicitly selected.

Target-origin routes are not interchangeable:

- `matrix_member` is the default route and requires an included matrix
  membership row from a released `PB-MATRIX-INCLUSION-0-C` revision.
- `ready_expanded_case_lineage` requires released `PB-CASE-EXPANSION-0-C`
  readiness and no contamination blockers.
- `direct_adapter_case_exception` requires explicit exception posture and a
  non-matrix-lineage warning.

The selected target must also bind to released attempt/trial/workbench
substrate where applicable:

- worker input packet ref and hash;
- execution runbook ref and hash;
- sandbox readiness / policy ref and hash;
- run budget ref and hash;
- local probe basis ref and hash;
- write-scope ref and hash;
- tool manifest ref and hash;
- non-authority guardrails.

## Field-Level Expectations

`programbench_single_case_run_request@1` should include:

- `single_case_run_request_ref`
- `requested_case_lineage_ref`
- `requested_case_lineage_hash`
- `request_source_family_ref`
- `request_source_closeout_ref`
- `single_case_run_relation_to_prior_lifecycle`
- `target_origin_route`
- `target_origin_justification`
- `target_origin_exception_posture`
- `run_horizon`
- `run_rationale_rows`
- `single_case_only_posture`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `baseline_comparison_authority_posture`
- `model_ranking_authority_posture`
- `batch_execution_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

`programbench_single_case_target_selection@1` should include:

- `single_case_target_selection_ref`
- `single_case_run_request_ref`
- `selected_case_lineage_ref`
- `selected_case_lineage_hash`
- `selected_case_origin_posture`
- `target_origin_route`
- `target_origin_required_refs`
- `source_matrix_ref`
- `source_matrix_revision_ref`
- `source_matrix_revision_hash`
- `matrix_membership_row_ref`
- `matrix_membership_status`
- `source_visibility_boundary_hash`
- `cleanroom_boundary_hash`
- `case_artifact_manifest_ref`
- `case_artifact_manifest_hash`
- `worker_visible_packet_ref`
- `worker_visible_packet_hash`
- `local_probe_basis_ref`
- `local_probe_basis_hash`
- `contamination_posture`
- `target_selection_status`
- `target_selection_blocker_refs`
- `limitation_note`

`programbench_single_case_execution_preflight@1` should include:

- `single_case_execution_preflight_ref`
- `single_case_run_request_ref`
- `single_case_target_selection_ref`
- `runbook_ref`
- `runbook_hash`
- `sandbox_policy_ref`
- `sandbox_policy_hash`
- `sandbox_witness_requirement_refs`
- `required_b_witness_refs`
- `run_budget_ref`
- `run_budget_hash`
- `tool_manifest_ref`
- `tool_manifest_hash`
- `write_scope_ref`
- `write_scope_hash`
- `environment_policy_ref`
- `environment_policy_hash`
- `network_posture`
- `source_lookup_posture`
- `decompilation_posture`
- `docker_socket_posture`
- `host_secret_posture`
- `preflight_check_rows`
- `preflight_status`
- `preflight_scope_posture`
- `dispatch_authority_posture`
- `limitation_note`

Required posture:

```text
preflight_scope_posture =
  eligibility_review_only_no_dispatch

dispatch_authority_posture =
  no_worker_dispatch_authority_granted_by_pb_single_case_run_0a
```

Required B witness refs:

- `sandbox_instance_ref`
- `sandbox_attestation_bundle_ref`
- `network_mode_witness_ref`
- `docker_socket_absence_witness_ref`
- `secret_absence_witness_ref`
- `source_lookup_absence_witness_ref`
- `decompilation_absence_witness_ref`
- `write_scope_attestation_ref`

`programbench_single_case_run_control_contract@1` should include:

- `single_case_run_control_contract_ref`
- `single_case_run_request_ref`
- `worker_visible_packet_hash`
- `runbook_hash`
- `sandbox_policy_hash`
- `run_budget_hash`
- `tool_manifest_hash`
- `write_scope_hash`
- `local_probe_basis_hash`
- `allowed_command_policy`
- `timeout_policy`
- `resource_limit_policy`
- `artifact_capture_policy`
- `forbidden_content_screen_policy`
- `single_dispatch_limit_posture`
- `local_only_probe_posture`
- `official_evaluator_access_posture`
- `hidden_test_access_posture`
- `benchmark_score_authority_posture`
- `limitation_note`

`programbench_single_case_run_non_authority_guardrail@1` should include:

- `single_case_run_guardrail_ref`
- `single_case_run_request_ref`
- `forbidden_authority_rows`
- `worker_dispatch_deferred_posture`
- `command_execution_deferred_posture`
- `candidate_artifact_capture_deferred_posture`
- `local_outcome_audit_deferred_posture`
- `official_programbench_authority_posture`
- `benchmark_score_authority_posture`
- `baseline_comparison_authority_posture`
- `model_ranking_authority_posture`
- `batch_execution_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

## Validation Expectations

The future implementation should validate:

- every A bundle resolves to one `single_case_run_request_ref`;
- exactly one target case lineage is selected;
- matrix-member target origin requires `matrix_membership_status = included`;
- deferred or rejected matrix-inclusion candidates are rejected as targets;
- direct adapter case origin requires explicit exception posture and warning;
- selected target lineage resolves to released local cleanroom lineage;
- selected target has clean contamination posture;
- target selection binds source visibility, cleanroom boundary, artifact
  manifest, worker-visible packet, and probe basis hashes;
- execution preflight binds runbook, sandbox policy, sandbox witness
  requirements, run budget, tool manifest, write scope, and environment
  policy hashes;
- preflight rejects open network posture, source lookup, decompilation, Docker
  socket exposure, host secret exposure, non-closed tool manifest, or
  unbounded write scope;
- preflight defines required B witness refs but does not collect or satisfy
  those witnesses inside A;
- A cannot grant dispatch, command execution, artifact capture, local
  acceptance, retry, batch execution, benchmark scoring, baseline comparison,
  model ranking, official ProgramBench participation, or future-family
  selection authority;
- A rejects B/C record shapes.

## Reference Fixtures

Future A fixtures should include:

- one run request for exactly one released local case lineage;
- one target selection with stable case, artifact, worker packet, cleanroom,
  and probe-basis hashes;
- one execution preflight with all sandbox/tool/budget/write-scope checks
  ready for later execution review;
- one run control contract limiting the future specimen to one local dispatch;
- one non-authority guardrail.

Reject fixtures should include:

- run request with two target case lineages;
- matrix-origin target whose membership status is deferred or rejected;
- direct adapter case target without exception posture;
- target selection with missing released lineage;
- target selection with contamination blocker;
- preflight that grants dispatch authority;
- preflight with open network or source lookup;
- preflight with non-closed tool manifest;
- control contract allowing batch execution;
- guardrail that grants benchmark score, baseline comparison, model ranking,
  official ProgramBench, or future-family authority.

## Non-Outputs

`PB-SINGLE-CASE-RUN-0-A` must not output:

- worker dispatch specimen rows;
- execution trace rows;
- probe observation bundle rows;
- candidate artifact capture rows;
- lifecycle projection rows;
- local outcome audit rows;
- observation summary rows;
- remand or acceptance decision rows;
- official ProgramBench participation rows;
- benchmark score rows;
- baseline comparison rows;
- model ranking rows;
- batch execution rows;
- future-family selection rows.
