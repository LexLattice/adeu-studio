# Draft ADEU ProgramBench Local Cleanroom Retry Governance PB-RETRY-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-RETRY-0-A`.

Authority layer: support.

This note maps the likely implementation for `PB-RETRY-0-A`. It does not
authorize implementation by itself and does not replace a future
`vNext+257` lock, stop-gate decision, or edge assessment.

## Slice Intent

`PB-RETRY-0-A` should make one released `PB-TRIAL-0` remand decision
reviewable as a retry candidate without dispatching the retry.

The slice should answer:

```text
Given one released local trial lineage and one local remand decision, is a
bounded local cleanroom retry candidate recordable and eligible for later
dispatch review, and what scope and evidence boundaries would govern it?
```

It must not answer:

```text
Can we run the retry?
Can we execute commands?
Can we materialize retry candidate files?
Can this local retry count as benchmark success?
Can this remand create another retry automatically?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_local_retry_request@1`
- `programbench_local_retry_lineage_registry@1`
- `programbench_trial_remand_source_index@1`
- `programbench_local_retry_eligibility_review@1`
- `programbench_local_retry_scope_contract@1`
- `programbench_local_retry_non_authority_guardrail@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_retry.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_retry_request.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_lineage_registry.v1.json`
- `packages/adeu_benchmarking/schema/programbench_trial_remand_source_index.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_eligibility_review.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_scope_contract.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_non_authority_guardrail.v1.json`
- `spec/programbench_local_retry_request.schema.json`
- `spec/programbench_local_retry_lineage_registry.schema.json`
- `spec/programbench_trial_remand_source_index.schema.json`
- `spec/programbench_local_retry_eligibility_review.schema.json`
- `spec/programbench_local_retry_scope_contract.schema.json`
- `spec/programbench_local_retry_non_authority_guardrail.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_retry_pb_retry_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus257/`

## Consumed Lineage

`PB-RETRY-0-A` should require released `PB-TRIAL-0` refs:

- trial docket;
- trial runbook;
- sandbox readiness review;
- trial dispatch record;
- execution capture;
- candidate artifact snapshot;
- lifecycle projection;
- outcome audit;
- observation summary;
- remand decision;
- trial family closeout alignment.

It should also require released closeout lineage from `PB-ATTEMPT-0`,
`PB-RECON-0`, `PB-ADAPTER-0`, and `PB-PY-0` when retry eligibility depends on
those inherited cleanroom laws.

## Field-Level Expectations

`programbench_local_retry_request@1` should include:

- `retry_request_ref`
- `retry_lineage_ref`
- `trial_lineage_ref`
- `source_remand_decision_ref`
- `retry_lineage_registry_ref`
- `prior_retry_request_refs`
- `retry_sequence_index`
- `retry_uniqueness_posture`
- `source_trial_ref`
- `trial_outcome_audit_ref`
- `trial_observation_summary_ref`
- `trial_remand_decision_ref`
- `trial_family_closeout_ref`
- `requested_retry_horizon`
- `retry_depth_limit`
- `retry_dispatch_authority_posture`
- `official_benchmark_authority_posture`
- `model_ranking_posture`
- `limitation_note`

`programbench_local_retry_lineage_registry@1` should include:

- `retry_lineage_registry_ref`
- `trial_lineage_ref`
- `trial_remand_decision_ref`
- `existing_retry_request_refs`
- `eligible_retry_request_refs`
- `retry_sequence_rows`
- `retry_uniqueness_posture`
- `retry_chain_authority_posture`
- `limitation_note`

`programbench_trial_remand_source_index@1` should include:

- `remand_source_index_ref`
- `retry_request_ref`
- `trial_remand_decision_ref`
- `remand_source_rows`
- `retry_rationale_rows`
- `local_retryable_source_refs`
- `local_non_retryable_source_refs`
- `blocked_source_refs`
- `forbidden_source_refs`
- `support_only_source_refs`
- `source_visibility_posture`
- `hidden_or_forbidden_exposure_posture`
- `limitation_note`

`programbench_local_retry_eligibility_review@1` should include:

- `retry_eligibility_review_ref`
- `retry_request_ref`
- `remand_source_index_ref`
- `released_trial_lineage_refs`
- `cleanroom_continuity_refs`
- `retry_scope_contract_refs`
- `eligibility_posture`
- `ready_basis_posture`
- `carried_blocker_refs`
- `carried_warning_refs`
- `non_authority_guardrail_refs`
- `limitation_note`

`programbench_local_retry_scope_contract@1` should include:

- `retry_scope_contract_ref`
- `retry_request_ref`
- `retry_lineage_ref`
- `retry_scope_delta_refs`
- `retry_scope_delta_manifest_hash`
- `unchanged_worker_visible_source_refs`
- `unchanged_forbidden_source_refs`
- `unchanged_tool_policy_refs`
- `unchanged_sandbox_policy_refs`
- `unchanged_worker_visible_source_set_hash`
- `unchanged_forbidden_source_set_hash`
- `unchanged_tool_policy_hash`
- `unchanged_sandbox_policy_hash`
- `unchanged_write_scope_hash`
- `unchanged_network_policy_hash`
- `allowed_retry_action_rows`
- `forbidden_retry_action_rows`
- `retry_depth_limit`
- `retry_chain_posture`
- `scope_authority_posture`
- `limitation_note`

`programbench_local_retry_non_authority_guardrail@1` should include:

- `retry_guardrail_ref`
- `retry_request_refs`
- `guardrail_source_refs`
- `non_authority_rows`
- `retry_dispatch_posture`
- `official_programbench_posture`
- `hidden_test_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `second_retry_posture`
- `future_family_posture`
- `limitation_note`

## Validation Expectations

The future implementation should validate:

- every A bundle resolves to one `retry_lineage_ref`;
- every A bundle cites exactly one released `PB-TRIAL-0` remand decision;
- every A bundle resolves through one retry lineage registry;
- for a given trial lineage and trial remand decision, only one eligible
  retry request may exist unless a later family grants retry-chain authority;
- the cited trial family closeout is released and closes the same trial
  lineage;
- retry request cannot be eligible if the prior trial outcome is locally
  accepted;
- retry request cannot be eligible if the prior trial is blocked by
  contamination, sandbox violation, hidden/evaluator/source evidence, official
  benchmark posture, or missing local remand;
- remand source rows must be local evidence rows, support-only rows, blocked
  rows, or forbidden rows; hidden/evaluator/source/decompilation/internet refs
  cannot be retryable;
- remand source rows and retry rationale rows must not include hidden or
  forbidden source names, paths, excerpts, semantic summaries, test names,
  original-source clues, or derived facts;
- retry rationale kinds must be local-only and cannot cite hidden-test
  failure, official evaluator feedback, source lookup facts, decompilation
  facts, internet lookup facts, external repository facts,
  benchmark-score pressure, or model-ranking pressure;
- forbidden refs cannot appear in retryable source refs, worker-visible refs,
  scope delta refs, or derived worker summaries;
- eligibility marked ready requires local retryable remand source, empty
  carried blockers, clean contamination posture, unchanged cleanroom boundary
  refs, and retry depth within limit;
- scope contract must separate retry deltas from unchanged context;
- scope contract must include unchanged boundary hashes for worker-visible
  source set, forbidden source set, tool policy, sandbox policy, write scope,
  and network policy;
- scope contract must include `retry_scope_delta_manifest_hash`;
- scope contract must not widen worker-visible source refs, allowed tool refs,
  write scope, network posture, source lookup posture, or hidden evidence
  posture;
- guardrail rows must assert no dispatch authority in A;
- A rejects B/C artifact kinds.

## Reference Fixtures

Future `vNext+257` reference fixtures should include:

- one retry request over a released remanded trial lineage;
- one retry lineage registry showing no prior eligible retry for the same
  remand;
- one remand source index with local retryable and support-only rows clearly
  separated;
- one eligibility review marked ready for later local retry dispatch review;
- one scope contract with explicit retry delta refs and unchanged cleanroom
  boundary refs;
- one non-authority guardrail.

## Reject Fixtures

Future `vNext+257` reject fixtures should include:

- retry request from a locally accepted trial;
- retry request with no released trial family closeout;
- retry request with no local remand decision;
- two eligible retry requests over the same trial remand decision;
- retry eligibility based on hidden-test, official evaluator, original-source,
  decompilation, internet, external-repository, host-secret, Docker-socket,
  postmortem-only, or excluded-derived evidence;
- retry scope contract that widens worker-visible evidence;
- retry scope contract that widens tools, network, source lookup, decompilation
  access, Docker socket access, host-secret access, or write scope;
- retry scope contract with changed boundary hash but no later authority;
- retry request that claims A grants retry dispatch authority;
- remand source index that summarizes hidden/forbidden source content into a
  worker-visible advisory row;
- retry rationale based on benchmark score pressure or model-ranking pressure;
- A bundle containing B/C artifact kinds;
- retry request that grants second-retry or unbounded retry authority.

## Non-Outputs

`PB-RETRY-0-A` must not output:

- retry dispatch records;
- retry execution capture;
- retry candidate delta snapshots;
- retry lifecycle projections;
- retry sandbox application traces;
- retry outcome audit;
- retry delta observation summary;
- remand settlement;
- second-retry authority;
- official runner/evaluator integration;
- hidden-test handling;
- benchmark score or model ranking.
