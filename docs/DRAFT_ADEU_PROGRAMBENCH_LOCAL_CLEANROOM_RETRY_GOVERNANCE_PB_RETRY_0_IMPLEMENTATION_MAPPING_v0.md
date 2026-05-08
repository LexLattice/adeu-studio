# Draft ADEU ProgramBench Local Cleanroom Retry Governance PB-RETRY-0 Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-RETRY-0`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`PB-RETRY-0` family into likely package, schema, validator, fixture, artifact,
and evidence work so the family can be reviewed before the first active slice
lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v81.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`

## 1. Family Intent

`PB-RETRY-0` should add one bounded local cleanroom retry-governance lifecycle
over a released `PB-TRIAL-0` remand decision without turning it into:

- official ProgramBench participation, official task execution, official
  runner integration, official evaluator integration, benchmark submission,
  benchmark scoring, benchmark truth, hidden-test inference,
  hidden-test equivalence, or model ranking;
- multi-attempt comparison outside one retry lineage;
- unbounded retry loops or second-retry authority by default;
- original source lookup, decompilation, internet lookup, external source
  repository lookup, Docker socket access, or host-secret access;
- generated official submissions or official solver outputs;
- arbitrary command execution outside a released local sandbox;
- product authority, graph-memory authority, recursive policy amendment, PR
  creation, commit, merge, or release;
- `V86`, `V87`, `V88`, canonical implementation-lock review, official
  ProgramBench participation, or any other future-family selection.

The implementation target is a typed local retry family that can represent:

- retry requests;
- trial remand source indexes;
- retry eligibility reviews;
- retry scope contracts;
- retry non-authority guardrails;
- later local retry dispatch records;
- later retry execution capture rows;
- later retry candidate delta snapshots;
- later retry lifecycle projections;
- later retry sandbox application traces;
- later retry outcome audits;
- later same-lineage retry delta observation summaries;
- later remand settlement decisions;
- later retry family closeout alignment.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_benchmarking`
  - ProgramBench-shaped local cleanroom retry-governance models, enums,
    validators, and schema exports.
- logical module:
  - `adeu_benchmarking.programbench_cleanroom_retry`
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity.
- `apps/api/fixtures/benchmarking/vnext_plus257/`
  - likely future reference and reject fixtures for `PB-RETRY-0-A`, if that
    slice is selected after review.

Avoid `programbench_runner`, `programbench_eval`, `programbench_solver`,
`programbench_submitter`, `programbench_scoreboard`, and
`programbench_retry_runner` names in this family. Those names imply official
benchmark, solving, evaluation, submission, ranking, or execution authority
that the local retry family does not select.

Expected starter implementation surfaces, when the first slice begins:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_retry.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_retry_pb_retry_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`

If later slices need generic retry orchestration beyond ProgramBench-shaped
local reconstruction, that split should be selected by a future family.
`PB-RETRY-0` should keep the retry records in the benchmarking lane.

## 3. Candidate Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `programbench_local_retry_request@1` | `PB-RETRY-0-A` | one released local trial remand selected as retry candidate |
| `programbench_local_retry_lineage_registry@1` | `PB-RETRY-0-A` | uniqueness ledger preventing many eligible single retries for one remand |
| `programbench_trial_remand_source_index@1` | `PB-RETRY-0-A` | local remand rows and allowed/non-allowed retry sources |
| `programbench_local_retry_eligibility_review@1` | `PB-RETRY-0-A` | retryable/non-retryable decision without dispatch authority |
| `programbench_local_retry_scope_contract@1` | `PB-RETRY-0-A` | retry scope delta, evidence boundary continuity, and retry depth limit |
| `programbench_local_retry_non_authority_guardrail@1` | `PB-RETRY-0-A` | guardrail preventing retry rows from becoming official benchmark, ranking, or dispatch authority |
| `programbench_local_retry_dispatch_record@1` | `PB-RETRY-0-B` | one local retry dispatch specimen under released A refs |
| `programbench_local_retry_execution_capture@1` | `PB-RETRY-0-B` | retry transcript/output/artifact hashes, bounded excerpts, and sandbox witnesses |
| `programbench_local_retry_candidate_delta_snapshot@1` | `PB-RETRY-0-B` | sandbox-local candidate deltas against the original trial candidate |
| `programbench_local_retry_lifecycle_projection@1` | `PB-RETRY-0-B` | mapping from retry specimen evidence to released trial and attempt lifecycle refs |
| `programbench_local_retry_sandbox_application_trace@1` | `PB-RETRY-0-B` | sandbox/tool/network/source/secret/write-scope witness rows for the retry |
| `programbench_local_retry_outcome_audit@1` | `PB-RETRY-0-C` | local-only audit of the retry result |
| `programbench_local_retry_delta_observation_summary@1` | `PB-RETRY-0-C` | same-lineage local delta observations, not model ranking |
| `programbench_local_retry_remand_settlement@1` | `PB-RETRY-0-C` | local remand settlement without second-retry authority |
| `programbench_local_retry_family_closeout_alignment@1` | `PB-RETRY-0-C` | family closeout alignment without future-family authority |

`PB-RETRY-0-A` should ship only retry request, retry lineage registry, remand
source index, eligibility review, scope contract, guardrail, schema export,
validators, and fixtures. It should not ship retry dispatch records, execution capture,
candidate delta snapshots, lifecycle projection rows, outcome audit, delta
observation summary, remand settlement, official runner integration,
hidden-test handling, benchmark scoring, generated official submissions,
second-retry authority, or model ranking.

## 4. Source Classes

The family should consume concrete source refs from:

- `PB-TRIAL-0` family closeout:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
  - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_family_closeout_alignment_v256_reference.json`
  - `artifacts/agent_harness/v256/evidence_inputs/pb_trial_0c_trial_closeout_evidence_v256.json`
- `PB-TRIAL-0` implementation surfaces:
  - `apps/api/fixtures/benchmarking/vnext_plus254/programbench_local_reconstruction_trial_docket_v254_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus254/programbench_local_trial_execution_runbook_v254_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus254/programbench_local_trial_sandbox_readiness_review_v254_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus254/programbench_local_trial_non_authority_guardrail_v254_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus255/programbench_local_trial_worker_dispatch_record_v255_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus255/programbench_local_trial_execution_capture_v255_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus255/programbench_local_trial_candidate_artifact_snapshot_v255_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus255/programbench_local_trial_lifecycle_projection_v255_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_outcome_audit_v256_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_observation_summary_v256_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_remand_decision_v256_reference.json`
- `PB-ATTEMPT-0`, `PB-RECON-0`, `PB-ADAPTER-0`, and `PB-PY-0` family
  closeouts as lineage context:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
  - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
  - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
  - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- support doctrine:
  - `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
  - `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
  - `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
  - `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
  - `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`
  - `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`

Globs are discovery instructions, not evidence sources. Only observed
concrete files or explicitly recorded descriptor observations may become
source rows.

## 5. Shared Retry Vocabulary

Minimum retry phases:

- `retry_request_phase`
- `remand_source_index_phase`
- `retry_eligibility_phase`
- `retry_scope_contract_phase`
- `local_retry_dispatch_phase`
- `retry_execution_capture_phase`
- `retry_candidate_delta_snapshot_phase`
- `retry_lifecycle_projection_phase`
- `retry_outcome_audit_phase`
- `remand_settlement_phase`

Minimum retry posture values:

- `released_trial_remand_required`
- `single_retry_candidate_only`
- `same_lineage_required`
- `cleanroom_boundary_unchanged`
- `retry_depth_limited_to_one`
- `retry_dispatch_requires_later_lock`
- `retry_candidate_not_official_submission`
- `retry_delta_observation_not_model_ranking`
- `remand_settlement_no_second_retry_authority`

Minimum retry result states:

- `retry_eligible_for_later_local_dispatch_review`
- `retry_blocked_by_missing_trial_closeout`
- `retry_blocked_by_missing_local_remand`
- `retry_blocked_by_local_acceptance`
- `retry_blocked_by_contamination`
- `retry_blocked_by_sandbox_violation`
- `retry_blocked_by_hidden_or_forbidden_source`
- `retry_blocked_by_scope_widening`
- `retry_executed_local_only`
- `retry_locally_resolved`
- `retry_remand_still_open`
- `retry_inconclusive_local_only`
- `future_family_only`

## 6. Cross-Slice Validation Expectations

The family should validate:

- `PB-RETRY-0-A` requires released `PB-TRIAL-0` family closeout alignment;
- retry requests select exactly one trial lineage and one local remand
  decision;
- for a given `trial_lineage_ref + trial_remand_decision_ref`, only one
  `PB-RETRY-0` retry request may be eligible unless a later family grants
  retry-chain authority;
- retry lineage registry rows must list prior retry request refs or an
  explicit absence marker before eligibility can be marked ready;
- retry requests cannot cite accepted, contaminated, sandbox-blocked,
  official, hidden-test, benchmark-truth, model-ranking, or
  future-family-selected trial rows as retry-ready substrate;
- remand source indexes classify every remand source as local retryable,
  local non-retryable, blocked, support-only, or forbidden;
- hidden-test, official-evaluator, original-source, decompilation, internet,
  external-repository, host-secret, Docker-socket, postmortem-only, and
  excluded-derived refs cannot become retry source evidence;
- remand source rows cannot include hidden/forbidden source names, paths,
  excerpts, semantic summaries, test names, original-source clues, or derived
  facts;
- retry rationale kinds must be local-only; hidden-test failure, official
  evaluator feedback, source lookup facts, decompilation facts, internet
  lookup facts, external repository facts, benchmark-score pressure, and
  model-ranking pressure are forbidden;
- retry eligibility marked ready requires local-only remand source,
  clean contamination posture, same-lineage refs, unchanged cleanroom
  boundary refs, and retry depth within the declared limit;
- retry scope contracts cannot widen worker-visible source refs or allowed
  tools beyond released trial/workbench law;
- retry scope contracts must identify retry scope delta refs and unchanged
  boundary refs separately;
- retry scope contracts require unchanged boundary hashes for worker-visible
  sources, forbidden sources, tool policy, sandbox policy, write scope, and
  network policy;
- retry scope contracts require a retry scope delta manifest hash;
- retry scope delta refs may add only local retry instructions or
  remand-focused obligations; they may not add new evidence sources, tools,
  write scope, source visibility, source lookup, decompilation, Docker socket,
  host secret, or network authority;
- `PB-RETRY-0-A` rejects `PB-RETRY-0-B/C` artifact kinds;
- `PB-RETRY-0-B` requires released `PB-RETRY-0-A` refs;
- retry dispatch records enforce one retry dispatch specimen per retry
  request and one retry depth by default;
- retry dispatch records bind to a later B lock authority ref;
- retry execution capture rows require bounded transcript excerpts, output
  hashes, tool manifest hashes, worker tool-call manifest refs, forbidden
  content screen verdict, and sandbox witness refs;
- forbidden-content screen verdict must pass before retry candidate delta
  snapshots are valid;
- retry candidate delta snapshots require released write scope and same-lineage
  original candidate refs;
- retry lifecycle projections map retry evidence to released trial and
  attempt lifecycle rows and cannot define new evidence law;
- `PB-RETRY-0-C` requires released A and B refs;
- retry outcome audits cannot claim hidden-test equivalence, benchmark truth,
  official success, benchmark score, model ranking, or official submission;
- delta observation summaries are same-lineage local observations, not model
  comparison or leaderboard rows;
- remand settlement cannot grant a second retry or unbounded retry chain;
- family closeout alignment closes only `PB-RETRY-0`.

## 7. Expected Verification

When implementation begins, the default Python lane should run `make check`
before PR creation. If the starter or closeout is docs/artifacts-only, the
repo-local arc bundle shortcuts may be used with the appropriate `ARC=<n>` and
the skipped full Python lane should be stated explicitly.
