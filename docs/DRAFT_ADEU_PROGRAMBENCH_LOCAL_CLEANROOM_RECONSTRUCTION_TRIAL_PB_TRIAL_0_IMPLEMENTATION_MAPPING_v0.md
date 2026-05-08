# Draft ADEU ProgramBench Local Cleanroom Reconstruction Trial PB-TRIAL-0 Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-TRIAL-0`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`PB-TRIAL-0` family into likely package, schema, validator, fixture, artifact,
and evidence work so the family can be reviewed before the first active slice
lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v80.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`

## 1. Family Intent

`PB-TRIAL-0` should add a single local cleanroom reconstruction trial over the
released `PB-ATTEMPT-0` lifecycle without turning it into:

- official ProgramBench participation, official task execution, official
  runner integration, official evaluator integration, benchmark submission,
  benchmark scoring, benchmark truth, hidden-test inference, hidden-test
  equivalence, or model ranking;
- retry dispatch authority or multi-attempt comparison;
- original source lookup, decompilation, internet lookup, external source
  repository lookup, Docker socket access, or host-secret access;
- generated official submissions or official solver outputs;
- arbitrary command execution outside a released local sandbox;
- product authority, graph-memory authority, recursive policy amendment, PR
  creation, commit, merge, or release;
- `V86`, `V87`, `V88`, canonical implementation-lock review, official
  ProgramBench participation, or any other future-family selection.

The implementation target is a typed local trial family that can represent:

- trial dockets;
- local trial execution runbooks;
- sandbox readiness reviews;
- trial non-authority guardrails;
- later local worker dispatch records;
- later execution capture rows;
- later candidate artifact snapshots;
- later lifecycle projections onto `PB-ATTEMPT-0` rows;
- later local outcome audits;
- later trial observation summaries;
- later remand decisions;
- later trial family closeout alignment.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_benchmarking`
  - ProgramBench-shaped local cleanroom trial models, enums, validators, and
    schema exports.
- logical module:
  - `adeu_benchmarking.programbench_cleanroom_trial`
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity.
- `apps/api/fixtures/benchmarking/vnext_plus254/`
  - likely future reference and reject fixtures for `PB-TRIAL-0-A`, if that
    slice is selected after review.

Avoid `programbench_runner`, `programbench_eval`, `programbench_solver`,
`programbench_submitter`, and `programbench_scoreboard` names in this family.
Those names imply official benchmark, solving, evaluation, submission, or
ranking authority that the local trial family does not select.

Expected starter implementation surfaces, when the first slice begins:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_trial.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_trial_pb_trial_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`

If later slices need generic model/agent dispatch beyond ProgramBench-shaped
local reconstruction, that split should be selected by a future family.
`PB-TRIAL-0` should keep the trial records in the benchmarking lane.

## 3. Candidate Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `programbench_local_reconstruction_trial_docket@1` | `PB-TRIAL-0-A` | one released attempt package selected as local trial candidate |
| `programbench_local_trial_execution_runbook@1` | `PB-TRIAL-0-A` | allowed local steps, capture obligations, and no-dispatch posture |
| `programbench_local_trial_sandbox_readiness_review@1` | `PB-TRIAL-0-A` | sandbox, budget, tool, and worker-visible packet readiness before execution |
| `programbench_local_trial_non_authority_guardrail@1` | `PB-TRIAL-0-A` | guardrail preventing trial rows from becoming official benchmark or retry authority |
| `programbench_local_trial_worker_dispatch_record@1` | `PB-TRIAL-0-B` | one local worker dispatch specimen under released A refs |
| `programbench_local_trial_execution_capture@1` | `PB-TRIAL-0-B` | transcript/output/artifact hashes, bounded excerpts, and sandbox witnesses |
| `programbench_local_trial_candidate_artifact_snapshot@1` | `PB-TRIAL-0-B` | sandbox-local candidate files and manifests |
| `programbench_local_trial_lifecycle_projection@1` | `PB-TRIAL-0-B` | mapping from trial specimen evidence to released `PB-ATTEMPT-0` row refs |
| `programbench_local_trial_outcome_audit@1` | `PB-TRIAL-0-C` | local-only audit against runbook, lifecycle projection, and workbench evidence |
| `programbench_local_trial_observation_summary@1` | `PB-TRIAL-0-C` | non-ranking summary of what the single trial showed |
| `programbench_local_trial_remand_decision@1` | `PB-TRIAL-0-C` | local remand pressure without retry authority |
| `programbench_local_trial_family_closeout_alignment@1` | `PB-TRIAL-0-C` | family closeout alignment without future-family authority |

`PB-TRIAL-0-A` should ship only trial docket, execution runbook, sandbox
readiness review, guardrail, schema export, validators, and fixtures. It
should not ship worker dispatch records, execution capture, candidate
artifact snapshots, lifecycle projection rows, outcome audit, observation
summary, remand decision, official runner integration, hidden-test handling,
benchmark scoring, generated official submissions, retry authority, or model
ranking.

## 4. Source Classes

The family should consume concrete source refs from:

- `PB-ATTEMPT-0` family closeout:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
  - `apps/api/fixtures/benchmarking/vnext_plus253/programbench_reconstruction_attempt_family_closeout_alignment_v253_reference.json`
  - `artifacts/agent_harness/v253/evidence_inputs/pb_attempt_0c_attempt_closeout_evidence_v253.json`
- `PB-ATTEMPT-0` implementation surfaces:
  - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_request_v251_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_worker_input_packet_v251_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_dispatch_preflight_v251_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_non_authority_guardrail_v251_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus252/programbench_reconstruction_attempt_worker_invocation_record_v252_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus252/programbench_reconstruction_attempt_output_capture_v252_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus252/programbench_reconstruction_attempt_candidate_materialization_v252_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus252/programbench_reconstruction_attempt_sandbox_application_trace_v252_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus253/programbench_reconstruction_attempt_workbench_evidence_export_v253_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus253/programbench_reconstruction_attempt_result_review_v253_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus253/programbench_reconstruction_attempt_remand_queue_v253_reference.json`
- `PB-RECON-0`, `PB-ADAPTER-0`, and `PB-PY-0` family closeouts as lineage
  context:
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

## 5. Shared Trial Vocabulary

Minimum trial phases:

- `trial_docket_phase`
- `trial_runbook_phase`
- `sandbox_readiness_phase`
- `local_dispatch_phase`
- `execution_capture_phase`
- `candidate_snapshot_phase`
- `lifecycle_projection_phase`
- `outcome_audit_phase`
- `remand_decision_phase`

Minimum trial posture values:

- `released_attempt_lifecycle_required`
- `single_trial_only`
- `worker_input_packet_hash_bound`
- `sandbox_readiness_required_before_execution`
- `trial_ready_for_later_local_dispatch`
- `trial_blocked_by_readiness_gap`
- `trial_executed_local_only`
- `candidate_snapshot_not_official_submission`
- `trial_observation_not_benchmark_truth`
- `remand_pressure_no_retry_authority`

Minimum trial result states:

- `trial_ready_for_local_execution_review`
- `trial_blocked_by_attempt_lifecycle_gap`
- `trial_blocked_by_worker_input_gap`
- `trial_blocked_by_sandbox_readiness_gap`
- `trial_executed_local_only`
- `trial_candidate_snapshotted`
- `trial_lifecycle_projected`
- `trial_locally_accepted`
- `trial_remand_recommended`
- `trial_inconclusive_local_only`
- `future_family_only`

## 6. Cross-Slice Validation Expectations

The family should validate:

- `PB-TRIAL-0-A` requires released `PB-ATTEMPT-0` family closeout alignment;
- trial dockets select exactly one local attempt package and one local case
  lineage;
- trial dockets cannot cite official, hidden-test, benchmark-truth,
  model-ranking, retry-authority, or future-family-selected rows;
- execution runbooks bind to one trial docket, one attempt request, one worker
  input packet hash, one dispatch preflight, one sandbox policy, one run
  budget, one guardrail, one runbook hash, one trial input materialization
  policy ref, and sandbox witness requirement refs;
- execution runbooks are plans in slice A and cannot dispatch a worker;
- sandbox readiness reviews require network-disabled, source-lookup-disabled,
  decompilation-disabled, Docker-socket-absent, host-secret-absent,
  write-scope-bounded, and tool-manifest-closed readiness rows;
- sandbox readiness reviews marked ready require every readiness row to be
  tied to a later B witness requirement;
- consumed `PB-ATTEMPT-0` result-review rows may be lifecycle context only and
  cannot be counted as `PB-TRIAL-0` outcome evidence;
- `PB-TRIAL-0-A` rejects `PB-TRIAL-0-B/C` artifact kinds;
- `PB-TRIAL-0-B` requires released `PB-TRIAL-0-A` refs;
- worker dispatch records enforce one dispatch specimen per trial docket;
- worker dispatch records bind to the runbook and worker input packet hash;
- worker dispatch records require `dispatch_authority_ref`,
  `sandbox_instance_ref`, `sandbox_attestation_bundle_ref`, and
  `input_packet_materialization_hash`;
- execution capture rows require bounded transcript excerpts, full transcript
  hash, output hashes, tool manifest hashes, worker tool-call manifest refs,
  full output capture policy refs, and sandbox witness refs;
- forbidden-content screen verdict must pass before candidate snapshots are
  valid;
- candidate snapshots require released write scope, generated-file hashes, and
  non-official-submission posture;
- lifecycle projections map trial evidence to released `PB-ATTEMPT-0` rows and
  cannot define new evidence law;
- `PB-TRIAL-0-C` requires released A and B refs;
- outcome audits cannot claim hidden-test equivalence, benchmark truth,
  official success, benchmark score, model ranking, or official submission;
- local acceptance requires a candidate snapshot inside released write scope
  and lifecycle projection validator pass against released `PB-ATTEMPT-0`
  bindings;
- trial observation summaries are single-trial observations, not model
  comparison or leaderboard rows;
- trial observation summaries cannot contain comparative language across
  models, attempts, retries, or benchmark rows;
- remand decisions cannot grant retry dispatch authority;
- family closeout alignment closes only `PB-TRIAL-0`.

## 7. Expected Verification

When implementation begins, the default Python lane should run `make check`
before PR creation. If the starter or closeout is docs/artifacts-only, the
repo-local arc bundle shortcuts may be used with the appropriate `ARC=<n>` and
the skipped full Python lane should be stated explicitly.
