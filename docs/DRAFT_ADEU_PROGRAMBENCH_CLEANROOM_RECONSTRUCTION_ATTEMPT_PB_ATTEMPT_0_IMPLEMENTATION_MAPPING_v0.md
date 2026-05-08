# Draft ADEU ProgramBench Cleanroom Reconstruction Attempt PB-ATTEMPT-0 Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-ATTEMPT-0`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`PB-ATTEMPT-0` family into likely package, schema, validator, fixture, and
evidence work so the family can be reviewed before the first active slice lock
is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v79.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`

## 1. Family Intent

`PB-ATTEMPT-0` should add a local cleanroom reconstruction attempt harness
without turning it into:

- official ProgramBench participation, official task execution, official
  runner integration, official evaluator integration, benchmark submission,
  benchmark scoring, benchmark truth, hidden-test inference, hidden-test
  equivalence, or model ranking;
- original source lookup, decompilation, internet lookup, external source
  repository lookup, Docker socket access, or host-secret access;
- generated official submissions or official solver outputs;
- arbitrary command execution outside a selected local sandbox;
- product authority, graph-memory authority, recursive policy amendment, PR
  creation, commit, merge, or release;
- `V86`, `V87`, `V88`, canonical implementation-lock review, official
  ProgramBench participation, or any other future-family selection.

The implementation target is a typed local attempt family that can represent:

- attempt requests;
- worker input packets;
- dispatch eligibility and sandbox preflight;
- non-authority guardrails;
- later worker invocation records;
- later output captures;
- later candidate materialization records;
- later sandbox application traces;
- later workbench evidence exports;
- later attempt result reviews;
- later remand queues;
- later attempt family closeout alignment.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_benchmarking`
  - ProgramBench-shaped local cleanroom attempt models, enums, validators,
    and schema exports.
- logical module:
  - `adeu_benchmarking.programbench_cleanroom_attempt`
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity.
- `apps/api/fixtures/benchmarking/vnext_plus251/`
  - likely future reference and reject fixtures for `PB-ATTEMPT-0-A`, if that
    slice is selected after review.

Avoid `programbench_runner`, `programbench_eval`, `programbench_solver`,
`programbench_submitter`, and `programbench_scoreboard` names in this family.
Those names imply official benchmark, solving, evaluation, submission, or
ranking authority that the attempt harness does not select.

Expected starter implementation surfaces, when the first slice begins:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_attempt.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_attempt_pb_attempt_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`

If later slices need generic model/agent invocation logging beyond
ProgramBench-shaped local reconstruction, that split should be selected by a
future family. `PB-ATTEMPT-0` should keep the attempt records in the
benchmarking lane.

## 3. Candidate Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `programbench_reconstruction_attempt_request@1` | `PB-ATTEMPT-0-A` | released workbench selection, worker profile, attempt purpose, and non-dispatch posture |
| `programbench_reconstruction_attempt_worker_input_packet@1` | `PB-ATTEMPT-0-A` | exact worker-visible input refs and advisory context derived from released workbench rows |
| `programbench_reconstruction_attempt_dispatch_preflight@1` | `PB-ATTEMPT-0-A` | eligibility, sandbox/budget closure, and enforcement witness requirements before any invocation |
| `programbench_reconstruction_attempt_non_authority_guardrail@1` | `PB-ATTEMPT-0-A` | guardrail preventing attempt rows from becoming official benchmark authority |
| `programbench_reconstruction_attempt_worker_invocation_record@1` | `PB-ATTEMPT-0-B` | one bounded local worker invocation under released attempt refs |
| `programbench_reconstruction_attempt_output_capture@1` | `PB-ATTEMPT-0-B` | worker output hashes, bounded excerpts, uncertainty rows, and forbidden-content screening |
| `programbench_reconstruction_attempt_candidate_materialization@1` | `PB-ATTEMPT-0-B` | sandbox-bound candidate file materialization and hash rows |
| `programbench_reconstruction_attempt_sandbox_application_trace@1` | `PB-ATTEMPT-0-B` | local application trace, write-scope attestation, and application failure rows |
| `programbench_reconstruction_attempt_workbench_evidence_export@1` | `PB-ATTEMPT-0-C` | export of attempt capture into released `PB-RECON-0` evidence shape refs |
| `programbench_reconstruction_attempt_result_review@1` | `PB-ATTEMPT-0-C` | local attempt result posture without benchmark truth or model ranking |
| `programbench_reconstruction_attempt_remand_queue@1` | `PB-ATTEMPT-0-C` | local remand/retry queue without hidden-test diagnosis |
| `programbench_reconstruction_attempt_family_closeout_alignment@1` | `PB-ATTEMPT-0-C` | family closeout alignment without future-family authority |

`PB-ATTEMPT-0-A` should ship only attempt request, worker input packet,
dispatch preflight, guardrail, schema export, validators, and fixtures. It
should not ship worker invocation records, output captures, candidate
materialization, local run traces, probe result logs, workbench evidence
exports, result reviews, remand queues, official runner integration,
hidden-test handling, benchmark scoring, generated official submissions, or
model ranking.

## 4. Source Classes

The family should consume concrete source refs from:

- `PB-RECON-0` family closeout:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
  - `apps/api/fixtures/benchmarking/vnext_plus250/programbench_reconstruction_workbench_family_closeout_alignment_v250_reference.json`
  - `artifacts/agent_harness/v250/evidence_inputs/pb_recon_0c_local_audit_closeout_evidence_v250.json`
- `PB-RECON-0` implementation surfaces:
  - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_work_order_v248_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_worker_context_packet_v248_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_context_exclusion_manifest_v248_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_sandbox_policy_v248_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_run_budget_v248_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_workbench_non_authority_guardrail_v248_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus249/programbench_reconstruction_candidate_artifact_manifest_v249_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus249/programbench_reconstruction_local_run_trace_v249_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus249/programbench_reconstruction_probe_result_log_v249_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus249/programbench_reconstruction_remand_correction_record_v249_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus250/programbench_reconstruction_equivalence_audit_v250_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus250/programbench_reconstruction_result_summary_v250_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus250/programbench_reconstruction_handoff_v250_reference.json`
- `PB-ADAPTER-0` and `PB-PY-0` family closeouts as lineage context:
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

## 5. Shared Attempt Vocabulary

Minimum attempt phases:

- `attempt_request_phase`
- `worker_input_phase`
- `dispatch_preflight_phase`
- `local_worker_invocation_phase`
- `candidate_materialization_phase`
- `evidence_export_phase`
- `remand_phase`

Minimum attempt posture values:

- `released_workbench_required`
- `workbench_remand_posture_allowed_for_attempt_if_remand_targeted`
- `worker_input_cleanroom_visible_only`
- `dispatch_preflight_passed_for_later_local_attempt`
- `dispatch_preflight_blocked`
- `candidate_not_official_submission`
- `attempt_result_not_benchmark_truth`
- `remand_queue_local_only`

Minimum attempt result states:

- `attempt_ready_for_local_worker_invocation_review`
- `attempt_blocked_by_workbench_posture`
- `attempt_blocked_by_visibility_gap`
- `attempt_blocked_by_sandbox_preflight`
- `attempt_output_captured`
- `attempt_materialized_locally`
- `attempt_exported_to_workbench_evidence`
- `attempt_remand_queued`
- `attempt_inconclusive_local_only`
- `future_family_only`

## 6. Cross-Slice Validation Expectations

The family should validate:

- `PB-ATTEMPT-0-A` requires released `PB-RECON-0` workbench refs and family
  closeout alignment;
- attempt requests cannot cite contaminated, hidden-exposed,
  forbidden-exposed, official, benchmark-truth, model-ranking, or
  future-family-selected workbench rows;
- attempt requests consume only compatible `PB-RECON-0` result summaries:
  remand-required, inconclusive-local, or missing-evidence-blocked states
  with explicit remand/evidence-gap purpose;
- local accepted, contamination-blocked, sandbox-violation-blocked, and
  future-family-only workbench summaries are rejected as attempt substrates
  unless a later lock adds a narrower exception;
- worker input packets include only worker-visible refs from the released
  workbench context packet and advisory refs explicitly allowed by the
  workbench;
- worker input packets cannot include auditor-only exclusion refs, forbidden
  refs, postmortem-only refs, original-source refs, hidden-test refs,
  decompilation refs, internet lookup refs, external repo refs, host-secret
  refs, or Docker-socket refs;
- worker input packets require `worker_input_manifest_hash`,
  `worker_visible_ref_count`, and `forbidden_ref_exposure_check_hash`;
- excluded-ref summary rows may include only exclusion category, count, reason
  code, authority posture, and non-exposure statement; they must reject source
  paths, source names, content excerpts, semantic summaries, derived facts,
  test names, hidden artifact identifiers, and original-source clues;
- dispatch preflight is review posture in slice A, not invocation authority;
- dispatch preflight requires
  `preflight_scope_posture = eligibility_review_only_no_invocation`;
- dispatch preflight binds to sandbox policy, run budget, worker profile,
  attempt request, worker input packet, and guardrail refs;
- `PB-ATTEMPT-0-A` rejects `PB-ATTEMPT-0-B/C` artifact kinds;
- `PB-ATTEMPT-0-B` requires released `PB-ATTEMPT-0-A` refs;
- `PB-ATTEMPT-0-B` enforces one worker invocation per attempt request unless
  a later retry parent and retry authority surface is selected;
- worker invocation records bind to one released attempt request and one
  dispatch preflight;
- worker invocation records require input packet hash, worker-visible context
  hash, tool manifest ref, allowed tool manifest hash, and forbidden tool
  manifest hash;
- worker output capture requires hashes and bounded excerpts and cannot expose
  hidden, forbidden, or excluded-derived evidence;
- output capture requires a closed
  `forbidden_content_screening_posture`; candidate materialization is allowed
  only when that posture is passed;
- candidate materialization can write only inside released sandbox write
  scope and cannot claim official submission posture;
- candidate materialization requires materialization input hash,
  materialization output manifest hash, and explicit
  `materialized_inside_write_scope = true`;
- sandbox application traces require write-scope, network-disabled,
  source-lookup-disabled, secret-absence, and Docker-socket-absence
  attestations;
- `PB-ATTEMPT-0-C` requires released `PB-ATTEMPT-0-A/B` refs;
- evidence exports map attempt artifacts to existing `PB-RECON-0` evidence
  shapes without redefining those shapes or bypassing their validators;
- evidence exports require `pb_recon_validation_result_refs`, and positive
  reviews require those validator results to pass;
- attempt result reviews cannot claim hidden-test equivalence, benchmark
  truth, official evaluator truth, benchmark score, model ranking, or official
  submission authority;
- `attempt_locally_accepted` requires an exported `PB-RECON-0`
  local-accepted result summary, no contamination blockers, no sandbox
  violation blockers, no export gaps, no hidden-test equivalence posture, and
  no official submission posture;
- remand queues cite only local workbench evidence and cannot use hidden-test,
  official evaluator, original source, decompilation, internet, or external
  repo diagnostics;
- remand queue source kinds are closed to local probe failure, local output
  capture gap, materialization gap, sandbox application failure, exported
  workbench gap, and worker-declared uncertainty;
- remand queue rows cannot become retry authority by themselves;
- family closeout alignment closes only `PB-ATTEMPT-0`;
- official ProgramBench participation, official evaluator integration,
  hidden-test handling, benchmark scoring, product authority, graph authority,
  release, recursive policy amendment, and future-family selection remain
  absent unless later selected by a separate lock.

## 7. Expected Review Risks

- Worker input packets may accidentally launder auditor-only exclusions into
  worker-visible context.
- Dispatch preflight may be overread as worker-dispatch authority in slice A.
- Worker output capture may contain forbidden summaries or hidden evidence if
  screening is not explicit.
- Candidate materialization may be confused with official submission.
- Evidence export may bypass the already released `PB-RECON-0` validators.
- Attempt result review may be overread as benchmark truth or model ranking.
- Remand queue entries may be treated as permission to use hidden tests or
  original source diagnostics.

## 8. Suggested Verification Shape

When active slices are selected, tests should include:

- positive reference fixture for each selected shape;
- reject fixture for worker-visible auditor-only ref leakage;
- reject fixture for dispatch preflight granting invocation authority in
  slice A;
- reject fixture for official ProgramBench, hidden-test, benchmark-truth,
  model-ranking, or official-submission posture;
- cross-row bundle validator requiring released predecessor refs;
- schema export mirror parity with `spec/`;
- absence checks for future-slice artifact kinds in earlier slices.
