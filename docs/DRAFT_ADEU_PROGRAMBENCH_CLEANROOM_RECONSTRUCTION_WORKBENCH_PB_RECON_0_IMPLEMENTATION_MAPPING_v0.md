# Draft ADEU ProgramBench Cleanroom Reconstruction Workbench PB-RECON-0 Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-RECON-0`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`PB-RECON-0` family into likely package, schema, validator, fixture, and
evidence work so the family can be reviewed before the first active slice lock
is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v78.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`

## 1. Family Intent

`PB-RECON-0` should add a local cleanroom reconstruction workbench without
turning it into:

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

The implementation target is a typed local workbench family that can represent:

- reconstruction work orders;
- worker context packets;
- auditor-only context exclusion manifests;
- sandbox policies and run budgets;
- non-authority guardrails;
- later candidate artifact manifests;
- later local run traces and probe result logs;
- later remand/correction records;
- later local equivalence audits, result summaries, handoffs, and family
  closeout alignment.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_benchmarking`
  - ProgramBench-shaped local cleanroom reconstruction workbench models,
    enums, validators, and schema exports.
- logical module:
  - `adeu_benchmarking.programbench_cleanroom_reconstruction`
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity.
- `apps/api/fixtures/benchmarking/vnext_plus248/`
  - likely future reference and reject fixtures for `PB-RECON-0-A`, if that
    slice is selected after review.

Avoid `programbench_runner`, `programbench_eval`, `programbench_solver`,
`programbench_submitter`, and `programbench_scoreboard` names in this family.
Those names imply official benchmark, solving, evaluation, submission, or
ranking authority that the workbench does not select.

Expected starter implementation surfaces, when the first slice begins:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_reconstruction.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_reconstruction_pb_recon_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`

## 3. Candidate Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `programbench_reconstruction_work_order@1` | `PB-RECON-0-A` | released case-packet selection and worker task boundary without dispatch |
| `programbench_reconstruction_worker_context_packet@1` | `PB-RECON-0-A` | worker-visible cleanroom context derived from released case packet and realization refs |
| `programbench_reconstruction_context_exclusion_manifest@1` | `PB-RECON-0-A` | auditor-only ledger for hidden, forbidden, postmortem-only, and excluded derived-summary refs |
| `programbench_reconstruction_sandbox_policy@1` | `PB-RECON-0-A` | local sandbox, network, dependency, filesystem, and command boundary |
| `programbench_reconstruction_run_budget@1` | `PB-RECON-0-A` | local attempt, timeout, probe, and remand budget without execution |
| `programbench_reconstruction_workbench_non_authority_guardrail@1` | `PB-RECON-0-A` | guardrail preventing workbench rows from becoming official benchmark authority |
| `programbench_reconstruction_candidate_artifact_manifest@1` | `PB-RECON-0-B` | worker-generated candidate files and hashes |
| `programbench_reconstruction_local_run_trace@1` | `PB-RECON-0-B` | local sandbox command traces and bounded output evidence |
| `programbench_reconstruction_probe_result_log@1` | `PB-RECON-0-B` | local probe result rows under the work order |
| `programbench_reconstruction_remand_correction_record@1` | `PB-RECON-0-B` | remand and correction rows without hidden-test diagnosis |
| `programbench_reconstruction_equivalence_audit@1` | `PB-RECON-0-C` | local equivalence audit against case-packet observations and witness expectations |
| `programbench_reconstruction_result_summary@1` | `PB-RECON-0-C` | local accepted/remand/blocked/inconclusive summary without benchmark score |
| `programbench_reconstruction_handoff@1` | `PB-RECON-0-C` | post-workbench handoff pressure without selecting official evaluation |
| `programbench_reconstruction_workbench_family_closeout_alignment@1` | `PB-RECON-0-C` | family closeout alignment without future-family authority |

`PB-RECON-0-A` should ship only work order, worker-visible context,
auditor-only exclusion manifest, sandbox policy, run budget, guardrail, schema
export, validators, and fixtures. It should not ship candidate artifacts,
local run traces, probe result logs, equivalence audits, official runner
integration, hidden-test handling, benchmark scoring, generated submissions,
or model ranking.

## 4. Source Classes

The family should consume concrete source refs from:

- `PB-ADAPTER-0` family closeout:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
  - `apps/api/fixtures/benchmarking/vnext_plus247/programbench_cleanroom_adapter_family_closeout_alignment_v247_reference.json`
  - `artifacts/agent_harness/v247/evidence_inputs/pb_adapter_0c_case_packet_closeout_evidence_v247.json`
- `PB-ADAPTER-0` implementation surfaces:
  - `apps/api/fixtures/benchmarking/vnext_plus247/programbench_reconstruction_case_packet_v247_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus247/programbench_adapter_readiness_summary_v247_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus247/programbench_adapter_handoff_v247_reference.json`
- `PB-PY-0` family closeout:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
  - `apps/api/fixtures/benchmarking/vnext_plus244/programbench_realization_family_closeout_alignment_v244_reference.json`
- support doctrine:
  - `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
  - `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
  - `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
  - `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
  - `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`
  - `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`

Globs are discovery instructions, not evidence sources. Only observed concrete
files or explicitly recorded descriptor observations may become source rows.

## 5. Shared Workbench Vocabulary

Minimum workbench phases:

- `work_order_phase`
- `worker_context_phase`
- `local_reconstruction_phase`
- `local_probe_phase`
- `audit_phase`
- `postmortem_phase`

Minimum workbench posture values:

- `ready_case_packet_required`
- `contaminated_case_packet_blocked`
- `worker_context_cleanroom_visible_only`
- `sandbox_no_network_no_source_lookup`
- `local_probe_not_benchmark_truth`
- `candidate_not_official_submission`
- `result_not_model_ranking`
- `handoff_pressure_only`

Minimum result states:

- `local_accepted`
- `remand_required`
- `blocked_by_contamination`
- `blocked_by_sandbox_violation`
- `blocked_by_missing_evidence`
- `inconclusive_local_only`
- `future_family_only`

## 6. Cross-Slice Validation Expectations

The family should validate:

- `PB-RECON-0-A` requires released `PB-ADAPTER-0-C` case packet and readiness
  refs;
- contaminated, blocked, hidden-exposed, forbidden-exposed, or future-family
  case packets cannot become ready work orders;
- worker context packets include only cleanroom-visible and worker-authorized
  refs from the released case packet;
- context exclusion manifests are auditor-only and contain hidden, forbidden,
  postmortem-only, and excluded derived-summary refs without serving them into
  worker context;
- sandbox policy rejects network, internet lookup, original source lookup,
  decompilation, Docker socket, host-secret access, and external repo lookup;
- sandbox policy declares enforcement witness requirements for later slices:
  network disabled, source lookup disabled, decompilation disabled, Docker
  socket absent, host secrets absent, bounded filesystem write scope, and
  argv-shaped command policy;
- cross-row bundle validation resolves forward references across work order,
  worker context, exclusion manifest, sandbox policy, run budget, and guardrail
  rows as one bundle and rejects dangling or mismatched refs;
- run budget rows do not authorize execution in slice A;
- `PB-RECON-0-A` rejects `PB-RECON-0-B/C` artifact kinds;
- `PB-RECON-0-B` requires released `PB-RECON-0-A` work order, context,
  sandbox, budget, and guardrail refs;
- local run traces bind to released sandbox policy, released run budget,
  command authority refs, command allowlist match refs, sandbox attestations,
  network attestations, secret-absence attestations, dependency posture,
  write-scope attestations, and artifact capture policy refs;
- candidate artifact manifests cannot claim official submission status;
- local run traces must use argv-shaped commands and bounded outputs;
- local probe result logs cannot claim benchmark truth or hidden-test
  equivalence;
- remand/correction records cannot introduce hidden tests, original source,
  or decompilation evidence;
- remand/correction records cite only local cleanroom remand sources such as
  local probe failure, local sandbox violation, missing required artifact,
  unsupported behavior gap, or inconclusive trace;
- `PB-RECON-0-C` requires released `PB-RECON-0-A/B` refs;
- equivalence audits distinguish local probe evidence from official
  evaluator evidence;
- result summaries cannot rank models or create benchmark scores;
- local accepted result summaries require no contamination, no sandbox
  violations, required positive probes passed, required negative probes passed
  or marked not-applicable with reason, stdout/stderr/exit-code expectations
  satisfied, required filesystem side-effect expectations satisfied, and no
  missing required evidence blockers;
- family closeout alignment closes only `PB-RECON-0`;
- official ProgramBench participation, official evaluator integration,
  hidden-test handling, benchmark scoring, product authority, graph authority,
  release, recursive policy amendment, and future-family selection remain
  absent unless later selected by a separate lock.
