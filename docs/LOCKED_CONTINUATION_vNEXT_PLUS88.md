# Locked Continuation vNext+88

Status: `V41-F` implementation contract.

## V88 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v41f_practical_analysis_runner_contract@1",
  "target_arc": "vNext+88",
  "target_path": "V41-F",
  "target_scope": "practical_analysis_runner_and_habitual_orchestration_baseline",
  "analysis_request_schema": "adeu_architecture_analysis_request@1",
  "analysis_settlement_schema": "adeu_architecture_analysis_settlement_frame@1",
  "observation_frame_schema": "adeu_architecture_observation_frame@1",
  "semantic_ir_schema": "adeu_architecture_semantic_ir@1",
  "alignment_report_schema": "adeu_architecture_alignment_report@1",
  "run_manifest_schema": "adeu_architecture_analysis_run_manifest@1",
  "implementation_package": "adeu_architecture_compiler",
  "authoritative_request_package": "adeu_architecture_ir",
  "authoritative_intended_package": "adeu_architecture_ir",
  "authoritative_intended_comparison_surface": "adeu_architecture_semantic_ir@1",
  "runner_requires_distinct_intended_and_observed_artifacts": true,
  "run_manifest_emitted_on_blocked_run": true,
  "run_id_deterministic": true,
  "stage_ledger_required": true,
  "settlement_context_required": true,
  "cli_first_runner": true,
  "repo_mutation_deferred": true,
  "remediation_deferred": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "decomposition_doc": "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v23.md"
}
```

## Slice

- Arc label: `vNext+88`
- Family label: `V41-F`
- Scope label: practical analysis runner and habitual orchestration baseline

## Objective

Introduce the first concrete practical-runner slice by activating only the
orchestration lane and freezing one canonical
`adeu_architecture_analysis_run_manifest@1` artifact over the released `V41-A`
request boundary, `V41-B` settlement frame, `V41-C` observation frame, `V41-D`
intended semantic-root outputs, and `V41-E` alignment report before any remediation,
repo-mutation, workbench, or merged-truth surface is released.

This slice establishes the first repo-native practical-analysis substrate for:

- canonical `adeu_architecture_analysis_run_manifest@1`;
- one canonical CLI-first runner over the released `V41-A` through `V41-E` stack;
- exact sequencing for request capture, settlement, observation, intended compile,
  and alignment over one bounded repo scope;
- deterministic run identity plus deterministic output-root and runtime-evidence-root
  placement;
- explicit runner-level stop posture when settlement blocks intended compile or
  alignment emission;
- explicit distinction between runner-level blocked stop and a completed run whose
  consumed alignment report may still carry `alignment_posture = blocked`;
- committed runner fixture ladders proving full-run replay and settlement-blocked stop
  replay without repo mutation or merged-truth reconciliation.

This slice remains deliberately prior to:

- remediation planning;
- repo mutation or code-edit authority;
- API or web inspection surfaces;
- multi-repo fleet orchestration;
- automatic reconciliation of intended and observed lanes;
- checkpoint, projection, or UX practical reruns inside the runner;
- direct prompt-to-code generation.

Its job is to make the already-released practical-analysis stack runnable habitually
over one repo scope before any later slice widens that runner into mutation,
remediation, or broader product surfaces.

## Frozen Implementation Decisions

1. Active package strategy:
   - activate the practical runner lane in `packages/adeu_architecture_compiler` for
     `vNext+88`;
   - `packages/adeu_architecture_ir` remains authoritative for the released `V41-A`,
     `V41-B`, and `V41-D` upstream artifacts and may not be silently redefined by
     runner-local vocabulary.
2. Orchestration sequencing strategy:
   - `vNext+88` must orchestrate the released practical-analysis stack in this exact
     order:
     - analysis request
     - settlement frame
     - observation frame
     - intended semantic IR
     - alignment report
     - analysis run manifest
   - request, settlement, and observation may be materialized over a settlement world
     that is either `entitled` or `blocked`;
   - intended semantic IR and alignment report may be materialized only after the
     consumed settlement frame remains `compile_entitlement = entitled` with no
     blocking lineage.
3. Upstream consumption strategy:
   - `vNext+88` must materialize or consume one released `V41-A` analysis request,
     one released `V41-B` settlement frame, one released `V41-C` observation frame,
     one released `V41-D` intended semantic IR, and one released `V41-E` alignment
     report, or exact validated derivatives thereof, over one bounded repo world;
   - it may not bypass the released repo world with ambient working-tree reads,
     unbound file selection, free-floating prose, or runner-local reinterpretation of
     the request / settlement / observation / intended / alignment seams;
   - the run manifest must bind back to the same:
     - `analysis_request_id`
     - `analysis_request_ref`
     - `settlement_frame_id`
     - `settlement_frame_ref`
     - `observation_frame_id`
     - `observation_frame_ref`
     - `semantic_ir_id`
     - `semantic_ir_ref`
     - `alignment_report_id`
     - `alignment_report_ref`
     - `architecture_id`
     - `semantic_hash`
     - `source_set_hash`
     - `authority_boundary_policy`
     carried by the released upstream artifacts whenever those artifacts are lawfully
     emitted in the run.
   - every lawfully emitted upstream artifact consumed by the runner must appear in
     the manifest with both its canonical `*_id` and `*_ref`;
   - upstream artifacts that are not lawfully emitted in a blocked run may not be
     backfilled into the manifest by inference or placeholder refs.
4. Run-manifest strategy:
   - `adeu_architecture_analysis_run_manifest@1` is the only newly released artifact
     family in this slice;
   - authoritative JSON schema must live under
     `packages/adeu_architecture_compiler/schema/`;
   - mirrored export must live under `spec/`;
   - mirrored export must match the authoritative schema byte-for-byte after
     canonical export;
   - `run_id` must be derived deterministically from a canonical hash over the tuple:
     - `analysis_request_id`
     - `settlement_frame_id`
     - `observation_frame_id`
     - `semantic_ir_id` or canonical absent marker
     - `alignment_report_id` or canonical absent marker
     - canonical runner name / version / mode
   - the run manifest must carry a canonical `stage_statuses` ledger for exactly:
     - `request`
     - `settlement`
     - `observation`
     - `intended`
     - `alignment`
     - `manifest`
   - each `stage_statuses` entry must classify stage state as exactly:
     - `completed`
     - `not_run`
   - the run manifest carries orchestration lineage, deterministic placement, and
     stop posture only and may not become remediation, repo-mutation, or merged-truth
     authority.
5. Runner-outcome strategy:
   - the run manifest must classify runner outcome as exactly:
     - `completed`
     - `blocked`
   - the run manifest must classify stop reason as exactly:
     - `none`
     - `settlement_blocked`
   - `blocked` is legal only when the consumed settlement frame is
     `compile_entitlement = blocked` or carries non-empty blocking lineage;
   - a settlement-blocked run still emits one authoritative
     `adeu_architecture_analysis_run_manifest@1` as the canonical stop witness for
     that run;
   - a `blocked` run must stop after the observation frame and emit no
     `semantic_ir_id`, `semantic_ir_ref`, `alignment_report_id`,
     `alignment_report_ref`, or shadow artifact refs under the released intended or
     alignment family names;
   - a `blocked` run must record `stage_statuses` with:
     - `request = completed`
     - `settlement = completed`
     - `observation = completed`
     - `intended = not_run`
     - `alignment = not_run`
     - `manifest = completed`
   - `completed` is legal only when intended semantic IR and alignment report are
     both materialized lawfully and `stop_reason_kind = none`;
   - a `completed` run must record every stage in `stage_statuses` as `completed`;
   - a completed run may still consume an alignment report whose
     `alignment_posture = blocked` or `drifted`; runner completion is not equivalent
     to alignment success.
6. Deterministic placement and evidence strategy:
   - `output_root_ref`, `runtime_evidence_root_ref`, and `run_id` may depend only on
     canonical run inputs and frozen runner configuration, never on wall-clock
     naming, temp-dir randomness, or ambient working-tree state;
   - the runner must emit deterministic `output_root_ref` and
     `runtime_evidence_root_ref` values for a given canonical run input;
   - `emitted_artifact_refs` must list exactly the artifact refs actually emitted in
     canonical deterministic order;
   - runtime evidence remains required and informational-only in this slice and may
     not by itself redefine released artifact truth.
7. Authority-boundary strategy:
   - request boundary plus settlement frame remain the normative driver of intended
     truth throughout the run and may not be recomputed locally;
   - observation may constrain, block, or force unresolved posture, but it may not
     become the hidden source of intended truth;
   - the runner may not auto-accept drift, reconcile intended and observed lanes, or
     translate alignment findings into mutation authority.
8. Path decomposition strategy:
   - `vNext+88` is the first concrete `V41-F` arc;
   - any later widening into remediation planning, repo mutation, API/workbench
     release, or multi-repo orchestration remains available only for later concrete
     arcs outside this baseline.

## Required Deliverables

1. New typed practical-analysis runner surface:
   - extend `packages/adeu_architecture_compiler` with deterministic helpers that
     materialize canonical `adeu_architecture_analysis_run_manifest@1` plus the
     released `V41-A` through `V41-E` artifact sequence;
   - export schema helpers needed for authoritative and mirrored JSON-schema output;
   - keep remediation, repo mutation, checkpoint, projection, UX, and web/workbench
     surfaces out of scope.
2. Canonical practical-analysis orchestration artifact:
   - `adeu_architecture_analysis_run_manifest@1`
3. Deterministic runner entrypoints that:
   - materialize one released `adeu_architecture_analysis_request@1`, one released
     `adeu_architecture_analysis_settlement_frame@1`, one released
     `adeu_architecture_observation_frame@1`, one released
     `adeu_architecture_semantic_ir@1`, and one released
     `adeu_architecture_alignment_report@1` in exact lawful sequence when the
     released gates allow;
   - materialize `adeu_architecture_analysis_run_manifest@1`;
   - fail closed when request lineage, settlement lineage, observation lineage,
     intended lineage, alignment lineage, source-set identity, or released runner
     validation is invalid.
4. Top-level schema anchors for `adeu_architecture_analysis_run_manifest@1`:
   - `schema`
   - `run_id`
   - `runner`
   - `repo_root_ref`
   - `output_root_ref`
   - `runtime_evidence_root_ref`
   - `analysis_request_id`
   - `analysis_request_ref`
   - `settlement_frame_id`
   - `settlement_frame_ref`
   - `observation_frame_id`
   - `observation_frame_ref`
   - `semantic_ir_id`
   - `semantic_ir_ref`
   - `alignment_report_id`
   - `alignment_report_ref`
   - `architecture_id`
   - `source_set_hash`
   - `authority_boundary_policy`
   - `run_outcome`
   - `stop_reason_kind`
   - `terminal_alignment_posture`
   - `stage_statuses`
   - `emitted_artifact_refs`
   - `terminal_alignment_posture` must classify terminal alignment as exactly:
     - `none`
     - `aligned`
     - `drifted`
     - `blocked`
   - `terminal_alignment_posture = none` is required when `run_outcome = blocked`.
5. Deterministic runner laws that fail closed on at least:
   - any request / settlement / observation / intended / alignment lineage drift
     against the released repo world;
   - any attempt to materialize intended semantic IR or alignment report after a
     settlement-blocked stop;
   - any `blocked` run that fails to emit an authoritative run manifest as the
     canonical stop witness;
   - any `blocked` run that still emits `semantic_ir_id`, `semantic_ir_ref`,
     `alignment_report_id`, `alignment_report_ref`, or artifact-shaped shadows under
     the released intended or alignment family names;
   - any `completed` run that omits a released intended semantic IR or alignment
     report;
   - any blocked run whose `terminal_alignment_posture` is not exactly `none`;
   - any completed run whose `terminal_alignment_posture` disagrees with the consumed
     alignment report;
   - any `stage_statuses` ledger that is incomplete, out of canonical stage order, or
     disagrees with the emitted artifact set and runner outcome;
   - any `emitted_artifact_refs` set that is incomplete, contains non-emitted refs,
     or is not canonically ordered;
   - any attempt to recompute settlement entitlement or alignment posture locally
     rather than consuming the released upstream artifacts as-is;
   - any attempt to embed remediation plans, repo-mutation instructions, or
     merged-truth state into the run manifest.
6. Committed reference fixtures:
   - one accepted runner fixture ladder under
     `apps/api/fixtures/architecture/vnext_plus88/` covering:
     - one completed run over the full released `V41-A` through `V41-E` stack
     - one settlement-blocked stop before intended or alignment emission
     - canonical run-manifest outputs for both cases
   - the accepted fixture ladder must prove:
     - deterministic full-run replay;
     - deterministic blocked-stop replay;
     - deterministic `run_id` derivation;
     - exact sequencing across the released stack;
     - authoritative manifest emission for blocked runs;
     - canonical `stage_statuses` ledger replay for both cases;
     - explicit distinction between runner-level blocked stop and a completed run
       whose emitted alignment report may itself carry `alignment_posture = blocked`;
     - no shadow intended or alignment artifacts exist in the blocked case.
7. Python tests covering:
   - schema/model validation for `adeu_architecture_analysis_run_manifest@1`;
   - authoritative/mirrored schema export parity;
   - deterministic full-run replay from the accepted fixture ladder;
   - deterministic blocked-stop replay from the accepted fixture ladder;
   - deterministic `run_id` derivation from canonical run inputs;
   - exact sequencing and emitted-artifact ordering;
   - canonical `stage_statuses` ledger derivation;
   - distinction between runner-level blocked stop and alignment-level blocked
     posture;
   - blocked-run `terminal_alignment_posture = none`;
   - rejection of repo-mutation, remediation, or merged-truth fields inside the
     runner lane.

## Hard Constraints

- `vNext+88` may not reopen or redefine the released `V41-A`, `V41-B`, `V41-C`,
  `V41-D`, or `V41-E` contracts.
- `vNext+88` may not ship:
  - remediation plans,
  - repo mutation or code-edit authority,
  - API or web workbench routes,
  - multi-repo fleet orchestration,
  - merged-truth reconciliation,
  - repo-grounded checkpoint/projection/UX practical outputs,
  - direct prompt-to-code generation.
- runner-level `run_outcome = blocked` may not be used to describe a completed run
  whose emitted alignment report merely carries `alignment_posture = blocked`.
- a settlement-blocked run may not emit shadow advisory intended or alignment
  artifacts under the released family names.
- runtime evidence remains informational-only and may not silently redefine emitted
  artifact truth.
- the formal Lean sidecar may mirror released orchestration laws only:
  - it is not required for slice validity,
  - it may not silently redefine the practical runner contract.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- the orchestration entrypoint, run-manifest grammar, fixture ladder, and stop
  behavior are one bounded seam;
- splitting them would create artificial staging inside the final remaining `V41`
  slice without reducing semantic risk.
