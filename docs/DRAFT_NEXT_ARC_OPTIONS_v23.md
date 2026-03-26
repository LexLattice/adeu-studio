# Draft Next Arc Options v23

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v22.md`, updated after
`vNext+87` closeout and released `V41-A` + `V41-B` + `V41-C` + `V41-D` + `V41-E`
practical-analysis baselines on `main`.

This draft keeps `V41` active and selects the immediate next seam inside that family.

The next question is no longer how to bind the repo world deterministically.

The next question is no longer how to compare intended and observed lanes
deterministically either.

The next question is how to habitualize the now-released request, settlement,
observation, intended, and alignment stack as one practical runner without silently
widening into repo mutation, remediation authority, or a merged-truth surface.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `V41-A`, `V41-B`, `V41-C`, `V41-D`, and `V41-E` are now closed on `main`.
- `vNext+87` is the current baseline implementation state.
- The released practical-analysis substrate now includes:
  - canonical `adeu_architecture_analysis_request@1`;
  - deterministic repo-root-relative scope selection;
  - `committed_tree` / `materialized_snapshot` request discipline;
  - per-item plus aggregate `source_set` hashing;
  - exact brief/doc reference closure;
  - explicit request-bound authority-boundary policy pinning;
  - canonical `adeu_architecture_analysis_settlement_frame@1`;
  - explicit interpretation register plus chosen interpretation;
  - explicit deontic typing, affordance decisions, claim posture, escalation policy,
    and fail-closed `compile_entitlement` over the released request boundary;
  - canonical `adeu_architecture_observation_frame@1`;
  - exact request + settlement consumption in the observed lane;
  - facts-only observed implementation extraction;
  - explicit direct-vs-derived observation marking;
  - explicit unresolved observations with bounded reason typing;
  - exact upstream blocked-settlement carry-through in the observed lane;
  - canonical repo-grounded intended compile over the released request, settlement,
    and observation boundary;
  - deterministic materialization of the released `V40-A` root-family artifacts over
    one bounded repo slice;
  - exact consumption of settlement `compile_entitlement = entitled` as-is rather
    than local recomputation;
  - explicit carry-through of unresolved observed facts into intended ambiguity or
    advisory posture;
  - continued intended vs observed lane separation with observation constrained to
    companion evidence only;
  - canonical `adeu_architecture_alignment_report@1`;
  - exact request + settlement + observation + intended consumption in the alignment
    lane;
  - stable finding ids over canonical typed support tuples;
  - deterministic dedup/order and explicit severity/blocking posture;
  - unresolved-unknown carry-through without merged-truth reconciliation.
- The released practical-analysis loop still does not yet include:
  - habitual runner orchestration.

## Gap

The missing layer is no longer request/world binding, settlement / entitlement,
observed implementation extraction, intended compile, or deterministic alignment.

The missing layer is the practical runner that says:

- how one released request / settlement / observation / intended / alignment stack is
  orchestrated habitually from a bounded repo scope without reopening any of those
  seams ad hoc;
- how a CLI-first practical loop can materialize the already-released artifacts in
  lawful sequence while preserving replay identity and evidence capture;
- how one canonical run-manifest artifact can record exact sequencing, emitted refs,
  and bounded stop posture for that loop without silently becoming remediation or
  repo-mutation authority;
- how the runner remains orchestration-only rather than silently widening into repo
  mutation, remediation authority, or merged-truth reconciliation;
- and how practical execution can remain fail-closed when released settlement posture
  stops intended/alignment emission while still recording terminal alignment posture
  honestly when the full comparison run completes.

Today the repo still lacks a released way to:

- run one canonical CLI-first practical-analysis loop over a bounded repo slice;
- materialize the already-released `V41-A` through `V41-E` artifact ladder from one
  runner entrypoint;
- materialize one canonical `adeu_architecture_analysis_run_manifest@1` that binds
  exact request / settlement / observation / intended / alignment lineage for that
  loop;
- preserve replay-stable orchestration lineage, evidence capture, and stop/fail
  boundaries for that loop;
- and habitualize practical analysis without improvising the sequence manually across
  separate commands and fixtures.

## Naming Convention (Active Family)

- `V41-*` identifiers remain reserved for the practical repo-grounded architecture
  analysis family.
- `V40-*` remains historical / closed.

## Recommended Family

- Family name: `V41`
- Family theme: practical repo-grounded architecture analysis, settlement, intended
  compile, alignment, and runner orchestration
- Closed current-family paths:
  - `V41-A`
  - `V41-B`
  - `V41-C`
  - `V41-D`
  - `V41-E`
- Recommended decomposition reference:
  - `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V41-F`
- Recommended next concrete arc:
  - `vNext+88`
- Default path selection:
  - select `V41-F` as the next default candidate

## Closed Current Paths (`V41-A`, `V41-B`, `V41-C`, `V41-D`, `V41-E`)

Solved:

- one canonical analysis-request artifact;
- one deterministic repo scope and `source_set`;
- one exact snapshot identity posture;
- exact brief/doc reference closure;
- explicit settlement deferral and no compile-claim authority from request capture
  alone;
- one canonical settlement-frame artifact;
- explicit chosen interpretation and grounded registers;
- explicit deontic typing, affordance decisions, claim posture, escalation policy,
  and fail-closed compile entitlement;
- one canonical observation-frame artifact;
- facts-only observed implementation extraction over the released request +
  settlement boundary;
- explicit direct-vs-derived observation marking;
- explicit unresolved observation preservation and upstream blocked-settlement
  carry-through;
- one canonical repo-grounded intended compile lane over the same released request,
  settlement, and observation boundary;
- reuse of unchanged `V40-A` root-family artifact families rather than a fresh
  practical schema family;
- entitled-only emission with explicit refusal on blocked settlement posture;
- explicit carry-through of unresolved or derived observed facts into intended
  ambiguity/advisory posture;
- one canonical deterministic alignment-report artifact;
- exact comparison over the released request, settlement, observation, and intended
  boundaries;
- stable finding ids over canonical typed support tuples;
- explicit severity and blocking posture over starter mismatch classes;
- explicit unresolved-unknown carry-through into the alignment surface.

What `V41-A` + `V41-B` + `V41-C` + `V41-D` + `V41-E` did not solve:

- habitual runner orchestration.

## Recommended Next Path (`V41-F`)

Implement the practical runner / habitual orchestration baseline.

`V41-F` should introduce:

- one canonical `adeu_architecture_analysis_run_manifest@1` artifact;
- one canonical CLI-first orchestration entrypoint over the released `V41-A` through
  `V41-E` stack;
- exact sequencing for request capture, settlement consumption, observation
  extraction, intended compile, and alignment generation over one bounded repo slice;
- replay-stable run identity, evidence capture, and artifact lineage across that
  sequence;
- deterministic `run_id` derivation plus a canonical stage ledger over request,
  settlement, observation, intended, alignment, and manifest stages;
- fail-closed stop behavior when released settlement posture blocks intended compile
  or alignment emission;
- authoritative manifest emission even for settlement-blocked runs, so the stop
  witness remains typed and replayable;
- explicit distinction between runner-level `run_outcome = blocked` and a completed
  run whose consumed alignment report may still carry `alignment_posture = blocked`;
- explicit runner evidence and committed reference harness output proving the full
  practical loop can be replayed habitually without silently mutating the repo or
  reconciling intended and observed into one surface.

## Why This Path

- It is the only remaining default seam in `V41` after request, settlement,
  observation, intended, and alignment are all now released.
- It lets the repo habitualize the already-frozen stack without reopening the
  previous artifact families or forcing maintainers to orchestrate the loop manually.
- It gives practical analysis one stable entrypoint to consume the already-released
  comparison surface instead of improvising sequencing ad hoc.

## First-Slice Boundary (`V41-F`)

`V41-F` should stay bounded to:

- deterministic run-manifest materialization only;
- deterministic runner/orchestration materialization only;
- released request + settlement + observation + intended + alignment consumption only;
- CLI-first habitual execution over one bounded repo slice only;
- deterministic output-root placement and runtime-evidence placement only;
- explicit evidence capture and replay identity only;
- explicit blocked-stop recording without hidden shadow artifacts only;
- explicit terminal alignment posture of `none` for blocked runs only;
- no remediation generation or repo-mutation planning;
- no merged-truth reconciliation or hidden semantic settlement;
- committed orchestration reference fixtures only;
- validator tests only.

It should not attempt:

- repo mutation or remediation plans;
- automatic reconciliation or auto-acceptance of drift;
- API or web inspection surfaces;
- automatic code changes or prompt-to-code generation.

## Remaining Path Inside `V41`

The recommended family ladder after closed `V41-E` has one default slice left:

1. `V41-F`
   - practical runner / habitual orchestration

## Planning Boundary

- no reopening of the released `V41-A` request / `source_set` contract is authorized
  by this planning draft;
- no observation extraction, intended compile, or alignment report is authorized by
  this planning draft;
- no silent promotion of permissions into obligations or bounded search absence into
  proved impossibility is authorized by this planning draft;
- no API or web workbench release is authorized by this planning draft;
- no automatic repo mutation or direct prompt-to-code generation is authorized by this
  planning draft;
- no formal Lean sidecar becomes authoritative over practical alignment validity by
  this planning draft;
- no stop-gate schema-family fork or implicit metric-key expansion is authorized.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v22.md",
  "baseline_arc": "vNext+87",
  "closed_prior_family": "V40",
  "closed_prior_paths": [
    "V40-A",
    "V40-B",
    "V40-C",
    "V40-D",
    "V40-E",
    "V40-F"
  ],
  "active_family": "V41",
  "closed_current_family_paths": [
    "V41-A",
    "V41-B",
    "V41-C",
    "V41-D",
    "V41-E"
  ],
  "default_next_arc_candidate": "V41-F",
  "default_next_concrete_arc_candidate": "vNext+88",
  "family_decomposition_doc": "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md",
  "analysis_request_artifact": "adeu_architecture_analysis_request@1",
  "analysis_settlement_artifact": "adeu_architecture_analysis_settlement_frame@1",
  "analysis_settlement_package": "packages/adeu_architecture_ir",
  "observed_lane_artifact": "adeu_architecture_observation_frame@1",
  "observed_lane_package": "packages/adeu_architecture_compiler",
  "intended_lane_artifact": "adeu_architecture_semantic_ir@1",
  "alignment_artifact": "adeu_architecture_alignment_report@1",
  "alignment_package": "packages/adeu_architecture_compiler",
  "alignment_authoritative_intended_surface": "adeu_architecture_semantic_ir@1",
  "practical_runner_artifact": "adeu_architecture_analysis_run_manifest@1",
  "practical_runner_package": "packages/adeu_architecture_compiler",
  "intended_observed_lane_separation_required": true,
  "alignment_requires_distinct_intended_and_observed_artifacts": true,
  "precompile_settlement_required": true,
  "settlement_entitlement_gate_required": true,
  "settlement_entry_grounding_required": true,
  "settlement_blocking_lineage_required": true,
  "alignment_blocked_distinct_from_settlement_blocked": true,
  "runner_blocked_distinct_from_alignment_blocked": true,
  "run_manifest_emitted_on_blocked_run": true,
  "run_id_deterministic": true,
  "stage_ledger_required": true,
  "settlement_notes_authoritative": false,
  "formal_sidecar_authoritative": false,
  "cli_first_practical_runner": true,
  "remaining_default_paths_in_family": [
    "V41-F"
  ],
  "v41f_repo_mutation_deferred": true,
  "v41f_remediation_authority_deferred": true
}
```
