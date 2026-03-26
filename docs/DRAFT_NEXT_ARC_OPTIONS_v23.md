# Draft Next Arc Options v23

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v22.md`, updated after
`vNext+86` closeout and released `V41-A` + `V41-B` + `V41-C` + `V41-D`
practical-analysis baselines on `main`.

This draft keeps `V41` active and selects the immediate next seam inside that family.

The next question is no longer how to bind the repo world deterministically.

The next question is how to compare the now-released intended and observed practical
lanes deterministically without collapsing them into one truth surface, silently
normalizing drift, or widening immediately into runner, remediation, or repo-mutation
behavior.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `V41-A`, `V41-B`, `V41-C`, and `V41-D` are now closed on `main`.
- `vNext+86` is the current baseline implementation state.
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
    companion evidence only.
- The released practical-analysis loop still does not yet include:
  - deterministic alignment / drift reporting;
  - habitual runner orchestration.

## Gap

The missing layer is no longer request/world binding itself, it is no longer the
settlement / entitlement seam, it is no longer the observed implementation lane, and
it is no longer the intended compile seam either.

The missing layer is the deterministic alignment lane that says:

- how intended and observed architecture are compared without collapsing into one
  merged truth surface;
- how request-bound intended authority remains primary while observation constrains,
  blocks, or forces unresolved posture without becoming the hidden source of intent;
- how starter mismatch classes remain explicit, stable, and grounded in the released
  upstream artifacts;
- how unresolved unknowns remain visible as unresolved alignment posture rather than
  being normalized away;
- and how drift becomes inspectable before any habitual runner starts materializing
  the full practical loop by default.

Today the repo still lacks a released way to:

- emit one canonical `adeu_architecture_alignment_report@1` artifact over the
  released request, settlement, observation, and intended boundaries;
- classify starter mismatches deterministically rather than leaving drift as prose or
  reviewer intuition;
- keep severity and blocking posture explicit without silently reconciling intended
  and observed into one cleaned-up artifact;
- preserve unresolved unknowns as first-class alignment findings rather than hiding
  them inside notes or by omission;
- and hand the later practical runner a released comparison surface rather than
  forcing it to improvise comparison logic ad hoc.

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
- Recommended decomposition reference:
  - `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V41-E`
- Recommended next concrete arc:
  - `vNext+87`
- Default path selection:
  - select `V41-E` as the next default candidate

## Closed Current Paths (`V41-A`, `V41-B`, `V41-C`, `V41-D`)

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
  ambiguity/advisory posture.

What `V41-A` + `V41-B` + `V41-C` + `V41-D` did not solve:

- deterministic alignment and drift diagnostics;
- habitual runner orchestration.

## Recommended Next Path (`V41-E`)

Implement the deterministic intended-vs-observed alignment baseline.

`V41-E` should introduce:

- one canonical `adeu_architecture_alignment_report@1` artifact;
- exact consumption of the released `V41-A` request boundary, released `V41-B`
  settlement frame, released `V41-C` observation frame, and released `V41-D`
  intended root-family outputs over the same:
  - `analysis_request_id`
  - `analysis_request_ref`
  - `settlement_frame_id`
  - `settlement_frame_ref`
  - `observation_frame_id`
  - `observation_frame_ref`
  - `architecture_id`
  - `semantic_hash`
  - `source_set_hash`
  - `authority_boundary_policy`;
- released `adeu_architecture_semantic_ir@1` as the authoritative intended
  comparison surface for the first baseline, with any companion intended
  root-family refs allowed only through an explicit declared support contract;
- deterministic starter mismatch classes at least for:
  - `declared_not_observed`
  - `observed_not_declared`
  - `authority_boundary_drift`
  - `workflow_or_state_drift`
  - `evidence_or_observability_gap`
  - `unresolved_unknown`;
- stable deterministic finding ids derived from canonical typed support tuples,
  deterministic finding dedup/order rules, and explicit severity / blocking posture
  over those starter classes;
- exact carry-through of settlement and unresolved-observation context into the
  comparison surface without reopening or redefining the upstream artifacts;
- explicit distinction between report-level `blocked` alignment posture and upstream
  settlement `compile_entitlement = blocked`;
- no silent reconciliation or normalization of intended and observed lanes into one
  merged truth surface;
- one committed alignment reference fixture over one bounded internal repo slice,
  including at least one explicit unresolved or blocking drift case and at least one
  upstream ambiguity or unresolved observation that survives into an explicit
  `unresolved_unknown` finding.

## Why This Path

- It is the next lawful seam after world binding plus settlement / entitlement plus
  observed implementation extraction plus intended compile.
- It keeps intended and observed lanes separate while making their differences
  inspectable before any runner tries to habitualize the loop.
- It prevents later orchestration from comparing observation against prose or against
  an implied intended surface that was never released deterministically.
- It gives later practical-runner lanes one stable comparison artifact to consume
  habitually.

## First-Slice Boundary (`V41-E`)

`V41-E` should stay bounded to:

- deterministic alignment-report materialization only;
- released request + settlement + observation + intended consumption only;
- starter mismatch classes and severity / blocking posture only;
- basis-typed findings grounded only in typed upstream refs, not prose-only notes;
- explicit unresolved-unknown carry-through only;
- no remediation generation or repo-mutation planning;
- no CLI runner rollout in the first concrete `vNext+87` arc;
- committed alignment reference fixtures only;
- validator tests only.

It should not attempt:

- runner orchestration;
- remediation plans or repo-mutation instructions;
- automatic reconciliation or auto-acceptance of drift;
- API or web inspection surfaces;
- automatic code changes or prompt-to-code generation.

## Follow-On Paths Inside `V41`

The recommended family ladder after `V41-D` is:

1. `V41-E`
   - deterministic alignment and drift diagnostics
2. `V41-F`
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
  "baseline_arc": "vNext+86",
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
    "V41-D"
  ],
  "default_next_arc_candidate": "V41-E",
  "default_next_concrete_arc_candidate": "vNext+87",
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
  "intended_observed_lane_separation_required": true,
  "alignment_requires_distinct_intended_and_observed_artifacts": true,
  "precompile_settlement_required": true,
  "settlement_entitlement_gate_required": true,
  "settlement_entry_grounding_required": true,
  "settlement_blocking_lineage_required": true,
  "alignment_blocked_distinct_from_settlement_blocked": true,
  "settlement_notes_authoritative": false,
  "formal_sidecar_authoritative": false,
  "cli_first_practical_runner": true,
  "v41e_runner_deferred": true,
  "v41e_remediation_deferred": true
}
```
