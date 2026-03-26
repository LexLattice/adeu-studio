# Draft Next Arc Options v23

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v22.md`, updated after
`vNext+85` closeout and released `V41-A` + `V41-B` + `V41-C`
practical-analysis baselines on `main`.

This draft keeps `V41` active and selects the immediate next seam inside that family.

The next question is no longer how to bind the repo world deterministically.

The next question is how to compile intended architecture over that already-frozen
repo world, already-released settlement posture, and already-released observed frame
without collapsing intended and observed lanes or smuggling in alignment verdicts.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `V41-A`, `V41-B`, and `V41-C` are now closed on `main`.
- `vNext+85` is the current baseline implementation state.
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
  - exact upstream blocked-settlement carry-through in the observed lane.
- The released practical-analysis loop still does not yet include:
  - intended repo-grounded ASIR compile;
  - deterministic alignment / drift reporting;
  - habitual runner orchestration.

## Gap

The missing layer is no longer request/world binding itself, it is no longer the
settlement / entitlement seam, and it is no longer the observed implementation lane
either.

The missing layer is the intended repo-grounded compile lane that says:

- what intended architecture can be compiled over the same frozen repo world that the
  observed lane consumed;
- how that intended compile stays bound to the released request, settlement, and
  observation boundary instead of drifting into a fresh brief universe;
- how intended semantics remain explicit without silently inheriting unresolved
  observed gaps as if they were settled truth;
- and how the intended lane stays distinct from later alignment / drift judgment.

Today the repo still lacks a released way to:

- compile one canonical repo-grounded intended
  `adeu_architecture_semantic_ir@1` artifact over the released request, settlement,
  and observation boundary;
- keep intended compile sourced from the same frozen `source_set` rather than a fresh
  drifting maintainer-brief universe;
- force intended compile to respect blocked settlement posture and explicit unresolved
  observation carry-through rather than laundering them away;
- preserve intended semantics as a distinct typed lane rather than silently blending
  them with observed implementation facts;
- and hand later alignment lanes a released intended surface rather than expecting
  them to compare observation against prose.

## Naming Convention (Active Family)

- `V41-*` identifiers remain reserved for the practical repo-grounded architecture
  analysis family.
- `V40-*` remains historical / closed.

## Recommended Family

- Family name: `V41`
- Family theme: practical repo-grounded architecture analysis, settlement, and
  alignment
- Closed current-family paths:
  - `V41-A`
  - `V41-B`
  - `V41-C`
- Recommended decomposition reference:
  - `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V41-D`
- Recommended next concrete arc:
  - `vNext+86`
- Default path selection:
  - select `V41-D` as the next default candidate

## Closed Current Paths (`V41-A`, `V41-B`, `V41-C`)

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
  and fail-closed compile entitlement.
- one canonical observation-frame artifact;
- facts-only observed implementation extraction over the released request +
  settlement boundary;
- explicit direct-vs-derived observation marking;
- explicit unresolved observation preservation and upstream blocked-settlement
  carry-through.

What `V41-A` + `V41-B` + `V41-C` did not solve:

- intended repo-grounded ASIR compile;
- deterministic alignment and drift diagnostics;
- habitual runner orchestration.

## Recommended Next Path (`V41-D`)

Implement the repo-grounded intended-architecture compile baseline.

`V41-D` should introduce:

- one canonical repo-grounded `adeu_architecture_semantic_ir@1` artifact;
- exact consumption of the released `V41-A` request boundary, released `V41-B`
  settlement frame, and released `V41-C` observation frame over the same:
  - `analysis_request_id`
  - `analysis_request_ref`
  - `settlement_frame_id`
  - `settlement_frame_ref`
  - `observation_frame_id`
  - `observation_frame_ref`
  - `source_set_hash`
  - `authority_boundary_policy`;
- the released request boundary plus released settlement frame as the normative
  driver of intended compile, with the observation frame limited to constraining
  overreach, forcing ambiguity/advisory posture, or triggering refusal rather than
  becoming the hidden source of intended truth;
- deterministic intended compile from the same frozen request world rather than a
  fresh ambient brief universe;
- exact carry-through of settlement posture and unresolved observation posture into
  compile legality;
- explicit intended semantics over at least:
  - ontology
  - epistemics
  - deontics
  - utility
  with the same bounded honesty law already frozen in `V40-A`;
- no observed implementation facts silently promoted into intended truth without an
  explicit compile claim posture;
- no local recomputation of `compile_entitlement`; the intended lane consumes the
  released settlement posture as-is;
- no alignment severity, remediation, or runner behavior inside the intended lane;
- one committed intended-compile reference fixture over one bounded internal repo
  slice, including at least one visible carry-through case where an unresolved or
  derived observation remains ambiguity, advisory posture, or refusal to settle.

## Why This Path

- It is the next lawful seam after world binding plus settlement / entitlement plus
  observed implementation extraction.
- It keeps intended and observed lanes separate before any later alignment slice tries
  to compare them.
- It forces intended compile to earn its semantics over the same frozen repo world
  already consumed by the observation lane.
- It prevents later alignment from comparing observation against prose or ad hoc
  maintainer restatement.
- It gives later drift lanes a deterministic intended surface to consume habitually.

## First-Slice Boundary (`V41-D`)

`V41-D` should stay bounded to:

- intended semantic-root compile only;
- released request + settlement + observation consumption only;
- exact carry-through of blocked settlement and unresolved observation posture only;
- no practical checkpoint/oracle reuse in the first concrete `vNext+86` arc even if
  the broader `V41-D` path may later admit bounded reuse when ambiguity remains;
- committed intended-compile reference fixtures only;
- validator tests only.

It should not attempt:

- drift or alignment diagnostics;
- remediation plans or repo-mutation instructions;
- CLI orchestration of the full practical loop;
- API or web inspection surfaces;
- automatic code changes or prompt-to-code generation.

## Follow-On Paths Inside `V41`

The recommended family ladder after `V41-C` is:

1. `V41-D`
   - intended repo-grounded ASIR compile
2. `V41-E`
   - deterministic alignment and drift diagnostics
3. `V41-F`
   - practical runner / habitual orchestration

## Planning Boundary

- no reopening of the released `V41-A` request / `source_set` contract is authorized
  by this planning draft;
- no observed extraction, intended compile, or alignment report is authorized by this
  planning draft;
- no silent promotion of permissions into obligations or bounded search absence into
  proved impossibility is authorized by this planning draft;
- no API or web workbench release is authorized by this planning draft;
- no automatic repo mutation or direct prompt-to-code generation is authorized by this
  planning draft;
- no formal Lean sidecar becomes authoritative over practical settlement validity by
  this planning draft;
- no stop-gate schema-family fork or implicit metric-key expansion is authorized.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v22.md",
  "baseline_arc": "vNext+85",
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
    "V41-C"
  ],
  "default_next_arc_candidate": "V41-D",
  "default_next_concrete_arc_candidate": "vNext+86",
  "family_decomposition_doc": "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md",
  "analysis_request_artifact": "adeu_architecture_analysis_request@1",
  "analysis_settlement_artifact": "adeu_architecture_analysis_settlement_frame@1",
  "analysis_settlement_package": "packages/adeu_architecture_ir",
  "observed_lane_artifact": "adeu_architecture_observation_frame@1",
  "observed_lane_package": "packages/adeu_architecture_compiler",
  "intended_lane_artifact": "adeu_architecture_semantic_ir@1",
  "alignment_artifact": "adeu_architecture_alignment_report@1",
  "intended_observed_lane_separation_required": true,
  "alignment_requires_distinct_intended_and_observed_artifacts": true,
  "precompile_settlement_required": true,
  "settlement_entitlement_gate_required": true,
  "settlement_entry_grounding_required": true,
  "settlement_blocking_lineage_required": true,
  "settlement_notes_authoritative": false,
  "formal_sidecar_authoritative": false,
  "cli_first_practical_runner": true,
  "v41b_runner_deferred": true,
  "v41c_runner_deferred": true,
  "v41d_runner_deferred": true
}
```
