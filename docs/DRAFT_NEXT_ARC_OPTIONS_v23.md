# Draft Next Arc Options v23

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v22.md`, updated after
`vNext+84` closeout and released `V41-A` + `V41-B` practical-analysis baselines on
`main`.

This draft keeps `V41` active and selects the immediate next seam inside that family.

The next question is no longer how to bind the repo world deterministically.

The next question is how to extract observed implementation facts over that already-
frozen world and already-released settlement posture without smuggling in intended
semantics, evaluation, or remediation.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `V41-A` and `V41-B` are now closed on `main`.
- `vNext+84` is the current baseline implementation state.
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
    and fail-closed `compile_entitlement` over the released request boundary.
- The released practical-analysis loop still does not yet include:
  - observed implementation extraction;
  - intended repo-grounded ASIR compile;
  - deterministic alignment / drift reporting;
  - habitual runner orchestration.

## Gap

The missing layer is no longer request/world binding itself, and it is no longer the
settlement / entitlement seam either.

The missing layer is the observed implementation lane that says:

- what concrete implementation facts can be extracted deterministically from the
  released `source_set`;
- which services, boundaries, workflows, authority sources, evidence hooks, and
  observability surfaces are actually visible in code or configuration;
- which observations remain unresolved instead of being silently invented;
- and how those observations stay provenance-linked to the released repo world and
  settlement posture without collapsing into intended architecture or drift judgment.

Today the repo still lacks a released way to:

- extract bounded implementation facts into a canonical
  `adeu_architecture_observation_frame@1` artifact;
- preserve exact provenance back to released `source_set` items instead of ambient
  repo reads;
- keep unresolved observations explicit rather than inventing missing structure;
- prevent observed extraction from smuggling in maintainer-intent semantics or
  downstream alignment judgment;
- and hand later intended-compile and alignment lanes an inspectable observed surface
  rather than a prose summary.

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
- Recommended decomposition reference:
  - `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V41-C`
- Recommended next concrete arc:
  - `vNext+85`
- Default path selection:
  - select `V41-C` as the next default candidate

## Closed Current Paths (`V41-A`, `V41-B`)

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

What `V41-A` + `V41-B` did not solve:

- observed implementation extraction over the frozen request/settlement boundary;
- implementation-fact provenance grouped into a canonical observed lane artifact;
- explicit unresolved observation markers in a released observation frame;
- intended repo-grounded ASIR compile;
- deterministic alignment and drift diagnostics;
- habitual runner orchestration.

## Recommended Next Path (`V41-C`)

Implement the observed implementation observation baseline.

`V41-C` should introduce:

- one canonical `adeu_architecture_observation_frame@1` artifact;
- exact consumption of the released `V41-A` request boundary and released `V41-B`
  settlement frame over the same:
  - `analysis_request_id`
  - `analysis_request_ref`
  - `settlement_frame_id`
  - `settlement_frame_ref`
  - `source_set_hash`
  - `authority_boundary_policy`;
- deterministic extraction of bounded implementation facts only from released
  `source_set` items or exact validated derivatives thereof;
- observation may consume either `compile_entitlement = entitled` or
  `compile_entitlement = blocked` from the released settlement frame, but may not
  upgrade, reinterpret, or erase that settlement posture;
- explicit observed surfaces for at least:
  - implementation units / components
  - boundaries and boundary crossings
  - workflows / transitions
  - authority sources
  - evidence hooks
  - observability hooks
  - unresolved observations
- per-entry provenance refs and source hashes back to concrete files in the released
  request boundary;
- per-entry machine-checkable observation anchors including:
  - `fact_kind`
  - `observation_mode = direct | derived`
  on resolved observed entries;
- explicit carry-through of:
  - `upstream_compile_entitlement`
  - `upstream_blocking_refs`
  from the released settlement frame;
- explicit unknown / unresolved observation markers rather than silent invention;
- bounded unresolved-observation reason kinds rather than prose-only unknowns;
- no intended semantics, deontic settlement, evaluation, remediation, or drift
  judgment inside the observed lane;
- one committed observed-frame reference fixture over one bounded internal repo slice.

## Why This Path

- It is the next lawful seam after world binding plus settlement / entitlement.
- It keeps intended and observed lanes separate before any later alignment slice tries
  to compare them.
- It makes implementation observations inspectable as typed, provenance-linked state
  rather than prose summaries or hidden repo reads.
- It distinguishes direct file-grounded facts from bounded derived structural
  extraction so later alignment can see what kind of observation it is consuming.
- It keeps the observed lane honest: implementation facts may be extracted, but they
  may not silently become intended architecture truth or alignment verdicts.
- It gives later intended-compile and drift lanes a deterministic observed surface to
  consume habitually.

## First-Slice Boundary (`V41-C`)

`V41-C` should stay bounded to:

- observation-frame schema/model/export baseline only;
- released request + settlement consumption only;
- bounded implementation-fact extraction only;
- direct-vs-derived observation marking only;
- upstream entitlement/blocking carry-through only;
- request/source-set provenance for every observed entry;
- explicit unresolved observation markers only;
- committed observed-frame reference fixtures only;
- validator tests only.

It should not attempt:

- intended ASIR compile over a real repo;
- drift or alignment diagnostics;
- remediation plans or repo-mutation instructions;
- CLI orchestration of the full practical loop;
- API or web inspection surfaces;
- automatic code changes or prompt-to-code generation.

## Follow-On Paths Inside `V41`

The recommended family ladder after `V41-B` is:

1. `V41-C`
   - observed implementation observation frame
2. `V41-D`
   - intended repo-grounded ASIR compile
3. `V41-E`
   - deterministic alignment and drift diagnostics
4. `V41-F`
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
  "baseline_arc": "vNext+84",
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
    "V41-B"
  ],
  "default_next_arc_candidate": "V41-C",
  "default_next_concrete_arc_candidate": "vNext+85",
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
  "v41c_runner_deferred": true
}
```
