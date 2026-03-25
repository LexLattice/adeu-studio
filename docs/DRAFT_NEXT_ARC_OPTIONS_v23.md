# Draft Next Arc Options v23

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v22.md`, updated after
`vNext+82` closeout and bounded `V40` family completion.

This draft treats `V40-F` as closed on `main` at its bounded baseline and begins
selection of the next family.

The next question is no longer how to complete the ASIR artifact ladder itself.

The next question is how to use the released ASIR ladder practically against a real
repo so that ADEU can:

- make intended architecture explicit;
- make observed implementation explicit; and
- compare the two truthfully rather than blurring them together.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `vNext+82` is the current baseline implementation state.
- The released ASIR family substrate now includes:
  - canonical semantic-root artifacts and schema exports;
  - deterministic conformance and blocked/ready gating;
  - bounded hybrid checkpoint, oracle, and delta artifacts;
  - honest `adeu_core_ir@0.1` lowering through canonical projection bundle/manifest
    lineage;
  - first UX compatibility lowering into canonical `ux_domain_packet@1` only;
  - family-complete evidence and stop-gate continuity for `vNext+77` through
    `vNext+82`.
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md` is now the historical closed decomposition
  for `V40`.

## Gap

The missing layer is no longer semantic-root release, deterministic conformance,
bounded hybrid disposition, lowering, UX compatibility, or family release evidence.

The missing layer is a practical repo-grounded analysis loop that can:

- bind one real repo scope plus maintainer brief into one canonical analysis request;
- capture one exact `source_set` of docs, code, config, and tests rather than relying
  on ad hoc file reads;
- settle one explicit interpretive and deontic frame before observed extraction,
  intended compile, or drift claims begin;
- compile intended architecture over that `source_set` into canonical
  `adeu_architecture_semantic_ir@1`;
- compile observed implementation facts from the same repo scope into a separate
  comparable artifact;
- emit one deterministic alignment report that surfaces code-vs-intent drift without
  silently merging the two lanes.

Today the repo still lacks a released way to:

- run ASIR habitually against one of our real codebases rather than only against
  frozen synthetic fixtures;
- externalize the chosen interpretation / entitlement / escalation posture before
  compiling observed or intended architecture claims;
- preserve the distinction between:
  - intended architecture,
  - observed implementation, and
  - the deterministic comparison between them;
- surface practical mismatch classes such as:
  - declared but unimplemented behavior,
  - implemented but undeclared behavior,
  - authority-boundary drift,
  - workflow drift,
  - observability / evidence gaps;
- orchestrate the resulting loop repeatably from one CLI-first runner.

In this family, "one real repo scope" should mean:

- one repo-root-relative subtree as the default scope anchor;
- optional explicit file additions outside that subtree when they are named
  deterministically;
- explicit exclusion rules;
- and an allowed artifact-kind set for docs, code, config, and tests.

## Naming Convention (New Family)

- `V41-*` identifiers are reserved for the practical repo-grounded architecture
  analysis family in this planning cycle.
- `B41-*` identifiers are reserved for explicit multi-path bundles if later needed.
- `V40-*` remains historical/closed and is not reused.

## Recommended Family

- Family name: `V41`
- Family theme: practical repo-grounded architecture analysis, settlement, and
  alignment
- Closed prior family:
  - `V40-A`
  - `V40-B`
  - `V40-C`
  - `V40-D`
  - `V40-E`
  - `V40-F`
- Recommended decomposition reference:
  - `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V41-A`
- Recommended next concrete arc:
  - `vNext+83`
- Default path selection:
  - select `V41-A` as the next default candidate

## Closed Earlier Family (`V40`)

Solved:

- the complete ASIR artifact ladder from semantic-root through family evidence;
- deterministic separation of semantic root, conformance, hybrid checkpoint state,
  projection lineage, UX compatibility, and release evidence;
- bounded advisory-only oracle law and fail-closed escalation;
- bounded projection and UX honesty over released lineage;
- family-complete release evidence and stop-gate continuity.

What `V40` did not solve:

- running the pipeline habitually against one real repo;
- keeping intended architecture and observed implementation as separate comparable
  typed lanes;
- emitting one deterministic alignment report over the two lanes;
- packaging the loop into one repeatable CLI-first practical runner.

## Recommended Next Path (`V41-A`)

Implement the practical analysis-request and source-set capture baseline.

`V41-A` should introduce:

- one canonical `adeu_architecture_analysis_request@1` artifact;
- exact maintainer-brief refs and accepted-doc refs bound into the request rather than
  only free prose content;
- deterministic repo-root-relative scope selection and inclusion/exclusion policy;
- one exact `source_set` over accepted docs, code, config, and tests;
- explicit snapshot mode over either:
  - committed tree content; or
  - an explicitly materialized snapshot captured as part of the request,
  rather than whatever files happen to be present in an ambient live working tree;
- immutable snapshot identity for the chosen mode;
- per-source-item hash binding plus one aggregate `source_set` hash for replay-stable
  canonicalization;
- brief/doc refs that resolve either into the frozen `source_set` or into separately
  materialized and hashed captured artifacts;
- explicit request-bound `authority_boundary_policy` or exact policy ref;
- room for a later settlement artifact ref without pretending settlement is already
  complete;
- one committed reference fixture over one bounded internal repo scope;
- no observed extraction, intended compile, or alignment report yet.

## Why This Path

- It is the narrowest lawful next consumer of the released `V40` ladder.
- It turns the practical loop into something deterministic immediately instead of
  letting repo analysis start as ad hoc file selection.
- It preserves the central architectural distinction:
  intended architecture and observed implementation cannot be compared honestly unless
  they are derived from the same explicit source set.
- It keeps the next slice comparable to earlier ADEU seams instead of mixing request
  capture, repo observation, alignment, and workflow UI in one first lock.

## First-Slice Boundary (`V41-A`)

`V41-A` should stay bounded to:

- analysis-request schema/model/export baseline only;
- deterministic `source_set` capture only;
- repo-scope selection, inclusion/exclusion policy, and hash binding only;
- request-bound authority policy and settlement hooks only;
- artifact inputs for a later runner only, not the runner itself;
- committed request/reference fixtures only;
- validator tests only.

It should not attempt:

- semantic settlement;
- drift claims;
- impossibility claims;
- observed implementation extraction;
- intended ASIR compile over a real repo;
- alignment or drift diagnostics;
- CLI orchestration of the full loop;
- API or web inspection surfaces;
- automatic repo mutation or prompt-to-code generation.

## Follow-On Paths Inside `V41`

The recommended family ladder after `V41-A` is:

1. `V41-A`
   - analysis request and deterministic `source_set` capture
2. `V41-B`
   - interpretation settlement, deontic typing, and entitlement / escalation baseline
3. `V41-C`
   - observed implementation observation frame
4. `V41-D`
   - intended repo-grounded ASIR compile
5. `V41-E`
   - deterministic alignment and drift diagnostics
6. `V41-F`
   - practical runner / habitual orchestration

## Planning Boundary

- no reopening of `V40-A` through `V40-F` semantics is authorized by this planning
  draft;
- no silent collapse of intended and observed architecture into one artifact is
  authorized by this planning draft;
- no direct prompt-to-code or automatic repo mutation is authorized by this planning
  draft;
- no API or web workbench release is authorized by this planning draft;
- no formal Lean proof surface becomes authoritative over practical repo analysis by
  this planning draft;
- the practical loop should stay CLI-first and one-repo-scoped before any broader
  orchestration widening;
- no stop-gate schema-family fork or implicit metric-key expansion is authorized.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v22.md",
  "baseline_arc": "vNext+82",
  "closed_prior_family": "V40",
  "closed_prior_paths": [
    "V40-A",
    "V40-B",
    "V40-C",
    "V40-D",
    "V40-E",
    "V40-F"
  ],
  "next_family": "V41",
  "default_next_arc_candidate": "V41-A",
  "default_next_concrete_arc_candidate": "vNext+83",
  "family_decomposition_doc": "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md",
  "analysis_request_artifact": "adeu_architecture_analysis_request@1",
  "analysis_settlement_artifact": "adeu_architecture_analysis_settlement_frame@1",
  "observed_lane_artifact": "adeu_architecture_observation_frame@1",
  "intended_lane_artifact": "adeu_architecture_semantic_ir@1",
  "alignment_artifact": "adeu_architecture_alignment_report@1",
  "intended_observed_lane_separation_required": true,
  "alignment_requires_distinct_intended_and_observed_artifacts": true,
  "precompile_settlement_required": true,
  "source_set_snapshot_mode": "committed_tree_or_explicit_materialized_snapshot_only",
  "source_set_hashing_profile": "per_item_hashes_plus_aggregate_hash",
  "dual_compile_required": true,
  "formal_sidecar_authoritative": false,
  "cli_first_practical_runner": true,
  "v41a_runner_deferred": true
}
```
