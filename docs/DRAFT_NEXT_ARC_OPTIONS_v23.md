# Draft Next Arc Options v23

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v22.md`, updated after
`vNext+83` closeout and released `V41-A` world-binding baseline on `main`.

This draft keeps `V41` active and selects the immediate next seam inside that family.

The next question is no longer how to bind the repo world deterministically.

The next question is how to externalize interpretation, deontic typing, entitlement,
and escalation posture over that already-frozen world before any observed extraction,
intended compile, or drift claim begins.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `V41-A` is now closed on `main`.
- `vNext+83` is the current baseline implementation state.
- The released practical-analysis substrate now includes:
  - canonical `adeu_architecture_analysis_request@1`;
  - deterministic repo-root-relative scope selection;
  - `committed_tree` / `materialized_snapshot` request discipline;
  - per-item plus aggregate `source_set` hashing;
  - exact brief/doc reference closure;
  - explicit request-bound authority-boundary policy pinning;
  - explicit settlement deferral over the released request boundary.
- The released practical-analysis loop still does not yet include:
  - canonical settlement / entitlement gating;
  - observed implementation extraction;
  - intended repo-grounded ASIR compile;
  - deterministic alignment / drift reporting;
  - habitual runner orchestration.

## Gap

The missing layer is no longer request/world binding itself.

The missing layer is the pre-compile governance seam that says:

- what interpretation of the maintainer brief / accepted docs was chosen;
- what high-impact ambiguity remains unresolved;
- how prompt and brief content was deontically typed;
- which claims are entitled versus conjectural or unentitled;
- when the system must escalate instead of silently continuing;
- and whether downstream compile is currently entitled or blocked.

Today the repo still lacks a released way to:

- externalize the chosen interpretation over a released `analysis_request_id` and
  `source_set_hash` rather than settling a different world implicitly;
- record permitted or fallback affordances that were noticed and intentionally
  declined or deferred;
- distinguish search-bounded negative posture from proved impossibility strongly
  enough that compile does not overclaim certainty;
- expose escalation triggers before observed extraction, intended compile, or drift
  diagnostics begin;
- block downstream compile honestly when unresolved high-impact ambiguity, active
  escalation triggers, or unentitled negative claims remain.

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
- Recommended decomposition reference:
  - `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V41-B`
- Recommended next concrete arc:
  - `vNext+84`
- Default path selection:
  - select `V41-B` as the next default candidate

## Closed Current Path (`V41-A`)

Solved:

- one canonical analysis-request artifact;
- one deterministic repo scope and `source_set`;
- one exact snapshot identity posture;
- exact brief/doc reference closure;
- explicit settlement deferral and no compile-claim authority from request capture
  alone.

What `V41-A` did not solve:

- chosen interpretation over that frozen request boundary;
- prompt / brief deontic typing;
- affordance decisions and entitlement posture;
- escalation trigger policy;
- downstream compile authorization.

## Recommended Next Path (`V41-B`)

Implement the practical analysis-settlement and entitlement-gating baseline.

`V41-B` should introduce:

- one canonical `adeu_architecture_analysis_settlement_frame@1` artifact;
- exact consumption of the released `V41-A` analysis request and its `source_set_hash`;
- one explicit interpretation register plus one chosen interpretation;
- register entries that remain typed all the way down rather than top-level-only,
  including explicit ids, grounded refs, and rationale where appropriate;
- prompt / brief deontic typing over the released request boundary using frozen
  starter classes:
  - `required`
  - `forbidden`
  - `permitted`
  - `optional_hint`
  - `fallback_affordance`
- explicit `affordance_decisions` recording when a permitted or fallback affordance
  was:
  - `used`
  - `deferred`
  - `intentionally_declined`
  with rationale;
- explicit claim-posture classification at least for:
  - `observed`
  - `inferred`
  - `conjectural`
  - `unentitled_negative_claim`
- explicit escalation-trigger policy at least for:
  - `unresolved_high_impact_ambiguity`
  - `silent_semantic_assumption_needed`
  - `impossibility_claim_without_proof`
  - `externalized_search_or_check_required`
- one exact pre-compile entitlement gate, with:
  - `entitled`
  - `blocked`
  only;
- explicit `blocking_lineage` when `compile_entitlement = blocked`;
- request-bound ref resolution for interpretation support refs, deontic targets,
  affordance-decision targets, claim refs, ambiguity refs, and escalation support refs;
- explicit advisory-only notes if any, with no authority to introduce new typed
  meaning by prose;
- one committed settlement reference fixture over the released v83 request boundary;
- no observation frame, intended compile, alignment report, or runner release yet.

## Why This Path

- It is the next lawful seam after deterministic world binding.
- It prevents the repo from compiling observed or intended claims over the right files
  but under the wrong unexternalized interpretation.
- It turns deontic and entitlement posture into inspectable typed state rather than
  buried model behavior.
- It makes the settlement frame harder to game by requiring grounded per-entry
  structure, blocking lineage, and explicit affordance coverage instead of
  semi-structured blobs.
- It keeps practical analysis truthful: request capture alone does not entitle
  compile, and compile may not proceed silently when high-impact ambiguity or
  unentitled negative claims remain.

## First-Slice Boundary (`V41-B`)

`V41-B` should stay bounded to:

- settlement-frame schema/model/export baseline only;
- released-request consumption only;
- interpretation register, deontic typing, claim posture, affordance decisions, and
  escalation-trigger policy only;
- request-bound grounding for every typed entry inside those registers;
- exact pre-compile entitlement gating only;
- committed settlement reference fixtures only;
- validator tests only.

It should not attempt:

- observed implementation extraction;
- intended ASIR compile over a real repo;
- drift or alignment diagnostics;
- remediation plans or repo-mutation instructions;
- CLI orchestration of the full practical loop;
- API or web inspection surfaces;
- automatic code changes or prompt-to-code generation.

## Follow-On Paths Inside `V41`

The recommended family ladder after `V41-B` is:

1. `V41-B`
   - interpretation settlement, deontic typing, and entitlement / escalation baseline
2. `V41-C`
   - observed implementation observation frame
3. `V41-D`
   - intended repo-grounded ASIR compile
4. `V41-E`
   - deterministic alignment and drift diagnostics
5. `V41-F`
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
  "baseline_arc": "vNext+83",
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
    "V41-A"
  ],
  "default_next_arc_candidate": "V41-B",
  "default_next_concrete_arc_candidate": "vNext+84",
  "family_decomposition_doc": "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md",
  "analysis_request_artifact": "adeu_architecture_analysis_request@1",
  "analysis_settlement_artifact": "adeu_architecture_analysis_settlement_frame@1",
  "analysis_settlement_package": "packages/adeu_architecture_ir",
  "observed_lane_artifact": "adeu_architecture_observation_frame@1",
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
  "v41b_runner_deferred": true
}
```
