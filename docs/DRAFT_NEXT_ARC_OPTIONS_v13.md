# Draft Next Arc Options v13

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v12.md`, updated after
`vNext+72` closeout.

This draft now treats `V39` as a broader module-conformance family rather than a
single-slice one-off.

`V39-A` is now closed on `main` as the retrospective external-contribution alignment
baseline. The next question is how to generalize that conformance terrain without
collapsing into a generic style engine or an unbounded all-module marketplace.

## Baseline

- `V38-A` established a typed way to compile high-level ADEU/UDEO intent into a
  bounded brokered execution plan.
- `V39-A` established a typed retrospective-alignment lane for imported single-PR
  contributions through:
  - canonical `external_contribution_alignment_packet@1`;
  - canonical `module_conformance_report@1`;
  - canonical `v39a_external_contribution_alignment_evidence@1`;
  - one localized reference bundle for the poetry utility contribution.
- The repo now already has:
  - strong internal arc discipline through lock, assessment, and decision docs;
  - deterministic local gates through `make check`;
  - deterministic closeout and scaffold linting;
  - a bounded imported-work conformance lane;
  - a real reference example where code alignment and process alignment had to remain
    separate.

## Gap

The missing layer is no longer external-contribution intake alone.

The missing layer is a bounded, typed module for structural drift patterns that can
apply across:

- forward coding;
- post-code optimization;
- retrospective contribution assessment;
- later module-conformance checks.

Today the repo still lacks a canonical way to:

- encode structurally meaningful code smells without falling back to the vague phrase
  "AI accent";
- separate:
  - pseudo-safety inflation,
  - abstraction without pressure,
  - error-opacity drift,
  - naming-semantic drift,
  - communication-without-load drift;
- state which of those can be:
  - auto-fixed safely,
  - deterministically warned on,
  - kept as heuristic human-review findings only;
- project those rules differently for:
  - the forward coding agent,
  - the post-code optimizer agent.

## Recommended Family

- Family name: `V39`
- Family theme: module conformance and structural drift governance
- Closed first path: `V39-A`
- Recommended next path: `V39-B`
- Default path selection:
  select `V39-B` as the next default candidate

## Closed First Path (`V39-A`)

`V39-A` is the completed retrospective external-contribution baseline.

It solved:

- imported single-PR lane classification;
- code-alignment vs meta-sequence separation;
- truthful three-layer scope recording;
- pinned policy provenance for deterministic replay;
- default-negative precedent semantics.

It intentionally did not solve:

- general structural-drift taxonomy;
- reusable pattern registry;
- forward-agent preventive rules;
- post-optimizer corrective rules.

## Recommended Next Path (`V39-B`)

Implement a bounded canonical taxonomy for structural code drift patterns that are
currently described informally as an "AI accent."

The path should normalize that intake language into repo-native ADEU structure.

`V39-B` should introduce:

- a canonical `synthetic_structure_rule_registry@1`;
- a neutral typed drift taxonomy rather than an authorship detector;
- explicit ODEU framing for each rule:
  - `O`: drift family,
  - `E`: evidence mode,
  - `D`: policy grade,
  - `U`: expected utility gain;
- automation-tier labeling for each rule:
  - safe autofix,
  - deterministic warning,
  - heuristic review,
  - human-only.

## Why This Path

- It generalizes a real repo pain point exposed by `V39-A` without leaving the family
  boundary.
- It keeps the conformance lane about structure and utility rather than about vague
  "AI detection."
- It creates reusable substrate for both future imported-work alignment and future
  agent-policy refinement.
- It turns style folklore into typed, reviewable, scope-bounded objects.

## Follow-On Paths Inside `V39`

### `V39-C`

Observation and reporting lane:

- canonical `synthetic_structure_observation_packet@1`;
- canonical `synthetic_structure_conformance_report@1`;
- bounded deterministic detectors for the high-confidence subset;
- one or more seed fixtures, likely beginning from the poetry utility reference and
  one repo-native reference diff.

### `V39-D`

Agent-policy projection lane:

- canonical `synthetic_structure_fix_plan@1`;
- forward coding agent policy projection;
- post-code optimizer policy projection;
- bounded safe-autofix support only for the highest-confidence subset.

## First-Slice Boundary (`V39-B`)

`V39-B` should stay bounded to:

- taxonomy and registry only;
- typed drift families rather than broad style doctrine;
- explicit automation-tier classification;
- explicit false-positive risk and counterexample handling;
- forward-agent and post-optimizer policy hooks at the registry level only.

It should not attempt:

- full detector implementation in the first slice;
- broad CI enforcement of heuristic style judgments;
- authorship attribution;
- a generic style marketplace;
- free-form "make code less AI-looking" rhetoric as policy.

## Governing Reference

The higher-order concept note for this follow-on is:

- `docs/DRAFT_SYNTHETIC_STRUCTURE_DRIFT_v0.md`

That note is the place to evolve the neutral abstraction, drift families, ODEU
framing, automation tiers, and agent-embedding plan.
