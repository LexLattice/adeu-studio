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

The missing layer is a bounded, typed module for pressure-mismatch drift patterns in
code and surrounding repo artifacts that can apply across:

- forward coding;
- post-code optimization;
- retrospective contribution assessment;
- later module-conformance checks.

Today the repo still lacks a canonical way to:

- encode a symptom corpus like "AI accent" without turning it into authorship rhetoric
  or style law;
- separate:
  - state-model drift,
  - abstraction-pressure drift,
  - semantic-communication drift,
  - shape-regularity drift,
  - meta-intent failure;
- record for each rule:
  - signal kind,
  - harm kind,
  - evidence regime,
  - allowed action;
- state which findings belong to:
  - deterministic local drift,
  - static contextual drift,
  - semantically ambiguous drift,
  - meta-governance drift;
- project those rules differently for:
  - the forward coding agent,
  - the post-code optimizer agent.

The repo also still lacks an explicit execution architecture for mixed-confidence
checks where a deterministic harness can classify a checkpoint and invoke the resident
coding agent only when synthetic reasoning is required.

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

Implement a bounded canonical taxonomy for pressure-mismatch drift patterns that are
currently described informally as an "AI accent."

The path should normalize that intake language into repo-native ADEU structure.

`V39-B` should introduce:

- a canonical `synthetic_pressure_mismatch_rule_registry@1`;
- a neutral typed drift taxonomy rather than an authorship detector;
- explicit ODEU framing for each rule:
  - `O`: signal kind and subject kind,
  - `E`: evidence mode and evidence regime,
  - `D`: allowed action and policy force,
  - `U`: expected utility gain;
- explicit separation of:
  - signal kind,
  - harm kind,
  - evidence regime,
  - allowed action,
  - resolution route;
- derived automation posture rather than one flat severity label.

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

- canonical `synthetic_pressure_mismatch_observation_packet@1`;
- canonical `synthetic_pressure_mismatch_conformance_report@1`;
- bounded deterministic detectors for the deterministic-local subset;
- one or more seed fixtures, likely beginning from the poetry utility reference and
  one repo-native reference diff.

### `V39-D`

Agent-policy projection lane:

- canonical `synthetic_pressure_mismatch_fix_plan@1`;
- forward coding agent policy projection;
- post-code optimizer policy projection;
- bounded safe-autofix support only for the narrow deterministic-local subset.

### `V39-E`

Hybrid execution lane:

- canonical `synthetic_pressure_mismatch_oracle_request@1`;
- canonical `synthetic_pressure_mismatch_oracle_resolution@1`;
- canonical `synthetic_pressure_mismatch_checkpoint_trace@1`;
- explicit checkpoint classifier:
  - `deterministic_pass`,
  - `deterministic_fail`,
  - `oracle_needed`,
  - `human_needed`;
- deterministic adjudicator with replay, cache, and version pinning;
- oracle outputs remain advisory only and may not directly authorize repo mutation;
- bounded human-escalation lane for unstable or contradictory oracle outputs.

This lane is intentionally later and higher-risk than `V39-B` through `V39-D`:

- it introduces novel repo infrastructure rather than extending an already-frozen
  schema family;
- it should not be pulled forward until the taxonomy, observation packet, and policy
  projection lanes are all structurally stable.

## First-Slice Boundary (`V39-B`)

`V39-B` should stay bounded to:

- taxonomy and registry only;
- typed pressure-mismatch families rather than broad style doctrine;
- explicit separation of signal, harm, evidence, allowed action, and resolution route;
- explicit false-positive risk, counterexample handling, and rewrite risk;
- explicit implementation decisions on schema-family placement and glossary strategy;
- forward-agent and post-optimizer policy hooks at the registry level only.

It should not attempt:

- full detector implementation in the first slice;
- broad CI enforcement of heuristic style judgments;
- authorship attribution;
- a generic style marketplace;
- free-form "make code less AI-looking" rhetoric as policy.

The hybrid execution architecture belongs later in `V39-E`, not in the first registry
slice.

At `V39-B` start, freeze two implementation choices explicitly:

- whether the first schema family lives in `adeu_core_ir` or a later dedicated
  conformance package;
- whether the drift vocabulary remains registry-local or emits a dedicated glossary
  artifact distinct from the `V36-A` same-context glossary.

## Governing Reference

The higher-order concept note for this follow-on is:

- `docs/DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md`

That note is the place to evolve the pressure-mismatch abstraction, drift families,
ODEU framing, evidence and action regimes, hybrid checkpoint architecture, and
agent-embedding plan.
