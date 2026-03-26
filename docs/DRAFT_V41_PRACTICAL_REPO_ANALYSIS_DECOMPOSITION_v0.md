# Draft V41 Practical Repo Analysis Decomposition v0

Status: working decomposition draft after `vNext+87` closeout and released `V41-A`,
`V41-B`, `V41-C`, `V41-D`, and `V41-E` practical-analysis baselines on `main`.

This document is an intermediate planning artifact between:

- the released ASIR architecture ladder;
- the practical repo-analysis use case now in view; and
- the next-family selection / first-lock docs.

It exists to prevent a direct jump from "ASIR exists as a typed artifact family" to
"one large practical harness rollout tries to land repo capture, observation,
alignment, and workflow wiring all at once."

This is not a lock doc. It does not authorize runtime behavior, schema release, or
implementation by itself.

## Purpose

- compile the practical repo-grounded ASIR use case into repo-sized implementation
  slices;
- keep the next family centered on habitual analysis of real codebases rather than on
  further abstract ASIR-only completion work;
- make the dual-compile model explicit before the first practical-analysis lock is
  drafted;
- keep intended architecture and observed implementation as separate typed lanes rather
  than collapsing them into one artifact;
- keep CLI / harness orchestration ahead of any future web or workbench widening.

## Inputs

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v23.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS77.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS78.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS79.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS80.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS81.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS82.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS83.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS84.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS85.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS86.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS87.md`

## Decomposition Thesis

`V40` solved the ASIR artifact ladder itself:

- semantic root;
- deterministic conformance;
- bounded hybrid;
- `adeu_core_ir@0.1` lowering;
- first UX compatibility lowering;
- family evidence and stop-gate continuity.

That is necessary, but it is not yet the practical loop the repo actually wants to
exercise habitually.

The missing practical loop is:

```text
repo scope + maintainer brief + accepted docs
    -> canonical analysis request and source_set
    -> analysis settlement / entitlement frame
    -> observed implementation frame
    -> intended architecture semantic IR
    -> deterministic alignment / drift report
    -> habitual runner that can be re-executed on real repos
```

That loop requires one additional family because it introduces a new operational seam:

- ASIR is no longer being proven only against frozen fixtures;
- it is being asked to analyze an actual repo subtree;
- both intent and implementation have to be made explicit and compared;
- the interpretive and entitlement frame for that comparison has to be externalized
  before compile-time claims are allowed;
- the result has to be repeatable enough that the same analysis can become a normal
  engineering habit rather than a one-off experiment.

## Baseline Agreement

- `vNext+82` (`V40-F`) is closed on `main`.
- `vNext+83` (`V41-A`), `vNext+84` (`V41-B`), `vNext+85` (`V41-C`),
  `vNext+86` (`V41-D`), and `vNext+87` (`V41-E`) are closed on `main`.
- The bounded `V40` family is complete on `main` at its intended baseline.
- The released ASIR ladder now exists end-to-end for semantic-root, conformance,
  hybrid, lowering, UX compatibility, and family evidence, and the practical
  request, settlement, observation, intended, and alignment seams now exist over one
  real repo scope.
- The next safe step is not to reopen `V40`, relitigate request/source-set capture,
  widen settlement/entitlement semantics, re-extract observed facts, relitigate
  intended compile authority, or reopen deterministic alignment; it is to
  habitualize the already-released stack through one bounded orchestration surface
  without silently widening into remediation, repo mutation, or merged-truth
  reconciliation.
- The Lean formal lane remains useful but sidecar-only and should not become a hidden
  prerequisite for practical repo analysis.

## Machine-Checkable Decomposition Baseline

```json
{
  "schema": "v41_practical_repo_analysis_decomposition@1",
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
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
  "next_path_family": "V41",
  "closed_current_family_paths": [
    "V41-A",
    "V41-B",
    "V41-C",
    "V41-D",
    "V41-E"
  ],
  "default_next_arc_candidate": "V41-F",
  "default_next_concrete_arc_candidate": "vNext+88",
  "v41_path_count": 6,
  "v41_default_arc_span": {
    "from": "vNext+88",
    "to": "vNext+88"
  },
  "v41_paths_may_span_multiple_arcs": true,
  "planned_family_packages": [
    "packages/adeu_architecture_ir",
    "packages/adeu_architecture_compiler"
  ],
  "analysis_request_artifact": "adeu_architecture_analysis_request@1",
  "analysis_settlement_artifact": "adeu_architecture_analysis_settlement_frame@1",
  "analysis_settlement_package": "packages/adeu_architecture_ir",
  "intended_lane_artifact": "adeu_architecture_semantic_ir@1",
  "observed_lane_artifact": "adeu_architecture_observation_frame@1",
  "observed_lane_package": "packages/adeu_architecture_compiler",
  "alignment_artifact": "adeu_architecture_alignment_report@1",
  "practical_runner_artifact": "adeu_architecture_analysis_run_manifest@1",
  "intended_observed_lane_separation_required": true,
  "precompile_settlement_required": true,
  "settlement_entry_grounding_required": true,
  "settlement_blocking_lineage_required": true,
  "source_set_snapshot_mode": "committed_tree_or_explicit_materialized_snapshot_only",
  "source_set_hashing_profile": "per_item_hashes_plus_aggregate_hash",
  "runner_mode": "cli_first_repo_grounded",
  "runner_blocked_distinct_from_alignment_blocked": true,
  "formal_kernel_mode": "proof_mirror_sidecar_only",
  "forbidden_first_lock_widenings": [
    "api_or_web_workbench_release",
    "direct_prompt_to_code_generation",
    "silent_intended_observed_artifact_collapse",
    "automatic_repo_mutation",
    "formal_kernel_required_for_practical_validity"
  ]
}
```

## Family Scale Rules

To stay aligned with prior ADEU implementation families, `V41` should obey these
decomposition rules:

- each path introduces one practical seam, not several unrelated ones;
- intended architecture and observed implementation must remain distinct until an
  explicit alignment step compares them;
- no path should mix repo capture, observation extraction, alignment, and workflow UI
  release in one slice;
- no path should require web or workbench integration merely to prove a lower-level
  contract;
- the first practical baseline should target one repo or bounded subtree, not a
  cross-repo fleet workflow.

## Package Activation Timing

- `packages/adeu_architecture_ir` remains the natural home for canonical practical
  request / source-set artifacts.
- `packages/adeu_architecture_ir` is also the natural home for the canonical
  settlement-frame artifact because it is a pre-compile governance surface.
- `packages/adeu_architecture_compiler` remains the natural home for observed-frame,
  alignment-report, and practical orchestration helpers.
- `V41` should prefer extending the released ASIR packages before inventing a new
  package family unless orchestration pressure makes a separate surface clearly
  necessary later.

## Concrete Arc Granularity

`V41` path labels are not assumed to map one-to-one onto concrete `vNext+` arcs.

The current recommended concrete split is:

- `vNext+83`
  - closed first concrete `V41-A` arc:
    analysis-request schema/model/export baseline, deterministic source-set capture,
    repo-scope selection, accepted-input hashing, authority-boundary policy pinning,
    and reference fixtures
- `vNext+84`
  - closed first concrete `V41-B` arc:
    settlement-frame schema/model/export baseline plus interpretation register,
    deontic typing, affordance decisions, claim posture, explicit compile-entitlement
    gating, and escalation trigger policy over the released request/source-set
    boundary
- `vNext+85`
  - closed first concrete `V41-C` arc:
    observed implementation frame schema/model/export baseline plus deterministic repo
    observation over one bounded codebase slice
- `vNext+86`
  - closed first concrete `V41-D` arc:
    repo-grounded intended root-family compile over the released request,
    settlement, and observation boundary using the released `V40-A` semantic-root
    family rather than only frozen synthetic fixtures
- `vNext+87`
  - closed first concrete `V41-E` arc:
    deterministic alignment report, mismatch classes, stable finding ids, severity /
    blocking posture, and drift diagnostics between intended and observed lanes
- `vNext+88`
  - default first concrete `V41-F` arc:
    CLI-first practical runner / harness orchestration that produces the full analysis
    bundle habitually for one internal repo or subtree

Later `V41` paths may also take one or more concrete arcs when that keeps each lock
comparable to earlier ADEU slices.

## Recommended `V41` Slice Ladder

| Path | Theme | Primary output | Baseline role |
|---|---|---|---|
| `V41-A` | analysis request + source-set capture | canonical repo-grounded request artifact | required |
| `V41-B` | settlement + entitlement gating | analysis settlement frame | required |
| `V41-C` | observed implementation observation | observed architecture frame | required |
| `V41-D` | intended repo-grounded compile | intended `adeu_architecture_semantic_ir@1` over real repo context | required |
| `V41-E` | alignment and drift diagnostics | deterministic alignment report | required |
| `V41-F` | practical runner / habitual orchestration | canonical analysis run manifest + repeatable CLI analysis loop | required |

## Path V41-A: Analysis Request and Source-Set Capture

Lock class: `L1`

Goal:

- establish one canonical request artifact and one deterministic source-set posture for
  practical repo-grounded architecture analysis.

Scope:

- canonical `adeu_architecture_analysis_request@1`;
- explicit repo-root-relative scope selection defined as:
  - one subtree anchor;
  - optional explicit file additions;
  - explicit exclusion rules;
  - allowed artifact kinds for docs, code, config, and tests;
- hash-bound `source_set` capture for selected docs, code, config, and tests;
- first-baseline snapshot posture limited to:
  - committed tree content; or
  - an explicitly materialized snapshot captured inside the request,
  not ambient live working-tree state by itself;
- immutable snapshot identity over the chosen mode;
- per-item source hashes plus one aggregate `source_set` hash;
- maintainer brief / non-goal / accepted-doc refs bound into the same request;
- explicit pinned `authority_boundary_policy` or exact policy ref;
- settlement-frame hooks only, without pretending semantic settlement is complete;
- authoritative and mirrored schema exports;
- one committed reference fixture over one bounded repo subtree.

Locks:

- no observed implementation extraction yet;
- no intended ASIR compile yet;
- no alignment report yet;
- no semantic settlement, drift claim, or impossibility claim authority yet;
- no runner release yet;
- no API or web integration yet.

Acceptance:

- one bounded repo scope can be selected deterministically;
- the request artifact binds source refs, per-item hashes, aggregate hash, snapshot
  mode, accepted brief inputs, and policy pinning exactly;
- source-set replay is deterministic.

Expected PR shape:

- single integrated PR

## Path V41-B: Interpretation Settlement, Deontic Typing, and Entitlement Gating

Lock class: `L1`

Goal:

- externalize the chosen interpretation and claim-governance posture before observed
  extraction, intended compile, or drift claims begin.

Scope:

- canonical `adeu_architecture_analysis_settlement_frame@1`;
- exact consumption of the released `V41-A` analysis request over the same
  `analysis_request_id`, `source_set_hash`, and pinned authority-boundary policy;
- chosen interpretation plus explicit interpretation register over the request;
- each interpretation entry should remain explicitly addressable and grounded at least
  by:
  - `interpretation_id`
  - canonical summary
  - support refs
  - linked ambiguity refs;
- prompt-content / brief-content deontic typing at least for:
  - required
  - forbidden
  - permitted
  - optional_hint
  - fallback_affordance
- each deontic typing entry should remain explicitly addressable and grounded at least
  by:
  - `typing_id`
  - `target_ref`
  - `target_kind`
  - `deontic_class`
  - rationale;
- affordance decisions recording when a permitted affordance was:
  - used
  - deferred
  - intentionally declined
  together with rationale;
- every request-bound affordance surfaced by deontic typing should also emit one
  explicit affordance-decision record;
- claim posture classification at least for:
  - observed
  - inferred
  - conjectural
  - unentitled_negative_claim
- each claim-posture entry should remain explicitly addressable and grounded at least
  by:
  - `claim_id`
  - `claim_ref`
  - `posture_class`
  - rationale;
- any `unentitled_negative_claim` should also record why it is unentitled, at least
  through one bounded-support marker such as:
  - `search_absence`
  - `proof_not_attempted`
  - `ambiguity_dependent`
  - `assumption_pressure`;
- the starter negative-claim posture must not collapse "not found within current
  search/proof bound" into proved impossibility; any stronger impossibility taxonomy
  remains deferred unless a later lock freezes an explicit proof surface;
- escalation trigger policy at least for:
  - unresolved_high_impact_ambiguity
  - silent_semantic_assumption_needed
  - impossibility_claim_without_proof
  - externalized_search_or_check_required
- explicit pre-compile entitlement posture with:
  - entitled
  - blocked
  only;
- explicit `blocking_lineage` when compile entitlement remains blocked;
- any free-text notes field should stay advisory only and must not become the real
  home for interpretations, typed classes, escalation support, or blocking reasons;
- authoritative and mirrored schema exports.

Locks:

- no observed implementation extraction yet;
- no intended ASIR compile yet;
- no final alignment report yet;
- no automatic code edits or repair suggestions yet;
- no hidden settlement through free prose or silent branch choice;
- no mushy typed-top / prose-inside register entries;
- no silent promotion of permissions or fallback affordances into obligations;
- no compile-entitlement claim while unresolved high-impact ambiguity, active
  escalation triggers, or unentitled negative claims remain.

Acceptance:

- one bounded repo scope emits a deterministic settlement frame;
- chosen reading, unresolved high-impact ambiguity, affordance decisions, claim
  posture, compile entitlement, and escalation triggers remain explicit;
- downstream compile lanes can no longer claim settlement was implicit.

Expected PR shape:

- single integrated PR

## Path V41-C: Observed Implementation Observation

Lock class: `L1`

Goal:

- compile one bounded codebase slice into a typed observed architecture frame with
  exact provenance back to repo files.

Scope:

- canonical `adeu_architecture_observation_frame@1`;
- exact consumption of the released `V41-A` request boundary and released `V41-B`
  settlement frame over the same repo world;
- deterministic extraction of observed surfaces, boundaries, workflows, authority
  sources, evidence hooks, and observability surfaces from a bounded repo scope;
- explicit provenance refs to concrete source files;
- explicit per-entry `observation_mode = direct | derived` so later lanes can tell
  raw file-grounded facts from bounded derived structure;
- explicit carry-through of upstream settlement posture through
  `upstream_compile_entitlement` and `upstream_blocking_refs`;
- observation may consume either `compile_entitlement = entitled` or
  `compile_entitlement = blocked` from the released settlement frame, but may not
  upgrade, reinterpret, or erase that settlement posture;
- observed-lane output is limited to extracted implementation facts and unresolved
  observations, not inferred intent, evaluation, or remediation;
- explicit unknown / unresolved observation markers rather than silent invention,
  including bounded unresolved-reason typing.

Locks:

- observed implementation may not mint intended architecture truth;
- no human brief semantics may be smuggled into the observed lane;
- no alignment report yet;
- no automatic code edits or repair suggestions yet.

Acceptance:

- one bounded repo scope emits a deterministic observed architecture frame;
- extraction remains provenance-linked and fail-closed on lineage/provenance contract
  violations while preserving unresolved observations when bounded extraction cannot
  determine a fact from a valid repo world;
- cross-entry workflow/boundary refs resolve to typed in-frame observation entries
  rather than floating above ungrounded structure;
- unresolved observations remain explicit.

Expected PR shape:

- single integrated PR

## Path V41-D: Intended Repo-Grounded ASIR Compile

Lock class: `L1`

Goal:

- compile one real repo-grounded maintainer brief into intended ASIR using the released
  `V40` ladder rather than only synthetic reference fixtures.

Scope:

- settlement-frame-governed intended compile entrypoint into the released `V40-A`
  semantic-root family;
- request-bound maintainer brief and accepted-doc lineage under the released
  settlement frame as the normative driver of intended compile;
- exact consumption of the released `V41-C` observation frame as companion practical
  input without collapsing intended and observed lanes;
- repo-grounded intended `adeu_architecture_semantic_ir@1` plus companion released
  root-family artifacts over the same frozen repo `source_set` selected by `V41-A`,
  not an independent brief universe;
- committed intended-architecture reference fixture ladder for one internal repo or
  subtree.

Locks:

- intended and observed lanes must remain separate artifacts;
- observation may constrain, block, or force ambiguity/advisory posture, but may not
  become the hidden source of intended truth;
- no alignment report yet;
- no practical-loop conformance, checkpoint, projection, or UX emission yet;
- the broader `V41-D` path may later admit bounded checkpoint/oracle reuse when
  ambiguity remains, but the first concrete `vNext+86` arc intentionally defers that
  practical reuse;
- no new projection or product-surface release is required in this path;
- no direct prompt output becomes architecture truth without the released ASIR
  root-family validators and settlement-frame gating.

Acceptance:

- one repo-grounded maintainer brief compiles into intended root-family artifacts
  deterministically;
- blocked settlement remains fail-closed and does not emit authoritative intended
  output;
- unresolved or derived observations that matter to intent remain visible as
  ambiguity, advisory posture, or refusal to settle rather than disappearing;
- request, settlement, and observation lineage is preserved into emitted intended
  ASIR.

Expected PR shape:

- single integrated PR

## Path V41-E: Alignment and Drift Diagnostics

Lock class: `L0`

Goal:

- compare intended architecture and observed implementation deterministically and make
  misalignment inspectable without collapsing the two lanes.

Scope:

- canonical `adeu_architecture_alignment_report@1`;
- exact consumption of the released `V41-A` request boundary, released `V41-B`
  settlement frame, released `V41-C` observation frame, and released `V41-D`
  intended root-family outputs over the same practical repo world;
- released `adeu_architecture_semantic_ir@1` as the authoritative intended
  comparison surface for the first concrete alignment baseline, with companion
  intended root-family refs admitted only through an explicit support contract;
- deterministic starter mismatch classes at least for:
  - declared_not_observed
  - observed_not_declared
  - authority_boundary_drift
  - workflow_or_state_drift
  - evidence_or_observability_gap
  - unresolved_unknown
- the starter class set is intentionally bounded and not the whole future ontology of
  drift;
- stable deterministic finding ids over the starter classes, derived from canonical
  typed support tuples with deterministic deduplication and ordering;
- severity / blocking posture for alignment findings;
- unresolved unknowns must remain first-class findings rather than vanishing into
  notes or by omission;
- exact lineage back to the intended ASIR, observed frame, settlement frame, and
  analysis request.

Locks:

- no silent reconciliation of intended and observed artifacts into one merged truth;
- request boundary plus settlement frame remain the normative driver of intended
  truth, while observation may constrain, block, or force unresolved posture but may
  not become the hidden source of intended architecture;
- report-level `blocked` remains an alignment diagnostic posture over an already
  entitled comparison world and is not equivalent to upstream settlement
  `compile_entitlement = blocked`;
- no remediation plans or repo-mutation instructions in the first concrete `V41-E`
  arc;
- no automatic repo mutation or patch generation;
- no product-surface or workbench release yet.

Acceptance:

- one internal repo/subtree yields a deterministic alignment report;
- intended and observed lanes remain separately inspectable;
- at least one upstream ambiguity or unresolved observation survives into an explicit
  `unresolved_unknown` finding in the committed fixture ladder;
- high-impact misalignment fails closed rather than being normalized away.

Expected PR shape:

- single integrated PR

## Path V41-F: Practical Runner and Habitual Orchestration

Lock class: `L0`

Goal:

- make the repo-grounded ASIR analysis loop runnable habitually by a maintainer or
  orchestrator over one bounded repo scope without widening into remediation or
  repo-mutation authority.

Scope:

- canonical `adeu_architecture_analysis_run_manifest@1`;
- CLI-first orchestration over:
  - analysis request
  - source-set capture
  - settlement frame
  - observed frame
  - intended ASIR
  - alignment report
- exact sequencing over the released `V41-A` through `V41-E` stack;
- deterministic run identity plus deterministic output-root and runtime-evidence-root
  placement;
- authoritative manifest emission even for settlement-blocked runs, so blocked stops
  remain typed and replayable;
- canonical stage ledger over:
  - request
  - settlement
  - observation
  - intended
  - alignment
  - manifest;
- explicit runner-level stop posture when settlement blocks intended compile or
  alignment emission;
- explicit distinction between runner-level blocked stop and a completed run whose
  consumed alignment report may still carry `alignment_posture = blocked`;
- deterministic artifact placement under repo-native artifact directories;
- bounded evidence bundle for reruns over one internal repo or subtree;
- no requirement for web or workbench integration in the first baseline.

Locks:

- no hidden recomputation of settlement entitlement or alignment posture inside the
  runner;
- no shadow intended or alignment artifacts may be emitted after a settlement-blocked
  stop;
- blocked runs must carry `terminal_alignment_posture = none` rather than inferred
  alignment state;
- no silent reconciliation of intended and observed artifacts into one merged truth;
- no remediation plans or repo-mutation instructions in the runner output;
- no web or API workbench release by default;
- no multi-repo fleet orchestration in the first baseline;
- no direct PR-authority or code-edit authority in the runner itself.

Acceptance:

- the practical loop can be re-run habitually against one internal repo or subtree;
- artifacts remain deterministic and provenance-linked;
- the accepted fixture ladder proves one completed run over the full released stack
  and one settlement-blocked stop before intended or alignment emission;
- `run_id` and stage-ledger replay remain deterministic across reruns;
- runner-level blocked stop is visibly distinct from an emitted alignment report whose
  own posture is `blocked`;
- reruns make intent / implementation drift visible without requiring a separate
  one-off maintainer assembly process.

Expected PR shape:

- single integrated PR
