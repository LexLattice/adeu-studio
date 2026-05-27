# Draft Next Arc Options v87

Status: planning draft after `HOB-0` family closeout and after support-layer
ProgramBench phase-transition audits.

Authority layer: planning.

This draft records the next candidate family after deterministic hierarchical
obligation traversal became reviewable. It does not authorize semantic
adjudication, ontology generation, phase execution, probe execution, command
execution, code edits, worker dispatch, implementation authority, product
authority, graph-memory authority, recursive policy amendment, PR creation,
commit, merge, release, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

This selector treats `HOB-0` as the immediate upstream family:

```text
HOB = deterministic obligation inheritance inside an ontology tree.
```

The next pressure is different:

```text
phase outputs exist
  -> transition conditions are assumed
  -> next phase starts too early
  -> evidence, object identity, obligation preservation, or authority posture
     is discovered to be invalid only after downstream work
```

## Current Frontier

The ProgramBench support runs exposed a repeatable transition failure:

```text
worker produces a plausible phase artifact
  -> orchestrator treats the artifact as transition-ready
  -> downstream implementation or evaluation begins
  -> later audit shows that the necessary O/E/D/U bridge was never proved
```

Two recent examples provide the motivating shape:

- `hyperfine`: the first large score jump came from recognizing that the
  constructed control schema was not yet proved equivalent to the real public
  control object. Product behavior could not be judged until parser and
  validation reachability were established.
- `xq`: pre-eval descent passes produced real improvements, but the run needed
  explicit saturation and transition checks to decide which artifacts could be
  promoted and which remaining quirks belonged to post-eval/source-tail
  pressure.

The missing mechanism is not another domain ontology node. It is a deterministic
transition broker over the meta-program circuit:

```text
phase A output
  -> O/E/D/U bridge validation
  -> legal next frontier
  -> no silent promotion, contamination, skipped gate, or stale-object reuse
```

Primary support inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v86.md`
- `docs/ARCHITECTURE_ADEU_HIERARCHICAL_OBLIGATION_BROKER_FAMILY_v0.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS272.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS273.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS274.md`
- `docs/support/principled_recursive_odeu_meta_program_experimental_v46.md`
- `docs/support/general_program_ontology_derived_v1_7.md`
- `artifacts/manual_runs/programbench_hyperfine_v44_gpt55_high_run_C_20260526T145836+0300/phase_outputs/p18_run_evolution_win_groups.md`

## Next Planning Question

Should the next family make phase-transition legality deterministic across the
ODEU meta-program circuit, without turning the tool into a semantic judge,
domain ontology author, probe runner, worker dispatcher, implementation planner,
or product authority?

Recommended candidate:

```text
OTB-0:
  ODEU Transition Broker
```

Alternate descriptive name:

```text
Phase ODEU Circuit Broker
```

The family label should remain `OTB-0` for compact slice naming.

## Family Thesis

`OTB-0` should implement the deterministic broker between completed phase
artifacts and legal next-phase frontiers.

The worker owns:

```text
semantic reasoning inside a phase
artifact production inside the assigned phase
uncertainty statements inside the assigned phase
proposed warrants and evidence references
```

The orchestrator and broker jointly need a deterministic transition layer:

```text
O: object identity, carried artifacts, transformations, and comparison targets
E: evidence required, evidence forbidden, and warrant boundary
D: obligations created, preserved, discharged, blocked, or explicitly deferred
U: use, purpose, allowed next phases, forbidden promotions, and failure routes
```

Controlling invariant:

```text
The worker operates inside phases.
The orchestrator operates over ODEU bridges between phases.

A downstream phase is not legal merely because an upstream artifact exists.
It is legal only when the bridge conditions for objects, evidence, obligations,
and use have been named, scoped, and witnessed.
```

## Recommended Next Pressure

- family / practical arc: `OTB-0`
- proposed name:
  - `OTB-0: ODEU Transition Broker`
- recommended first slice:
  - `OTB-0-A`
- recommended package ownership:
  - `packages/adeu_transition_broker`
  - schema mirrors under `spec/`
- adjacent future integration:
  - HOB outputs can be consumed as phase artifacts later;
  - semantic compiler outputs can be consumed as phase artifacts later;
  - ProgramBench reconstruction can use transition-broker outputs later;
  - no integration is selected by this planning draft.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `OTB-0-A` | Phase catalog, O/E/D/U bridge contracts, transition validation, and legal frontier emission |
| `OTB-0-B` | Transition closure/readiness summaries, gate execution planning, worker baton contracts, and evidence posture plans |
| `OTB-0-C` | Transition delta attribution, stale phase-object invalidation, integration handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`OTB-0-A` should be the first active slice. Candidate starter surfaces:

- `repo_phase_circuit_catalog@1`
- `repo_phase_bridge_contract@1`
- `repo_phase_transition_claim@1`
- `repo_phase_transition_validation_report@1`
- `repo_phase_legal_frontier_report@1`
- `repo_transition_broker_non_authority_guardrail@1`

`OTB-0-A` boundary clarification:

```text
OTB-0-A validates whether supplied phase catalog rows, bridge contracts,
transition claims, artifact references, evidence references, obligation
transfer rows, and claimed next phases are structurally admissible. It emits
blockers and legal frontier rows.

OTB-0-A does not compute full circuit readiness summaries. Aggregated
transition closure and operational planning belong to OTB-0-B.
```

`OTB-0-B` later surfaces:

- `repo_phase_transition_closure_report@1`
- `repo_phase_gate_execution_plan@1`
- `repo_phase_worker_baton_contract@1`
- `repo_phase_evidence_posture_plan@1`
- `repo_phase_operationalization_report@1`

`OTB-0-C` later surfaces:

- `repo_phase_transition_delta_attribution_ledger@1`
- `repo_phase_stale_object_invalidation_report@1`
- `repo_transition_broker_integration_handoff@1`
- `repo_transition_broker_family_closeout_alignment@1`

## Non-Authority Boundary

`OTB-0` may:

- validate fixed phase-circuit catalog shape;
- validate bridge contracts over O/E/D/U fields;
- validate phase artifact identity, hash, authority layer, and source phase;
- detect missing required objects for a claimed transition;
- reject forbidden evidence contamination;
- reject silent obligation drops between phases;
- reject illegal promotion from scoped, representative, or pressure-only
  posture to gold or official posture;
- detect stale phase artifacts after upstream object, catalog, or evidence
  changes;
- emit deterministic legal frontier rows;
- plan bounded transition gates and worker baton contracts in later slices;
- attribute transition failures to bridge fields when supplied with admissible
  run-delta rows in later slices.

`OTB-0` may not:

- decide semantic truth inside a phase;
- decide that a domain ontology node applies;
- invent or revise a domain ontology catalog by itself;
- recompute HOB subtree closure;
- inspect source code to decide product meaning;
- generate probes from freeform prose;
- execute probes or commands;
- dispatch workers;
- implement code;
- grant implementation authority;
- grant product or runtime authority;
- treat official benchmark failures as clean first-pass evidence;
- select future families.

## `OTB-0-A` Output Contract

`OTB-0-A` should output only:

1. fixed phase-circuit catalog records;
2. bridge contracts supplied by planning docs or upstream orchestration rules;
3. typed transition-claim records supplied by an orchestrator, worker closeout,
   planner, broker output, or manual review;
4. transition validation reports;
5. legal-frontier rows for missing, blocked, contaminated, stale, or invalid
   transitions;
6. non-authority guardrails;
7. deferred handoff notes for `OTB-0-B` and `OTB-0-C`.

It should not output:

- worker taskpacks;
- probe matrices;
- implementation batch contracts;
- code patches;
- command execution logs;
- product decisions;
- full circuit readiness summaries;
- score-delta attribution;
- official-eval claims;
- future-family selection.

## Candidate First-Slice Acceptance Tests

The first implementation slice should stay small and deterministic:

```text
Test 1: valid transition
  required O/E/D/U rows are present, no forbidden evidence, next phase allowed.

Test 2: missing object
  bridge requires an artifact ref that is absent; validation fails closed.

Test 3: forbidden evidence
  bridge forbids official-eval pressure but evidence row includes it;
  validation fails closed.

Test 4: silent obligation drop
  upstream obligation is required to be preserved or discharged but disappears;
  validation fails closed.

Test 5: illegal promotion
  upstream posture is scoped_ready or representative_only but next phase claims
  official_ready; validation fails closed.

Test 6: stale object
  artifact hash or catalog hash no longer matches the bridge row; validation
  emits stale-object blocker.

Test 7: legal frontier
  blocked transition emits deterministic next-frontier rows.

Test 8: canonical hash stability
  semantically identical input orderings produce stable canonical output hash.
```

## Review Hardening Before Lock

Before `OTB-0-A` is turned into a starter lock, the mapping should include these
review-derived hardening points:

- make `repo_phase_transition_claim@1` first-class, because artifact presence is
  not the same as a typed transition claim;
- split `bridge_consistency_status` from `bridge_completeness_status`;
- avoid standalone `ready`, `implementation_ready`, `gold_ready`, or
  `official_ready` outputs from `OTB-0-A`;
- use `valid_for_broker_frontier` or equivalent for A-level validation;
- treat action authorization as outside OTB authority;
- use multi-hash artifact identity:
  - `file_hash`;
  - `canonical_payload_hash`;
  - `semantic_object_hash`;
  - `catalog_hash`;
  - `bridge_hash`;
  - `evidence_boundary_hash`;
  - `obligation_set_hash`;
- check evidence ancestry, not only direct evidence refs;
- emit `posture_downgrade_required` frontier rows when a claim requests a
  stronger posture than the bridge can support;
- reject phase-local freshness mismatches over source objects, catalog, bridge,
  evidence boundary, obligation set, target substrate, run topology, artifact
  partition, or implementation-visible / checker-only split.

## Recommended Selection

Select `OTB-0` as the next family and select `OTB-0-A` as the next default
candidate after the family and slice mapping bundle receives review.

Starter-bundle target phrase:

```text
select `OTB-0-A` as the next default candidate
```

## Continuation After `OTB-0-A`

After `OTB-0-A` is released and closed on `main`, continue the selected
`OTB-0` family by drafting the next slice lock/decision/assessment sequence and
select `OTB-0-B` as the next default candidate.

## Continuation After `OTB-0-B`

After `OTB-0-B` is released and closed on `main`, continue the selected
`OTB-0` family by drafting the next slice lock/decision/assessment sequence and
select `OTB-0-C` as the next default candidate.
