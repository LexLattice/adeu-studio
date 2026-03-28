# Locked Continuation vNext+90

Status: `V42-B` implementation contract.

## V90 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v42b_arc_observation_hypothesis_contract@1",
  "target_arc": "vNext+90",
  "target_path": "V42-B",
  "target_scope": "arc_observation_and_hypothesis_baseline_over_released_task_packet",
  "task_packet_schema": "adeu_arc_task_packet@1",
  "observation_frame_schema": "adeu_arc_observation_frame@1",
  "hypothesis_frame_schema": "adeu_arc_hypothesis_frame@1",
  "implementation_packages": [
    "adeu_arc_agi",
    "adeu_arc_solver"
  ],
  "authoritative_task_packet_source": "V42-A_released_task_packet",
  "local_first_required": true,
  "odeu_decomposition_gate_required": true,
  "ontology_register_required": true,
  "derived_observation_hypothesis_separation_required": true,
  "utility_pressure_register_required": true,
  "working_hypothesis_posture_required": true,
  "decomposition_coverage_denominator_required": true,
  "observation_hypothesis_bleed_rejection_fixture_required": true,
  "control_plane_honesty_required": true,
  "settlement_posture_required": true,
  "action_and_rollout_artifacts_deferred": true,
  "scorecard_and_competition_mode_deferred": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "decomposition_doc": "docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v24.md"
}
```

## Slice

- Arc label: `vNext+90`
- Family label: `V42-B`
- Scope label: ARC observation and hypothesis baseline over released task packet

## Objective

Introduce the first semantic-decomposition widening for ARC participation by releasing:

- one canonical `adeu_arc_observation_frame@1`; and
- one canonical `adeu_arc_hypothesis_frame@1`

over the released `V42-A` task-packet boundary, while preserving explicit O/E/D/U
discipline, claim posture, unresolved ambiguity carry-through, and control-plane honesty
before any action-proposal, rollout, scorecard, or competition-mode surface is released.

This slice establishes the first ADEU ARC interpretation substrate for:

- first-class ontology decomposition inventory over frozen ARC state;
- deterministic extraction of direct-vs-derived observed ARC facts;
- typed unresolved-observation carry-through rather than forced pseudo-completeness;
- typed hypothesis register over observed facts with explicit claim posture;
- explicit ambiguity register and bounded working-hypothesis posture;
- explicit utility/pressure register without tactical action commitment;
- deontic admissibility carry-through from released task-packet legality/mode boundaries;
- deterministic local fixture replay for both accepted and rejected decomposition cases.

This slice remains deliberately prior to:

- `adeu_arc_action_proposal@1` release;
- `adeu_arc_rollout_trace@1` release;
- local benchmark/tournament orchestration;
- scorecard or replay authority;
- competition-mode online integration;
- API/web operator surfaces.

Its job is to prove that ARC semantic anatomy and interpretation can be externalized
honestly before tactical action commitment is introduced.

## Frozen Implementation Decisions

1. Active package strategy:
   - activate bounded `V42-B` surfaces in:
     - `packages/adeu_arc_agi` for authoritative schema ownership and canonical
       artifacts;
     - `packages/adeu_arc_solver` for bounded observation/hypothesis derivation helpers;
   - no action-search, rollout, or scorecard helpers may be activated in this slice.
2. Upstream authority strategy:
   - `vNext+90` must consume released `adeu_arc_task_packet@1` artifacts from `V42-A`
     as the frozen ARC world boundary;
   - it may not bypass packet authority with prompt-authored, ad hoc, or ambient state
     reinterpretation;
   - mode-policy and legal envelope authority remain sourced from the consumed task
     packet and may not be recomputed as hidden doctrine.
3. O/E/D/U decomposition strategy:
   - observation/hypothesis compilation must remain explicitly typed across:
     - `O`: ontology units and boundaries;
     - `E`: direct-vs-derived observation and epistemic posture;
     - `D`: deontic admissibility surfaces inherited from task packet;
     - `U`: explicit utility/pressure fields without certainty laundering;
   - `O` must be externally inspectable as typed ontology surfaces, not only implied by
     free-form observation prose;
   - no hidden solver assumptions may be smuggled into ontology or observation entries.
4. Observation-frame strategy:
   - `adeu_arc_observation_frame@1` is authoritative for observed ARC facts in this
     slice;
   - observation frame must expose first-class ontology surfaces including:
     - `ontology_register`
     - `entity_inventory`
     - `relation_inventory`
     - `state_partition_register`
     - `ontology_uncertainty_register`
   - `decomposition_coverage` must be denominator-bound through explicit:
     - `coverage_basis`
     - `required_dimension_set`
     - `missing_dimension_register`
   - each observation entry must carry:
     - direct or derived mode;
     - typed source/evidence refs;
     - resolution posture;
   - derived observations may depend only on direct observations plus released
     decomposition rules, and may not carry candidate governing-transform or task-rule
     claims that belong to hypothesis artifacts;
   - unresolved observations must stay explicit and typed.
5. Hypothesis-frame strategy:
   - `adeu_arc_hypothesis_frame@1` is authoritative for candidate interpretation in this
     slice;
   - each hypothesis entry must bind to supporting observation refs and deontic posture;
   - hypothesis frame must carry explicit:
     - `utility_pressure_register`
     - `working_hypothesis_posture`
   - `working_hypothesis_posture` is non-committing investigation posture and may not be
     interpreted as action commitment or settled task-rule truth;
   - ambiguity must remain first-class and may not be silently collapsed by prose.
6. Claim-entitlement strategy:
   - significant claims inside hypothesis output must carry explicit claim posture such
     as observed / inferred / conjectural / blocked;
   - bounded-search absence may not be emitted as impossibility;
   - one successful hypothesis branch may not mint family-level necessity.
7. Local-first and widening strategy:
   - `vNext+90` remains local/offline only;
   - action proposal, rollout, scorecard, replay authority, and competition mode remain
     deferred to later paths.
8. Path decomposition strategy:
   - `vNext+90` is the first concrete `V42-B` arc;
   - any widening into `V42-C` action/rollout surfaces remains available only for later
     concrete arcs outside this lock.

## Required Deliverables

1. New typed observation/hypothesis surface:
   - extend bounded ARC helpers under `packages/adeu_arc_agi` and
     `packages/adeu_arc_solver` to materialize canonical observation and hypothesis
     artifacts over released task packets;
   - export schema helpers for authoritative and mirrored JSON-schema output;
   - keep action/rollout/scorecard/competition surfaces out of scope.
2. Canonical artifacts:
   - `adeu_arc_observation_frame@1`
   - `adeu_arc_hypothesis_frame@1`
3. Deterministic entrypoints that:
   - consume one released `adeu_arc_task_packet@1`;
   - materialize one canonical `adeu_arc_observation_frame@1`;
   - materialize one canonical `adeu_arc_hypothesis_frame@1`;
   - fail closed when task-packet lineage, deontic boundary carry-through, O/E/D/U
     typing, or claim posture validation is invalid.
4. Top-level schema anchors for `adeu_arc_observation_frame@1`:
   - `schema`
   - `observation_frame_id`
   - `task_packet_id`
   - `task_packet_ref`
   - `environment_authority`
   - `mode_posture`
   - `game_ref`
   - `session_ref`
   - `ontology_register`
   - `entity_inventory`
   - `relation_inventory`
   - `state_partition_register`
   - `ontology_uncertainty_register`
   - `observation_entries`
   - `unresolved_observation_entries`
   - `decomposition_coverage`
   - `coverage_basis`
   - `required_dimension_set`
   - `missing_dimension_register`
5. Top-level schema anchors for `adeu_arc_hypothesis_frame@1`:
   - `schema`
   - `hypothesis_frame_id`
   - `task_packet_id`
   - `task_packet_ref`
   - `observation_frame_id`
   - `observation_frame_ref`
   - `hypothesis_register`
   - `ambiguity_register`
   - `claim_posture_register`
   - `deontic_admissibility_register`
   - `utility_pressure_register`
   - `working_hypothesis_posture`
6. Deterministic laws that fail closed on at least:
   - any observation/hypothesis artifact not lineage-bound to one released task packet;
   - any observation frame missing first-class ontology inventory surfaces;
   - any observation entry missing direct-vs-derived typing or evidence refs;
   - any observation artifact with denominator-free or opaque decomposition coverage;
   - any derived observation that carries governing-transform/task-rule claims rather
     than structural observation;
   - any hypothesis entry lacking supporting observation refs;
   - any ambiguity-dependent hypothesis emitted as settled without explicit posture;
   - any bounded-search absence emitted as impossibility;
   - any hypothesis/interpretation content laundered into observation fields under
     neutral or structural naming;
   - any attempt to mint action/rollout/scorecard authority inside `V42-B` artifacts;
   - any ontology or observation field carrying hidden solver/search commitments.
7. Committed reference fixtures:
   - one accepted fixture ladder under `apps/api/fixtures/arc_agi/vnext_plus90/`
     covering:
     - one deterministic observation frame + hypothesis frame over a released task
       packet;
     - one rejected observation artifact with missing O/E typing and evidence refs;
     - one rejected observation artifact with hypothesis-laundering bleed under derived
       observation naming;
     - one rejected hypothesis artifact with ambiguity laundering or unsupported
       impossibility posture;
   - accepted fixtures must prove:
     - deterministic replay;
     - explicit unresolved-observation carry-through;
     - explicit ambiguity and claim-posture carry-through;
     - no hidden action/rollout/scorecard leakage.
8. Python tests covering:
   - schema/model validation for observation and hypothesis artifacts;
   - authoritative/mirrored schema export parity;
   - deterministic replay from accepted fixture ladder;
   - rejection of O/E typing omissions;
   - rejection of denominator-free decomposition coverage;
   - rejection of hypothesis laundering inside derived observations;
   - rejection of unsupported impossibility posture;
   - rejection of hidden action/rollout/scorecard leakage in `V42-B`.

## Hard Constraints

- `vNext+90` may not reopen or redefine released `V41` contracts or released `V42-A`
  task-packet semantics.
- `vNext+90` may not ship:
  - `adeu_arc_action_proposal@1`,
  - `adeu_arc_rollout_trace@1`,
  - scorecard/replay authority,
  - competition-mode online submission,
  - benchmark tournament orchestration,
  - API/web operator routes,
  - leaderboard-readiness claims.
- `vNext+90` may not treat prose-only narrative as sufficient for decomposition or claim
  posture validation.
- `vNext+90` may not keep ontology decomposition implicit inside observation prose
  without first-class typed ontology surfaces.
- `vNext+90` may not use derived observation fields to carry candidate governing
  transform or task-rule hypothesis content.
- `vNext+90` may not convert bounded search absence into impossibility claims.
- `vNext+90` may not smuggle solver heuristics into ontology or observation fields under
  neutral naming.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- observation-frame and hypothesis-frame release is one bounded semantic seam;
- splitting schema, derivation, fixtures, and fail-closed laws would create artificial
  staging inside the same `V42-B` boundary without reducing semantic risk.
