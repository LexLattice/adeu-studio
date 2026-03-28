# Locked Continuation vNext+93

Status: `V42-E` implementation contract.

## V93 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v42e_arc_scorecard_competition_contract@1",
  "target_arc": "vNext+93",
  "target_path": "V42-E",
  "target_scope": "arc_scorecard_replay_and_competition_posture_baseline_over_released_local_eval",
  "task_packet_schema": "adeu_arc_task_packet@1",
  "observation_frame_schema": "adeu_arc_observation_frame@1",
  "hypothesis_frame_schema": "adeu_arc_hypothesis_frame@1",
  "action_proposal_schema": "adeu_arc_action_proposal@1",
  "rollout_trace_schema": "adeu_arc_rollout_trace@1",
  "local_eval_record_schema": "adeu_arc_local_eval_record@1",
  "scorecard_manifest_schema": "adeu_arc_scorecard_manifest@1",
  "implementation_packages": [
    "adeu_arc_agi",
    "adeu_arc_solver"
  ],
  "authoritative_upstream_source": "V42-A_V42-B_V42-C_V42-D_released_artifacts",
  "local_first_foundation_required": true,
  "scorecard_authority_surface_required": true,
  "scorecard_source_kind_discriminator_required": true,
  "authority_posture_decomposition_required": true,
  "competition_mode_posture_enum_required": true,
  "replay_lineage_binding_required": true,
  "local_external_replay_authority_separation_required": true,
  "environment_session_identity_required": true,
  "scorecard_metrics_non_official_guard_required": true,
  "summary_non_authoritative_required": true,
  "competition_mode_posture_required": true,
  "local_online_authority_separation_required": true,
  "settlement_posture_carry_required": true,
  "authority_class_fixture_matrix_required": true,
  "leaderboard_overclaim_rejection_required": true,
  "direct_online_submission_deferred": true,
  "benchmark_tournament_orchestration_deferred": true,
  "api_web_operator_surfaces_deferred": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "decomposition_doc": "docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v24.md"
}
```

## Slice

- Arc label: `vNext+93`
- Family label: `V42-E`
- Scope label: ARC scorecard/replay and competition-posture baseline over released local eval

## Objective

Introduce the first scorecard/replay and competition-posture widening for ARC
participation by releasing one canonical `adeu_arc_scorecard_manifest@1` over released
`V42-A`/`V42-B`/`V42-C`/`V42-D` lineage, while preserving explicit local-vs-online
authority separation, deterministic replay lineage, settlement/entitlement carry-through,
and fail-closed anti-overclaim posture.

This slice establishes the first ADEU ARC scorecard substrate for:

- deterministic scorecard-manifest emission over one released local-eval chain;
- explicit scorecard authority posture as decomposed typed surfaces rather than
  prose-only claims;
- explicit scorecard source-kind discrimination between local shadow posture and
  official imported scorecard authority;
- explicit replay-lineage binding back to released local-eval evidence;
- explicit competition-mode posture as bounded enum states without forcing submission
  behavior;
- explicit separation between local replay lineage and external replay authority refs;
- explicit environment/session/competition-scope identity carry-through;
- explicit rejection of leaderboard-readiness and universal-necessity overclaim from
  bounded local/scorecard evidence.

This slice remains deliberately prior to:

- direct online competition submission execution;
- benchmark tournament orchestration;
- API/web operator routes and productized workbench surfaces;
- generalized multi-agent or multi-benchmark orchestration.

Its job is to prove that scorecard/replay authority seams can be made explicit and
auditable before deployment-mode widening.

## Frozen Implementation Decisions

1. Active package strategy:
   - activate bounded `V42-E` surfaces in:
     - `packages/adeu_arc_agi` for authoritative schema ownership and scorecard-manifest
       artifact handling;
     - `packages/adeu_arc_solver` for bounded scorecard/replay derivation helpers;
   - no direct submission, tournament, or product-surface helpers may be activated in
     this slice.
2. Upstream authority strategy:
   - `vNext+93` must consume released:
     - `adeu_arc_task_packet@1`,
     - `adeu_arc_observation_frame@1`,
     - `adeu_arc_hypothesis_frame@1`,
     - `adeu_arc_action_proposal@1`,
     - `adeu_arc_rollout_trace@1`,
     - `adeu_arc_local_eval_record@1`
     as authoritative scorecard inputs;
   - it may not bypass released lineage with prompt-authored ambient reinterpretation.
3. Scorecard source-kind strategy:
   - `adeu_arc_scorecard_manifest@1` must carry explicit `scorecard_source_kind` as one
     of:
     - `local_shadow_only`
     - `official_imported`
     - `competition_posture_declared_no_official_scorecard`
     - `deferred_absent`
   - scorecard outputs may not impersonate official external scorecard authority unless
     `scorecard_source_kind` is `official_imported` and authority basis refs are valid.
4. Scorecard authority strategy:
   - `adeu_arc_scorecard_manifest@1` is authoritative for bounded scorecard/replay
     posture in this slice;
   - authority posture may be declared only through decomposed machine-checkable fields:
     - `authority_scope`
     - `authority_source_kind`
     - `authority_validity`
     - `authority_limitations`
     - `authority_basis_refs`
   - `scorecard_outcome_summary` remains descriptive-only and may not override typed
     authority surfaces;
   - local evaluation success may constrain scorecard interpretation but may not mint
     leaderboard-readiness or competition-success authority.
5. Replay-lineage strategy:
   - scorecard artifacts must preserve explicit local replay lineage refs back to released
     `V42-D` local-eval evidence and upstream `V42-A` through `V42-C` lineage;
   - scorecard artifacts must also carry explicit external replay authority refs, which
     may be empty/deferred when no official external replay authority exists;
   - local replay lineage and external replay authority refs may not be conflated;
   - replay lineage must remain deterministic and fail closed on missing required refs.
6. Competition-mode posture strategy:
   - competition mode is represented in this slice as typed posture and authority
     boundaries;
   - `competition_mode_posture` must be one of:
     - `not_applicable`
     - `declared_deferred`
     - `eligible_but_not_exercised`
     - `officially_exercised`
   - `officially_exercised` posture is invalid unless authority/source-kind fields
     explicitly support `official_imported` status with valid basis refs;
   - direct online submission execution remains deferred;
   - scorecard outputs must distinguish:
     - local-only authority,
     - competition-posture declared,
     - competition-posture deferred.
7. Environment/session identity strategy:
   - scorecard artifacts must preserve explicit environment/session identity and
     competition scope refs for authority interpretation:
     - `environment_ref`
     - `session_ref`
     - `competition_scope_ref`
8. Settlement-carry strategy:
   - settlement/ambiguity/claim-posture carry from released decomposition/action/eval
     artifacts must remain explicit in scorecard outputs;
   - one successful scorecard trajectory may not mint universal necessity.
9. Local-first and widening strategy:
   - `vNext+93` widens into scorecard/replay posture only;
   - tournament orchestration and operator product surfaces remain deferred.
10. Path decomposition strategy:
   - `vNext+93` is the first concrete `V42-E` arc;
   - any further deployment widening remains available only for later concrete arcs.

## Required Deliverables

1. New typed scorecard/replay surface:
   - extend bounded ARC helpers under `packages/adeu_arc_agi` and
     `packages/adeu_arc_solver` to materialize canonical scorecard manifests over
     released `V42-A`/`V42-B`/`V42-C`/`V42-D` artifacts;
   - export schema helpers for authoritative and mirrored JSON-schema output;
   - keep direct submission/tournament/API/web surfaces out of scope.
2. Canonical artifact:
   - `adeu_arc_scorecard_manifest@1`
3. Deterministic entrypoints that:
   - consume one released task/observation/hypothesis/action/rollout/local-eval chain;
   - materialize one canonical scorecard manifest;
   - fail closed when lineage, authority posture typing, replay binding, or
     settlement-carry posture is invalid.
4. Top-level schema anchors for `adeu_arc_scorecard_manifest@1`:
   - `schema`
   - `scorecard_manifest_id`
   - `task_packet_id`
   - `task_packet_ref`
   - `observation_frame_id`
   - `observation_frame_ref`
   - `hypothesis_frame_id`
   - `hypothesis_frame_ref`
   - `action_proposal_id`
   - `action_proposal_ref`
   - `rollout_trace_id`
   - `rollout_trace_ref`
   - `local_eval_record_id`
   - `local_eval_record_ref`
   - `environment_ref`
   - `session_ref`
   - `competition_scope_ref`
   - `scorecard_scope`
   - `scorecard_profile`
   - `model_id`
   - `run_id`
   - `scorecard_source_kind`
   - `authority_posture`
   - `authority_scope`
   - `authority_source_kind`
   - `authority_validity`
   - `authority_limitations`
   - `competition_mode_posture`
   - `local_replay_lineage_refs`
   - `external_replay_authority_refs`
   - `scorecard_facing_metrics`
   - `official_scorecard_outcome_metrics`
   - `scorecard_outcome_summary`
   - `settlement_posture_carry`
   - `authority_basis_refs`
   - `deferred_authority_assertions`
   - `evidence_refs`
5. Deterministic laws that fail closed on at least:
   - any scorecard artifact not lineage-bound to one released upstream chain including
     one released local-eval record;
   - any scorecard artifact missing explicit `scorecard_source_kind` discriminator;
   - any scorecard output missing typed authority-posture surfaces;
   - any scorecard output with `authority_source_kind` or
     `competition_mode_posture` outside released enums;
   - any scorecard output that claims `official_imported` source kind without explicit
     valid authority basis refs;
   - any scorecard output missing local replay lineage refs;
   - any scorecard output that conflates local replay lineage with external replay
     authority refs;
   - any scorecard output carrying `official_scorecard_outcome_metrics` while
     `scorecard_source_kind` is not `official_imported`;
   - any scorecard output that treats local-only evidence as leaderboard-readiness or
     competition-success authority;
   - any scorecard output that omits settlement-posture carry while claiming finality;
   - any scorecard output that launders one successful trajectory into universal
     necessity;
   - any scorecard output that asserts direct online submission authority in `V42-E`;
   - any attempt to mint benchmark-tournament, API, or web operator authority inside
     `V42-E` artifacts.
6. Committed reference fixtures:
   - one accepted fixture ladder under `apps/api/fixtures/arc_agi/vnext_plus93/`
     covering:
     - one accepted authority-class case:
       `scorecard_source_kind = local_shadow_only`;
     - one accepted authority-class case:
       `scorecard_source_kind = competition_posture_declared_no_official_scorecard`;
     - one accepted authority-class case:
       `scorecard_source_kind = official_imported` with valid authority basis refs;
     - one rejected manifest missing replay-lineage binding;
     - one rejected manifest that presents local evidence as official scorecard
       authority;
     - one rejected manifest with leaderboard/competition overclaim from local-only
       evidence;
     - one rejected manifest with missing authority-posture typing;
     - one rejected manifest with settlement-posture erasure.
   - accepted fixtures must prove:
     - deterministic replay;
     - explicit authority-class matrix coverage across local/deferred/official source
       kinds;
     - explicit authority-posture typing;
     - explicit local-vs-competition posture separation;
     - explicit local-vs-external replay authority separation;
     - explicit replay-lineage carry-through;
     - no submission/tournament/operator authority leakage.
7. Python tests covering:
   - schema/model validation for scorecard-manifest artifacts;
   - authoritative/mirrored schema export parity;
   - deterministic replay from accepted fixture ladder;
   - acceptance of authority-class fixture matrix
     (`local_shadow_only`, `competition_posture_declared_no_official_scorecard`,
     `official_imported`);
   - rejection of missing authority-posture and replay-lineage surfaces;
   - rejection of local-as-official authority laundering;
   - rejection of leaderboard/competition overclaim from local-only evidence;
   - rejection of settlement-posture erasure;
   - rejection of direct-submission/tournament/operator authority leakage in `V42-E`.

## Hard Constraints

- `vNext+93` may not reopen or redefine released `V41`, `V42-A`, `V42-B`, `V42-C`, or
  `V42-D` contracts.
- `vNext+93` may not ship:
  - direct online competition submission execution,
  - benchmark tournament orchestration,
  - API/web operator routes,
  - generalized multi-benchmark or multi-agent orchestration.
- `vNext+93` may not treat scorecard outputs as authority unless authority posture and
  basis refs are explicit and valid.
- `vNext+93` may not emit official scorecard outcomes unless source kind is explicitly
  `official_imported` with valid authority basis refs.
- `vNext+93` may not treat local-only evidence as leaderboard-readiness authority.
- `vNext+93` may not mint post-hoc universal necessity claims from bounded scorecard
  outcomes.
- `vNext+93` may not collapse scorecard authority posture into summary-only prose;
  `scorecard_outcome_summary` remains descriptive and non-authoritative.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- scorecard schema release, deterministic derivation, fixtures, and fail-closed
  authority-boundary rules are one bounded seam;
- splitting these across multiple PRs would create artificial staging within the same
  `V42-E` boundary without reducing semantic risk.
