# Locked Continuation vNext+92

Status: `V42-D` implementation contract.

## V92 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v42d_arc_local_benchmark_eval_contract@1",
  "target_arc": "vNext+92",
  "target_path": "V42-D",
  "target_scope": "arc_local_eval_record_baseline_over_released_action_rollout",
  "task_packet_schema": "adeu_arc_task_packet@1",
  "observation_frame_schema": "adeu_arc_observation_frame@1",
  "hypothesis_frame_schema": "adeu_arc_hypothesis_frame@1",
  "action_proposal_schema": "adeu_arc_action_proposal@1",
  "rollout_trace_schema": "adeu_arc_rollout_trace@1",
  "local_eval_record_schema": "adeu_arc_local_eval_record@1",
  "implementation_packages": [
    "adeu_arc_agi",
    "adeu_arc_solver"
  ],
  "authoritative_upstream_source": "V42-A_V42-B_V42-C_released_artifacts",
  "local_first_required": true,
  "task_success_and_control_plane_joint_eval_required": true,
  "adherence_metric_decomposition_required": true,
  "evaluation_provenance_required": true,
  "orthogonality_fixture_matrix_required": true,
  "model_class_sensitivity_empirical_eval_required": true,
  "benchmark_aggregation_deferred": true,
  "settlement_posture_carry_required": true,
  "scorecard_and_replay_authority_deferred": true,
  "competition_mode_deferred": true,
  "deployment_surfaces_deferred": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "decomposition_doc": "docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v24.md"
}
```

## Slice

- Arc label: `vNext+92`
- Family label: `V42-D`
- Scope label: ARC local eval-record baseline over released action/rollout

## Objective

Introduce the first benchmark/evaluation widening for ARC participation by releasing one
canonical `adeu_arc_local_eval_record@1` over released `V42-A`/`V42-B`/`V42-C`
artifacts, while preserving local-only posture, deterministic replay lineage,
settlement-carry posture, and explicit control-plane honesty scoring before any
scorecard/replay authority or competition-mode surface is released.

Artifact identity rule for this slice:

- `vNext+92` intentionally releases a per-run local evaluation record;
- multi-run benchmark aggregation/coverage manifests remain deferred to a later `V42-D`
  continuation arc.

This slice establishes the first ADEU ARC local-eval substrate for:

- deterministic local eval-record emission over one released artifact chain;
- explicit joint evaluation of task success and control-plane adherence;
- typed control-plane adherence submetric decomposition;
- explicit evaluation provenance (`rule_set`, `method_version`, basis refs);
- explicit model-class sensitivity posture as empirical local evidence;
- explicit settlement/ambiguity posture carry checks in evaluation output;
- deterministic local fixture replay for accepted and rejected eval-record cases.
- explicit orthogonality matrix coverage showing task outcome and control-plane adherence
  as independent axes.

This slice remains deliberately prior to:

- `adeu_arc_scorecard_manifest@1` release;
- replay authority publication;
- competition-mode online integration;
- leaderboard-readiness claims;
- API/web operator surfaces.

Its job is to prove that local ARC evaluation can remain explicit and auditable without
widening into scorecard or deployment seams.

## Frozen Implementation Decisions

1. Active package strategy:
   - activate bounded `V42-D` surfaces in:
     - `packages/adeu_arc_agi` for authoritative schema ownership and canonical
       evaluation-record artifact handling;
     - `packages/adeu_arc_solver` for bounded local evaluation helpers;
   - no scorecard/replay or competition-mode helpers may be activated in this slice.
2. Upstream authority strategy:
   - `vNext+92` must consume released:
     - `adeu_arc_task_packet@1`,
     - `adeu_arc_observation_frame@1`,
     - `adeu_arc_hypothesis_frame@1`,
     - `adeu_arc_action_proposal@1`,
     - `adeu_arc_rollout_trace@1`
     as authoritative benchmark inputs;
   - it may not bypass released lineage with prompt-authored or ambient state
     reinterpretation.
3. Evaluation doctrine strategy:
   - local evaluation output must keep task-success metrics and control-plane adherence
     metrics explicit and separate;
   - this slice may not label a single-run artifact as benchmark aggregation authority;
   - true benchmark aggregation surfaces (`run_register`, coverage denominators,
     model-comparison aggregates) remain deferred in this arc;
   - `V42-D` may constrain later scorecard doctrine but may not mint scorecard authority;
   - local evaluation success may not be promoted to leaderboard-readiness claims.
4. Adherence-metric strategy:
   - control-plane adherence may not be emitted as one opaque blob;
   - adherence output must be decomposed into typed sub-surfaces including at least:
     - lineage completeness
     - ambiguity carry fidelity
     - claim-posture honesty
     - deontic compliance
     - expectation/outcome honesty
     - no retroactive necessity laundering
     - no hidden scorecard/replay leakage.
5. Settlement-carry strategy:
   - evaluation output must preserve explicit settlement/ambiguity/claim-posture
     carry-through from released `V42-B`/`V42-C` artifacts;
   - one successful local trajectory may not mint universal necessity claims.
6. Evaluation provenance strategy:
   - evaluation outputs must carry explicit provenance anchors for:
     - `evaluation_rule_set_ref`
     - `evaluation_method_version`
     - `task_success_basis`
     - `adherence_metric_basis`
     - `ground_truth_refs`
     - `benchmark_scope`
     - `sample_basis`.
   - `evaluation_summary` is descriptive only and may not be authoritative over typed
     metric/provenance surfaces.
7. Model-sensitivity strategy:
   - model-class fit is empirical in this slice;
   - per-model local evaluation outputs must remain explicitly keyed and non-collapsed.
8. Deterministic replay strategy:
   - deterministic replay in `V42-D` means deterministic evaluation over released
     artifact chains and frozen rule sets;
   - this slice does not claim deterministic re-generation of model behavior itself.
9. Local-first and widening strategy:
   - `vNext+92` remains local/offline only;
   - scorecard/replay authority and competition mode remain deferred.
10. Path decomposition strategy:
   - `vNext+92` is the first concrete `V42-D` arc;
   - any widening into `V42-E` scorecard/competition surfaces remains available only for
     later concrete arcs outside this lock.

## Required Deliverables

1. New typed local-eval-record surface:
   - extend bounded ARC helpers under `packages/adeu_arc_agi` and
     `packages/adeu_arc_solver` to materialize canonical local evaluation records over
     released `V42-A`/`V42-B`/`V42-C` artifacts;
   - export schema helpers for authoritative and mirrored JSON-schema output;
   - keep scorecard/replay/competition surfaces out of scope.
2. Canonical artifact:
   - `adeu_arc_local_eval_record@1`
3. Deterministic entrypoints that:
   - consume one released task/observation/hypothesis/action/rollout chain;
   - materialize one canonical local evaluation record;
   - fail closed when lineage, evaluation-surface completeness, settlement-carry
     posture, or authority-boundary constraints are invalid.
4. Top-level schema anchors for `adeu_arc_local_eval_record@1`:
   - `schema`
   - `local_eval_record_id`
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
   - `benchmark_scope`
   - `benchmark_profile`
   - `model_id`
   - `run_id`
   - `sample_basis`
   - `evaluation_rule_set_ref`
   - `evaluation_method_version`
   - `task_success_basis`
   - `adherence_metric_basis`
   - `ground_truth_refs`
   - `task_success_metrics`
   - `adherence_metric_register`
   - `adherence_failure_register`
   - `control_plane_adherence_metrics`
   - `settlement_posture_checks`
   - `evaluation_summary`
   - `evidence_refs`
   - `deferred_authority_assertions`
5. Deterministic laws that fail closed on at least:
   - any local-eval artifact not lineage-bound to one released task/observation/
     hypothesis/action/rollout chain;
   - any local-eval output missing either task-success or control-plane adherence metrics;
   - any local-eval output missing typed adherence submetric decomposition;
   - any local-eval output missing evaluation provenance anchors;
   - any local-eval output that collapses settlement/ambiguity posture into certainty-only
     scoring;
   - any local-eval output that omits per-model identity while claiming model comparison;
   - any local-eval output that mints scorecard/replay/competition authority;
   - any local-eval output that emits leaderboard-readiness claims from local-only runs;
   - any local-eval output that launders one successful trajectory into universal
     task-rule necessity.
6. Committed reference fixtures:
   - one accepted fixture ladder under `apps/api/fixtures/arc_agi/vnext_plus92/`
     covering:
     - one deterministic local eval record over a released `V42-C` chain;
     - one accepted orthogonality case: task succeeds + control plane succeeds;
     - one accepted orthogonality case: task succeeds + control plane fails;
     - one accepted orthogonality case: task fails + control plane succeeds;
     - one accepted orthogonality case: task fails + control plane fails;
     - one rejected record missing adherence submetric decomposition;
     - one rejected record missing evaluation provenance anchors;
     - one rejected record with scorecard/replay or competition-authority leakage;
     - one rejected record with leaderboard-readiness overclaim from local-only data.
   - accepted fixtures must prove:
     - deterministic replay;
     - explicit joint task/adherence evaluation surfaces;
     - explicit orthogonality between task outcome and adherence posture;
     - explicit settlement-posture carry checks;
     - no scorecard/replay/competition authority leakage.
7. Python tests covering:
   - schema/model validation for local evaluation record artifacts;
   - authoritative/mirrored schema export parity;
   - deterministic replay from accepted fixture ladder;
   - acceptance of the four orthogonality matrix cases above;
   - rejection of adherence-surface omissions;
   - rejection of missing evaluation provenance anchors;
   - rejection of local-to-scorecard authority leakage;
   - rejection of leaderboard-readiness overclaim from local-only artifacts.

## Hard Constraints

- `vNext+92` may not reopen or redefine released `V41`, `V42-A`, `V42-B`, or `V42-C`
  contracts.
- `vNext+92` may not ship:
  - `adeu_arc_scorecard_manifest@1`,
  - replay authority artifacts,
  - competition-mode online submission,
  - benchmark tournament orchestration,
  - API/web operator routes,
  - leaderboard-readiness claims.
- `vNext+92` may not treat local benchmark output as scorecard authority.
- `vNext+92` may not treat a single local evaluation record as benchmark aggregation
  authority.
- `vNext+92` may not claim deterministic replay of model behavior generation; only
  deterministic evaluation over released artifact chains is in scope.
- `vNext+92` may not collapse task-success and control-plane adherence into one opaque
  composite metric without typed sub-surfaces.
- `vNext+92` may not mint post-hoc necessity claims from one successful local benchmark
  trajectory.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- benchmark schema release, deterministic derivation, fixtures, and fail-closed laws are
  one bounded evaluation seam;
- splitting these across multiple PRs would create artificial staging within the same
  `V42-D` boundary without reducing semantic risk.
