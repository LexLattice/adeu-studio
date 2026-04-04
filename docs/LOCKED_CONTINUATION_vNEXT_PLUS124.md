# Locked Continuation vNext+124

Status: `V51-A` implementation contract.

## V124 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v51a_odeu_sim_kernel_contract@1",
  "target_arc": "vNext+124",
  "target_path": "V51-A",
  "target_scope": "bounded_repo_owned_odeu_simulation_kernel_package_for_one_region_one_commons_one_institution_one_archive_domain",
  "implementation_packages": [
    "adeu_odeu_sim"
  ],
  "governing_released_stack": "V49_semantic_forms_plus_V50_symbol_audit_as_adjacent_context_only_on_main",
  "governing_stack_consumption_mode": "adjacent_context_only_not_mandatory_dependencies_not_reopened_semantic_or_symbol_audit_semantics",
  "source_intake_bundle": "examples/external_prototypes/odeu-sandbox-app",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "odeu_sim_package_scaffold_required": true,
  "selected_schema_ids": [
    "adeu_odeu_lane_delta@1",
    "adeu_odeu_o_state@1",
    "adeu_odeu_e_state@1",
    "adeu_odeu_d_state@1",
    "adeu_odeu_u_state@1",
    "adeu_odeu_agent@1",
    "adeu_odeu_resource_pool@1",
    "adeu_odeu_institution@1",
    "adeu_odeu_norm@1",
    "adeu_odeu_observation@1",
    "adeu_odeu_evidence_record@1",
    "adeu_odeu_claim@1",
    "adeu_odeu_public_report@1",
    "adeu_odeu_audit_result@1",
    "adeu_odeu_sanction_event@1",
    "adeu_odeu_action_template@1",
    "adeu_odeu_action@1",
    "adeu_odeu_lane_crossing_contract@1",
    "adeu_odeu_scenario_config@1",
    "adeu_odeu_metric_point@1",
    "adeu_odeu_event_record@1",
    "adeu_odeu_world_state@1"
  ],
  "starter_domain_label": "one_region_one_commons_one_institution_one_archive",
  "starter_domain_constraints_frozen": [
    "one_region_only",
    "one_commons_resource_only",
    "one_institution_only",
    "one_public_archive_only",
    "one_action_per_agent_per_turn_only"
  ],
  "starter_scenarios_frozen": [
    "healthy_baseline",
    "weak_d"
  ],
  "canonical_replay_seed_frozen": 7,
  "canonical_replay_step_horizon_frozen": 25,
  "deterministic_replay_same_scenario_seed_initial_state_required": true,
  "unseeded_randomness_not_selected_here": true,
  "nested_submodels_frozen_in_models_py_required": true,
  "starter_lane_crossing_contracts_frozen": [
    "o_to_e_trace_contract",
    "e_to_d_legitimacy_contract",
    "d_to_o_allocation_contract",
    "u_to_d_pressure_contract"
  ],
  "lane_crossing_contract_surface_selected": "adeu_odeu_lane_crossing_contract@1",
  "typed_event_record_required": true,
  "event_log_string_list_not_selected_here": true,
  "deterministic_agent_iteration_order_frozen": "agent_id_ascending",
  "deterministic_action_tiebreak_law_frozen": "frozen_action_type_order_then_deterministic_target_order",
  "scenario_share_allocation_validation_required": true,
  "scenario_share_allocation_validation_rule": "each_share_between_zero_and_one_and_total_sum_equals_one",
  "heuristic_regime_classifier_diagnostic_only": true,
  "regime_classifier_not_control_authority": true,
  "regime_classifier_not_optimization_target": true,
  "api_surface_not_selected_here": true,
  "web_surface_not_selected_here": true,
  "persistent_storage_not_selected_here": true,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v34.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md",
    "docs/DRAFT_ADEU_ODEU_SIM_V51A_IMPLEMENTATION_MAPPING_v0.md",
    "examples/external_prototypes/odeu-sandbox-app/ALIGNMENT.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v34.md"
}
```

## Slice

- Arc label: `vNext+124`
- Family label: `V51-A`
- Scope label: bounded repo-owned ODEU simulation kernel package for one region, one
  commons, one institution, and one public archive

## Objective

Release the bounded `V51-A` kernel lane by creating the first repo-owned
`adeu_odeu_sim` package and freezing one typed simulation contract set rich enough to:

- declare one starter ontology over explicit O/E/D/U lane state;
- declare the key nested kernel objects as first-class typed models rather than only
  as subfields inside one `world_state` payload;
- declare one typed action catalog with explicit lane-delta posture;
- declare one typed lane-crossing contract surface and freeze where those contracts
  live in the kernel;
- declare one exact starter scenario family:
  - `healthy_baseline`
  - `weak_d`
- emit one deterministic engine/update loop over a frozen scenario + seed + initial
  state basis;
- emit one typed event-record posture instead of a loose string-only event log;
- emit one typed metrics family and one heuristic regime-diagnostic posture;
- freeze one starter lane-crossing contract set as typed kernel law:
  - `O -> E`
  - `E -> D`
  - `D -> O`
  - `U -> D`
- freeze deterministic agent iteration and action tie-break law;
- freeze exact archetype-share validation under starter scenario config;
- fail closed on malformed scenario/config input rather than repairing it ambiently.

This slice is kernel-first and pre-consumer. It does not authorize FastAPI routes,
browser UI, persistent storage, product routing, worker orchestration, or direct
import of the prototype tree into live package paths.

## Frozen Implementation Decisions

1. Package-ownership strategy:
   - `packages/adeu_odeu_sim` is the sole implementation owner in this slice;
   - the imported intake bundle remains shaping evidence only and may not be treated as
     the live kernel surface.
2. Starter-domain strategy:
   - the first released kernel domain is exactly:
     - one region;
     - one commons resource;
     - one institution;
     - one public archive;
     - one action per agent per turn;
   - multi-region, generalized resource families, or broader social infrastructure
     widening are forbidden in this slice.
3. Kernel-substructure strategy:
   - the first released kernel must keep the key nested simulation objects as
     first-class typed models in `models.py`;
   - that first-class set must include:
     - lane-state models:
       - `OState`
       - `EState`
       - `DState`
       - `UState`
     - `Agent`
     - `ResourcePool`
     - `Institution`
     - `Norm`
     - evidence/event carriers:
       - `Observation`
       - `EvidenceRecord`
       - `Claim`
       - `PublicReport`
       - `AuditResult`
       - `SanctionEvent`
     - `ActionTemplate`
     - `Action`
     - `ScenarioConfig`
     - `MetricPoint`
     - `WorldState`
   - the slice may not hide that ontology solely inside broad untyped
     `resource_pool`, `institution`, `norms`, `agents`, or `event_log` blobs.
4. Determinism strategy:
   - same scenario + same seed + same initial state must replay to byte-identical
     turn-by-turn world-state, metrics-history, and regime outputs;
   - the canonical replay seed is `7`;
   - the canonical replay horizon for starter fixtures is `25` steps;
   - agent iteration order must be deterministic and frozen;
   - action tie-break behavior must be deterministic and frozen;
   - unseeded randomness is not selected in this slice.
5. Scenario strategy:
   - the first released scenario family is exactly:
     - `healthy_baseline`
     - `weak_d`
   - starter scenario share allocation must validate exactly:
     - each archetype share between `0.0` and `1.0`
     - total share sum equals `1.0`
   - other prototype scenarios, including `weak_e`, `weak_e_weak_d`,
     `coercive_truth_poor_order`, and `ai_mediated_epistemics`, are explicitly later.
6. Regime strategy:
   - regime outputs are heuristic diagnostic classifications over kernel state only;
   - they are not control authority;
   - they are not optimization targets;
   - they are not semantic ground truth beyond the released kernel’s bounded
     diagnostic posture.
7. Lane-crossing strategy:
   - the starter lane-crossing contracts must be explicit typed kernel contracts, not
     comments or README-only doctrine;
   - those contracts must live in first-class `models.py` contract surfaces and be
     consumed explicitly by action templates and/or engine transition logic;
   - the frozen starter set is:
     - `O -> E` trace contract;
     - `E -> D` legitimacy contract;
     - `D -> O` allocation contract;
     - `U -> D` pressure contract.
8. Event-record strategy:
   - `V51-A` must not retain a loose string-only `event_log` as the only replay
     carrier;
   - the first released kernel must introduce a typed event-record posture instead,
     with deterministic event ordering and a frozen event-entry grammar.
9. Widening strategy:
   - no FastAPI routes here;
   - no browser UI here;
   - no persistent storage here;
   - no direct import of the prototype `api.py`, `static/`, or test tree into live
     package paths here.

## Bounded Starter Vocabularies

The first `V51-A` release should freeze bounded starter vocabularies rather than leave
the family open-ended.

The intended bounded starter vocabularies are:

- `archetype`:
  - `cooperator`
  - `opportunist`
  - `auditor`
  - `official`
  - `ai_dependent`
- `ai_mode`:
  - `none`
  - `accurate`
  - `sycophantic`
- `action_type`:
  - `contribute_to_commons`
  - `defect_or_overextract`
  - `share_claim`
  - `misreport`
  - `verify`
  - `audit_institution`
  - `sanction`
  - `appeal`
  - `invest_in_public_epistemics`
  - `invest_in_institution`
  - `do_nothing`
- `norm_modality`:
  - `obligation`
  - `prohibition`
  - `permission`
  - `role_duty`
- `deontic_status`:
  - `required`
  - `permitted`
  - `forbidden`
  - `contestable`
- `lane_crossing_contract_kind`:
  - `o_to_e_trace_contract`
  - `e_to_d_legitimacy_contract`
  - `d_to_o_allocation_contract`
  - `u_to_d_pressure_contract`
- `event_record_kind`:
  - `simulation_initialized`
  - `turn_started`
  - `planned_action`
  - `turn_completed`
  - `regime_classified`
  - `diagnostic_note`
- `regime_label`:
  - `Cooperative Legible Order`
  - `Coercive Truth-Poor Order`
  - `Epistemic Capture Collapse`
  - `Symbolic Institution Drift`
  - `Fragmented Opportunism`
  - `Contested Mixed Regime`

Out-of-scope constructs in this slice are:

- FastAPI routes;
- browser/static UI;
- persistent storage;
- multi-region or generalized ontology widening;
- learning or cultural-evolution lanes;
- worker orchestration or runtime mutation surfaces;
- product-route ownership.

## Selected Schema Anchors

The first `V51-A` release should freeze the following contract anchors.

1. `adeu_odeu_lane_delta@1`
   - `O`
   - `E`
   - `D`
   - `U`
2. lane-state submodels:
   - `adeu_odeu_o_state@1`
     - `resources`
     - `base_income`
     - `evidence_access`
     - `sanctioned_last_turn`
     - `pending_appeal`
   - `adeu_odeu_e_state@1`
     - `belief_commons`
     - `uncertainty`
     - `evidence_access`
     - `verification_capacity`
     - `epistemic_vigilance`
     - `trust_institution`
     - `trust_ai`
     - `peer_trust`
     - `last_verified_turn`
   - `adeu_odeu_d_state@1`
     - `norm_commitment`
     - `legitimacy_belief`
     - `role_duty_strength`
     - `appeal_propensity`
     - `compliance_bias`
   - `adeu_odeu_u_state@1`
     - `greed`
     - `long_term_horizon`
     - `fairness`
     - `risk_tolerance`
     - `sanction_aversion`
3. `adeu_odeu_agent@1`
   - `id`
   - `archetype`
   - `o_state`
   - `e_state`
   - `d_state`
   - `u_state`
   - `reputation`
   - `last_action`
4. `adeu_odeu_resource_pool@1`
   - `id`
   - `stock`
   - `capacity`
   - `regeneration_rate`
   - `extraction_damage`
5. `adeu_odeu_institution@1`
   - `id`
   - `name`
   - `legitimacy`
   - `operativity`
   - `enforcement_capacity`
   - `enforcement_remaining`
   - `sanction_consistency`
   - `appeal_availability`
   - `archive_capacity`
   - `public_epistemics_level`
   - `budget`
   - `capture_pressure`
6. `adeu_odeu_norm@1`
   - `id`
   - `modality`
   - `subject_scope`
   - `trigger_condition`
   - `target_action`
   - `sanction_rule`
   - `appeal_available`
   - `legitimacy_contribution`
   - `enforcement_cost`
   - `observability_dependency`
7. typed evidence/event carriers:
   - `adeu_odeu_observation@1`
   - `adeu_odeu_evidence_record@1`
   - `adeu_odeu_claim@1`
   - `adeu_odeu_public_report@1`
   - `adeu_odeu_audit_result@1`
   - `adeu_odeu_sanction_event@1`
   - each must remain first-class typed models in `models.py`, not anonymous nested
     dicts
8. `adeu_odeu_action_template@1`
   - `schema`
   - `action_type`
   - `actor_eligibility`
   - `material_cost`
   - `observability`
   - `evidence_emission`
   - `base_deontic_status`
   - `lane_impact`
9. `adeu_odeu_action@1`
   - `schema`
   - `id`
   - `turn`
   - `actor_id`
   - `action_type`
   - `targets`
   - `material_cost`
   - `observability`
   - `evidence_emission`
   - `deontic_status`
   - `lane_impact`
   - `rationale`
10. `adeu_odeu_lane_crossing_contract@1`
   - `schema`
   - `contract_kind`
   - `source_lane`
   - `target_lane`
   - `trigger_surface`
   - `effect_surface`
   - `diagnostic_posture`
11. `adeu_odeu_scenario_config@1`
   - `schema`
   - `name`
   - `description`
   - `num_agents`
   - `scarcity`
   - `regeneration_rate`
   - `misinformation`
   - `verification_capacity`
   - `enforcement_capacity`
   - `sanction_severity`
   - `initial_legitimacy`
   - `initial_operativity`
   - `sanction_consistency`
   - `archive_capacity`
   - `appeal_availability`
   - `public_epistemics_level`
   - `ai_mode`
   - `ai_reliability`
   - `cooperator_share`
   - `opportunist_share`
   - `auditor_share`
   - `official_share`
   - `ai_dependent_share`
   - `max_turns`
   - validation rule:
     - each starter share between `0.0` and `1.0`
     - starter-share total equals `1.0`
12. `adeu_odeu_metric_point@1`
   - `schema`
   - `turn`
   - `cooperation_rate`
   - `commons_health`
   - `average_belief_accuracy`
   - `epistemic_integrity`
   - `institution_legitimacy`
   - `institution_operativity`
   - `symbolic_gap`
   - `sanction_consistency`
   - `utility_concentration`
   - `trust_fragmentation`
   - `regime_label`
13. `adeu_odeu_event_record@1`
   - `schema`
   - `event_kind`
   - `turn`
   - `summary`
   - `related_ids`
14. `adeu_odeu_world_state@1`
   - `schema`
   - `seed`
   - `turn`
   - `scenario`
   - `config`
   - `resource_pool`
   - `institution`
   - `norms`
   - `agents`
   - `observations`
   - `evidence_records`
   - `claims`
   - `public_reports`
   - `audit_results`
   - `sanction_events`
   - `planned_actions`
   - `metrics_history`
   - `event_records`

## Accepted And Reject Fixtures

The first `V51-A` release should include a bounded deterministic fixture set:

Accepted fixture set:

- one `healthy_baseline` replay fixture at:
  - seed `7`
  - step horizon `25`
- one `weak_d` replay fixture at:
  - seed `7`
  - step horizon `25`
- byte-identical replay for world-state, metrics-history, and regime outputs over both
  starter scenarios.
- one deterministic tie-break / agent-order fixture proving replay does not drift when
  multiple candidate actions remain admissible.

Reject fixture set:

- malformed scenario share allocation;
- malformed enum/config input;
- malformed lane-crossing contract input;
- attempted unseeded-randomness widening.

## Required Deliverables

The first `V51-A` release should add:

- `packages/adeu_odeu_sim/pyproject.toml`
- `packages/adeu_odeu_sim/src/adeu_odeu_sim/models.py`
- `packages/adeu_odeu_sim/src/adeu_odeu_sim/actions.py`
- `packages/adeu_odeu_sim/src/adeu_odeu_sim/scenarios.py`
- `packages/adeu_odeu_sim/src/adeu_odeu_sim/regimes.py`
- `packages/adeu_odeu_sim/src/adeu_odeu_sim/metrics.py`
- `packages/adeu_odeu_sim/src/adeu_odeu_sim/engine.py`
- `packages/adeu_odeu_sim/src/adeu_odeu_sim/__init__.py`
- `packages/adeu_odeu_sim/tests/test_odeu_sim_models.py`
- `packages/adeu_odeu_sim/tests/test_odeu_sim_actions.py`
- `packages/adeu_odeu_sim/tests/test_odeu_sim_scenarios.py`
- `packages/adeu_odeu_sim/tests/test_odeu_sim_engine.py`
- committed `v51a` fixtures under `packages/adeu_odeu_sim/tests/fixtures/v51a/`

It should not add:

- `apps/api` route consumers
- `apps/web` route consumers
- persistent-storage surfaces
- direct imports of the prototype `api.py`, `static/`, or prototype tests

## Acceptance

Accept this slice when:

- the repo-owned `adeu_odeu_sim` package is the only live owner of the shipped
  `V51-A` code;
- the same scenario + same seed + same initial state replays to byte-identical
  world-state, metrics-history, and regime outputs;
- the committed `healthy_baseline` and `weak_d` fixtures match deterministic replay at
  seed `7` and horizon `25`;
- the key nested simulation objects remain first-class validated models rather than
  being hidden only inside one broad `world_state` payload;
- lane-crossing contracts are explicit in live typed kernel code rather than only in
  comments or support docs;
- those lane-crossing contracts live in explicit typed contract surfaces, not only in
  free-form engine comments;
- typed event records replace loose string-only logs as the replay-visible event
  carrier;
- deterministic agent iteration and action tie-break behavior are frozen and tested;
- starter scenario share allocation validates exactly under the locked rule;
- regime outputs remain bounded heuristic diagnostics rather than control authority,
  optimization targets, or semantic ground truth claims;
- malformed scenario/config input fails closed;
- no FastAPI, browser UI, persistent storage, or prototype-tree import ships in the
  same slice.

Do not accept this slice if:

- deterministic replay changes with the same scenario/seed basis;
- starter scenarios drift from `healthy_baseline` / `weak_d` without an updated lock;
- nested ontology is collapsed back into loose `world_state` blobs or string-only logs;
- lane-crossing contracts remain ambient/prose-only instead of typed;
- regime outputs become normative or control-bearing claims;
- the kernel slice quietly widens into app/API/UI ownership.

## Local Gate

Before opening or updating the implementation PR for this slice, the local gate should
be:

- `make check`

If narrower local validation is used during bounded implementation, it must be stated
explicitly in the PR notes, but the default repo-native gate for the Python lane
remains `make check`.
