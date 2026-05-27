# ProgramBench HOB Guard Phase-Transition Schema v0

Authority layer: support / proposed high-level guard schema.

Purpose: define a separate high-level schema for the HOB guard that governs
phase transitions in ProgramBench reconstruction runs. This is not a product
ontology, not an implementation plan, and not a replacement for
`adeu_obligation_broker` A/B/C records. It is the orchestrator-side contract
that says whether a transition between reconstruction phases is legal.

This draft incorporates the v21 anti-replay lesson and the v22 orchestrator
phase-transition lesson:

```text
HOB A/B/C records prove local obligation structure.
The HOB guard proves that the run is allowed to move from one phase to the next.
```

## 1. Core Role

The guard answers:

```text
May this run move from phase Phi_i to phase Phi_j with the artifacts currently
available, under the declared run posture?
```

It must not answer:

```text
What is the program behavior?
What should the worker implement?
Are official failures product truth?
Which future family should be selected?
```

## 2. Phase Vocabulary

```yaml
phase_id:
  enum:
    - P0_intake
    - P1_visible_spec_base_ontology
    - P2_top_level_hob_activation
    - P3_inherited_child_obligation_fill
    - P4_orthogonal_semantic_pool_descent
    - P5_pool_reconciliation_to_hob
    - P6_public_schema_scout_observation
    - P7_public_schema_reentry_tree_repair
    - P8_probe_matrix_compilation
    - P9_reference_observation_lock
    - P10_operationalization_equivalence_check
    - P11_implementation_handoff_contract
    - P12_implementation_worker_execution
    - P13_packaged_witness_target_substrate_parity
    - P14_local_candidate_gate
    - P15_anti_replay_sealed_metamorphic_gate
    - P16_regression_conservation_gate
    - P17_official_eval_experiment_or_gold_attempt
    - P18_post_eval_layer_transition_audit
    - P19_meta_program_amendment_frontier
```

## 3. Run Posture Vocabulary

```yaml
run_posture:
  enum:
    - clean_first_pass
    - scoped_experiment
    - scoped_repair
    - gold_attempt
    - method_test
    - post_eval_repair
    - source_postmortem
```

The guard must fail closed if a transition silently upgrades posture, for
example:

```text
scoped_experiment -> gold_attempt
```

without an explicit promotion gate.

## 4. Record: hob_guard_run_state@1

```yaml
schema: hob_guard_run_state@1
run_id: string
task_id: string
meta_program_version_ref: string
hob_catalog_id: string
hob_catalog_version: string
hob_catalog_hash: string
current_phase: phase_id
run_posture: run_posture
phase_state_hash: string | null

active_hob_node_refs:
  - string

completed_phase_refs:
  - phase_id

blocked_phase_refs:
  - phase_id

allowed_next_phase_refs:
  - phase_id

required_gate_refs:
  - string

artifact_partition_ref: string | null
latest_transition_ref: string | null

authority_posture:
  semantic_judgment_authority_granted: false
  implementation_authority_granted: false
  official_eval_authority_granted: false
  product_truth_authority_granted: false
```

Validation rules:

```text
current_phase must be one known phase.
allowed_next_phase_refs must be explicit; empty means blocked.
hob catalog identity must be hash-bound.
authority_posture booleans default false and cannot be inferred from phase name.
```

## 5. Record: hob_guard_transition_ledger@1

```yaml
schema: hob_guard_transition_ledger@1
transition_id: string
run_id: string
from_phase: phase_id
to_phase: phase_id
transition_kind:
  enum:
    - normal
    - reentry
    - repair_loop
    - downgrade
    - blocked
    - aborted

run_posture_before: run_posture
run_posture_after: run_posture

input_artifact_refs:
  - artifact_ref: string
    artifact_role: string
    artifact_hash: string
    authority_layer:
      enum: [visible_spec, public_observation, local_probe, checker_only, official_eval_pressure, source_postmortem, support]
    partition:
      enum: [implementation_visible, checker_only, orchestrator_only]

precondition_rows:
  - precondition_ref: string
    status:
      enum: [pass, fail, not_applicable, deferred_with_expected_risk]
    warrant_ref: string | null
    blocker_ref: string | null

failed_precondition_refs:
  - string

transition_decision:
  enum:
    - allowed
    - blocked
    - allowed_as_scoped_experiment
    - allowed_as_method_test
    - requires_reentry

next_required_action: string
transition_hash: string | null
```

Validation rules:

```text
No transition may be recorded as allowed while any required precondition is fail.
Deferred preconditions cannot allow gold_attempt unless the gate explicitly permits it.
P17 official eval requires P13, P14, P15, and P16 gate rows or an explicit method_test downgrade.
Reentry transitions must name the discovered larger statement or invalidated artifact.
```

## 6. Record: hob_guard_artifact_partition@1

```yaml
schema: hob_guard_artifact_partition@1
partition_id: string
run_id: string
phase_ref: phase_id

implementation_visible_refs:
  - artifact_ref: string
    allowed_visibility_reason:
      enum:
        - public_example
        - rule_description
        - representative_regression_example
        - implementation_contract

checker_only_refs:
  - artifact_ref: string
    checker_only_reason:
      enum:
        - exact_expected_bytes
        - sealed_argv_shape
        - sealed_fixture_bytes
        - metamorphic_seed
        - oracle_code
        - post_implementation_probe

orchestrator_only_refs:
  - artifact_ref: string
    orchestrator_only_reason:
      enum:
        - transition_ledger
        - contamination_audit
        - full_score_attribution
        - eval_pressure_summary

leakage_rows:
  - artifact_ref: string
    leaked_to_partition:
      enum: [implementation_visible, checker_only, orchestrator_only]
    expected_partition:
      enum: [implementation_visible, checker_only, orchestrator_only]
    leak_effect:
      enum:
        - harmless
        - regression_only
        - replay_risk
        - invalidates_heldout
        - blocks_transition
```

Validation rules:

```text
Checker-only artifacts cannot appear in the implementation-visible partition.
If exact heldout commands or bytes leak to implementation, their evidence role
is downgraded to regression_sentinel.
Any leak_effect = blocks_transition blocks P11 -> P12 and P14 -> P17.
```

## 7. Record: hob_guard_worker_baton@1

```yaml
schema: hob_guard_worker_baton@1
baton_id: string
run_id: string
phase_ref: phase_id
handoff_type:
  enum: [scoped_experiment, scoped_repair, gold_attempt, method_test]

target_node_refs:
  - string

allowed_input_refs:
  - string

forbidden_input_classes:
  - enum:
      - checker_only_exact_bytes
      - sealed_probe_manifest
      - official_eval_hidden_rows
      - source_repo
      - prior_post_eval_failure_groups
      - post_implementation_metamorphic_seeds

implementation_owner_refs:
  - string

forbidden_strategy_rows:
  - strategy:
      enum:
        - exact_argv_dispatch
        - fixture_signature_dispatch
        - embedded_oracle_bytes
        - finite_manifest_lookup
        - rc127_valid_domain_fallback
    applies: true

success_criteria_refs:
  - string

required_return_artifacts:
  - node_delta_report
  - changed_files
  - local_probe_result
  - regression_report
  - open_sibling_report
```

Validation rules:

```text
Every P12 implementation dispatch requires a baton.
The baton must cite the active transition ledger row.
The baton must not include checker-only artifacts.
The baton must name mechanism owners for every open-domain target family.
```

## 8. Record: hob_guard_anti_replay_gate@1

```yaml
schema: hob_guard_anti_replay_gate@1
gate_id: string
run_id: string
candidate_ref: string
package_ref: string

domain_cardinality_rows:
  - behavior_family_ref: string
    domain_type:
      enum:
        - finite_enumerated
        - bounded_but_parametric
        - open_grammar
        - open_resource_domain
        - open_data_value_domain
        - open_language_substrate
    finite_lookup_allowed: boolean
    required_generalization_mode:
      enum:
        - parser_rule
        - resource_rule
        - transform_rule
        - renderer_rule
        - diagnostic_rule
        - method_composition_rule

mechanism_posture_rows:
  - behavior_family_ref: string
    static_replay_risk:
      enum: [none, suspicious, confirmed]
    behavioral_replay_risk:
      enum: [none, suspicious, confirmed]
    observed_owner_refs:
      - string
    generalization_status:
      enum:
        - generalizes_behavior_family
        - representative_only
        - probe_replay_witness
        - blocked_uncertain

sealed_probe_rows:
  - probe_family_ref: string
    hidden_from_implementation: true
    generated_after_candidate_seal: true
    surfaces_checked:
      - stdout
      - stderr
      - exit
      - files
      - side_effects
    pass_required_for_handoff: boolean

fallback_surface_rows:
  - fallback_ref: string
    rc127_for_valid_branch_detected: boolean
    valid_domain_rejected_by_fallback:
      - string

anti_replay_status:
  enum:
    - passed
    - failed_probe_replay_witness
    - failed_checker_only_leak
    - failed_missing_sealed_probe
    - blocked_uncertain
```

Validation rules:

```text
Open-domain families cannot pass with finite_lookup_allowed = true.
Any mechanism_posture generalization_status = probe_replay_witness fails the gate.
Any rc127_for_valid_branch_detected = true fails the gate unless the run is downgraded to method_test.
P17 as gold_attempt is blocked unless anti_replay_status = passed.
```

## 9. Minimal Transition Rules

```text
P8 -> P9 requires:
  probe matrix rows have node refs and implementation/checker visibility labels.

P9 -> P10 requires:
  reference observations are split by stdout, stderr, exit, files, and side effects.

P10 -> P11 requires:
  operationalization equivalence proves worker task preserves HOB/audit nodes.

P11 -> P12 requires:
  worker baton exists and artifact partition has no checker-only leaks.

P12 -> P13 requires:
  candidate artifact sealed.

P13 -> P14 requires:
  packaged candidate compiles/runs under target substrate.

P14 -> P15 requires:
  local candidate gate passed at declared scope.

P15 -> P16 requires:
  anti-replay gate passed or run posture downgraded.

P16 -> P17 requires:
  regression conservation passed and transition ledger authorizes official eval.
```

## 10. Immediate ProgramBench Usage

For the next `trdsql` retry, the orchestrator should produce these rows before
implementation:

```text
hob_guard_run_state@1
hob_guard_artifact_partition@1
hob_guard_transition_ledger@1 for P10 -> P11
hob_guard_worker_baton@1 for P12
```

After implementation, before official eval:

```text
hob_guard_transition_ledger@1 for P12 -> P13
hob_guard_transition_ledger@1 for P13 -> P14
hob_guard_transition_ledger@1 for P14 -> P15
hob_guard_anti_replay_gate@1
hob_guard_transition_ledger@1 for P16 -> P17
```

If any of these records are missing, official eval may still be run as a
`method_test`, but its result must be labeled method pressure rather than
product reconstruction evidence.

