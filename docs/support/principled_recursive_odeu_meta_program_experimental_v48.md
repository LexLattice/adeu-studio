# Principled Recursive ODEU Meta-Program Experimental v48

Authority layer: support / experimental meta-program revision.

This v48 patch extends:

```text
docs/support/principled_recursive_odeu_meta_program_experimental_v47.md
docs/support/general_program_ontology_derived_v1_9.md
docs/support/programbench_hob_obligation_catalog_v1_1.json
.codex/review-shell/chatgpt-downloads/updated_mp_gpo_hob_v47_v18_review.md
```

Core update:

```text
Make dense-catalog handling executable as transition contracts, not only as
good prose. Split generic dense-catalog obligations from static-analyzer
overlays. Require cardinality/extensibility posture, child status tables,
public-matrix adequacy before source-tail escalation, and BRL compatibility
status before promotion.
```

## 1. Dense-Catalog Transition Contract Shape

Every dense-catalog gate should be emitted as an OTB-compatible transition
contract row:

```yaml
dense_catalog_transition_contract:
  transition_ref: string
  gate_ref: string
  consumes:
    - task_native_ontology_ref
    - gpo_projection_ref
    - public_catalog_ledger_ref
    - child_status_table_ref
  forbidden_inputs:
    - official_failures_as_clean_evidence
    - source_tail_facts_before_authorization
    - representative_examples_as_gold_closure
  required_outputs: []
  blocking_conditions: []
  allowed_next_phases: []
  forbidden_promotions: []
```

Rule:

```text
A gate name alone is not a handoff. The transition contract must state what it
consumed, what it produced, what remains blocked, and which next phases are
legal.
```

## 2. `CATALOG_CARDINALITY_AND_EXTENSIBILITY_GATE`

Trigger:

```text
A catalog-like parent is active or candidate-active.
```

Required output:

```yaml
catalog_cardinality:
  catalog_ref: string
  posture:
    closed_finite_public |
    closed_finite_reference_observed |
    closed_finite_source_tail_required |
    mixed_builtin_closed_extension_open |
    open_extensible |
    unknown_pending_scout
  closure_consequence:
    exhaustive_child_import_required |
    observed_child_import_with_gap_ledger |
    source_tail_or_deferral_required |
    builtin_import_plus_extension_interface_closure |
    registry_interface_closure_required |
    scout_or_deferral_required
  blocker_refs: []
```

Blocking rule:

```text
No catalog parent can reach gold posture while cardinality is unknown.
Open/extensible catalogs close through registry/interface semantics, not by
pretending future entries have been exhaustively imported.
```

## 3. `CATALOG_STATUS_TABLE_COMPLETENESS_GATE`

Required row:

```yaml
catalog_child_status_table:
  catalog_ref: string
  catalog_hash: string
  entry_universe_status:
    closed_public |
    closed_reference_observed |
    closed_source_tail |
    mixed_builtin_closed_extension_open |
    open_extensible |
    unknown
  canonical_entry_refs: []
  alias_map_refs: []
  child_rows:
    - entry_ref: string
      canonical_name: string
      aliases: []
      activation_sets: []
      status:
        matrix_closed |
        representative_only |
        source_tail_required |
        proved_shallow |
        proved_irrelevant |
        deferred_with_risk |
        blocked_pending_observation |
        blocked_pending_equivalence
      evidence_posture:
        visible_spec |
        semantic_inference |
        public_scout |
        reference_observation |
        source_tail |
        target_substrate_probe
      behavior_owner: string
      implementation_owner: string
      preservation_sentinels: []
      deferral_or_source_tail_reason: string | null
  total_known_count: int
  total_status_count: int
  all_known_children_accounted_for: bool
```

Blocking rule:

```text
Gold posture requires all known children accounted for and no representative_only
or unknown child unless the run explicitly carries scoped posture or deferral.
```

## 4. `CATALOG_ENTRY_SUBPROGRAM_GATE_V2`

Required row:

```yaml
catalog_entry_subprogram:
  entry_ref: string
  shallow_status:
    proved_shallow |
    subprogram_required |
    unknown
  argument_schema_ref: string | null
  trigger_positive_matrix_ref: string | null
  safe_negative_matrix_ref: string | null
  required_context_refs: []
  row_or_side_effect_law_ref: string | null
  diagnostic_law_ref: string | null
  projection_refs: []
  suppression_or_filter_refs: []
  closure_status:
    open |
    matrix_partial |
    matrix_closed |
    source_tail_equivalent |
    deferred
```

Blocking rule:

```text
Name acceptance cannot close an entry with shallow_status unknown or
subprogram_required.
```

## 5. `PUBLIC_MATRIX_ADEQUACY_BEFORE_SOURCE_TAIL_GATE`

Required row:

```yaml
public_matrix_adequacy:
  catalog_ref: string
  branch_matrix_complete: bool
  salience_gate_run: bool
  descent_completeness_gate_run: bool
  representative_only_gaps_named: bool
  unresolved_axes: []
  low_yield_pass_refs: []
  low_yield_interpretable_as_saturation: bool
  adequacy_status:
    adequate |
    inadequate |
    impossible_to_make_adequate_with_public_evidence
```

Blocking rule:

```text
Source-tail escalation is blocked when low yield came from inadequate public
matrix work rather than from saturation of an adequate public/blind method.
```

## 6. `CATALOG_SOURCE_TAIL_AUTHORIZATION_GATE_V2`

Required row:

```yaml
catalog_source_tail_authorization:
  catalog_ref: string
  public_matrix_adequacy_ref: string
  remaining_child_refs: []
  exact_predicate_owner:
    source |
    host_library |
    fixture_corpus |
    target_substrate |
    mixed
  prior_gates_preserved: []
  authorization:
    blocked |
    source_tail_authorized |
    fixture_corpus_authorized |
    host_library_authorized |
    target_substrate_required
  allowed_scope: []
  forbidden_use:
    - clean_first_pass_evidence
    - unbounded_source_import
    - hidden_fact_laundering
  non_laundering_statement: string
```

## 7. `BRL_COMPATIBILITY_STATUS_GATE`

Dense-catalog protocols may reference BRL before every run has a full BRL
certificate. The status must be explicit.

Required row:

```yaml
brl_compatibility_status:
  owner_surface: string
  preservation_manifest_ref: string | null
  brl_status:
    planned_manifest_only |
    manifest_validated |
    replay_executed |
    no_regression_certified |
    blocked_brl_unavailable
  preserved_leaf_refs: []
  promotion_allowed: bool
```

Blocking rule:

```text
A named preservation sentinel is not an executed no-regression certificate
unless `brl_status` says so.
```

## 8. Root Activation Policy

HOB child inheritance remains deterministic after activation, but root families
must be semantically adjudicated first.

Required root activation row:

```yaml
root_activation_policy:
  root_node_ref: string
  activation_status:
    applies |
    not_applicable_with_proof |
    candidate_pending_scout |
    candidate_pending_reciprocal_diff
  warrant_refs: []
  irrelevance_or_deferral_ref: string | null
```

Rule:

```text
The catalog JSON may use `inherited_required` as the default inheritance value,
but the orchestrator must interpret this as child inheritance after parent
activation, not as automatic activation of every root family for every task.
```

## 9. Dense-Catalog Official Postures

Allowed postures:

```text
method_test:
  may proceed with representative catalog rows, but cannot claim gold.

scoped_catalog_repair:
  may repair named children if unresolved siblings and score risk are explicit.

gold_catalog_attempt:
  requires child status table completeness, cardinality posture, adequate
  public matrix or authorized source-tail, and BRL status for touched owners.

source_tail_catalog_closure:
  requires source-tail authorization and witness separation.
```

## 10. HOB/OTB/BRL Split

```text
HOB:
  imports active catalog child obligations and detects missing rows.

OTB:
  validates whether the transition from catalog theory to implementation or
  official eval is legal for the intended posture.

BRL:
  preserves green sibling leaves when shared implementation owners are touched.
```

No one layer replaces the others.
