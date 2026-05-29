# ProgramBench HOB Application Protocol v6

Authority layer: support.

This note is a support-layer overlay on
`docs/support/programbench_hob_application_protocol_v5.md`. It incorporates the
post-review hardening from
`.codex/review-shell/chatgpt-downloads/updated_mp_gpo_hob_v47_v18_review.md`.

## Controlling Artifacts

```text
base protocol:
  docs/support/programbench_hob_application_protocol_v0.md

prior dense-catalog protocol:
  docs/support/programbench_hob_application_protocol_v5.md

hardened dense-catalog GPO and meta-program:
  docs/support/general_program_ontology_derived_v1_9.md
  docs/support/principled_recursive_odeu_meta_program_experimental_v48.md

hardened HOB catalog:
  docs/support/programbench_hob_obligation_catalog_v1_1.json
```

## V1.1 Catalog Identity

Use this catalog when the dense-catalog route is active:

```json
{
  "catalog_id": "programbench-odeu-meta-program-obligations",
  "catalog_version": "programbench-hob-v1.1",
  "canonical_catalog_hash": "sha256:a7013a4b34255c78999c8bbfb8e0cd9a2d97da5c462c3c8f06be1e1a74a963d1",
  "raw_file_sha256": "5398162f7bb3dbfd920d6af3a989b8d14f626735caaf09b361febacc835d718e",
  "path": "docs/support/programbench_hob_obligation_catalog_v1_1.json"
}
```

`catalog_hash` inside the JSON catalog is the HOB canonical payload hash used by
the broker and stale-ledger checks. It is not raw file SHA. Raw file SHA is
recorded here only as an optional file-integrity aid.

## V6 Hardening Summary

V5 made dense-catalog saturation first-class. V6 hardens it by:

```text
splitting generic dense catalogs from static-analyzer overlays;
adding root activation semantics;
adding catalog cardinality/extensibility posture;
requiring exact status-table and subprogram rows;
requiring public-matrix adequacy before source-tail escalation;
distinguishing BRL-compatible manifests from executed BRL certificates.
```

## Root Activation Semantics

Root families in the HOB catalog are not automatically active for every task.

Required root activation row:

```yaml
root_activation:
  root_node_ref: string
  activation_status:
    applies |
    not_applicable_with_proof |
    candidate_pending_scout |
    candidate_pending_reciprocal_diff
  warrant_refs: []
  proof_or_deferral_ref: string | null
```

Interpretation:

```text
if root applies:
  children inherit according to the catalog.

if root is not_applicable_with_proof:
  children do not activate.

if root is candidate_pending_*:
  implementation handoff is blocked for that root's possible children unless
  the intended posture explicitly carries scoped risk.
```

This is a protocol rule because the released HOB catalog schema stores only
node inheritance metadata, not activation triggers or conditional inheritance.

## Generic Dense Catalog vs Analyzer Overlay

Node `13` is generic:

```text
13 Dense finite catalog saturation
```

It covers catalog ledger, cardinality, activation, entry-as-subprogram,
status-table completeness, source-tail adequacy, source-tail authorization, and
BRL/preservation economics.

Node `14` is conditional:

```text
14 Configurable static analyzer dense catalog overlay
```

It activates only when the program reports findings over source/input files or
has analyzer-like rule behavior. Command catalogs, renderer catalogs, plugin
registries, and open extension systems do not inherit `14` unless analyzer-like
row emissions are present.

## Catalog Child Status Table

Required before dense-catalog implementation handoff:

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

Blocking failures:

```text
dense_catalog_parent_without_child_status_table
catalog_parent_gold_with_representative_children
unknown_catalog_cardinality_gold_claim
open_extensible_catalog_exhaustive_child_import_claim
```

## Catalog Entry Subprogram Row

Required for every behavior-bearing entry unless proved shallow:

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

Blocking failure:

```text
catalog_entry_treated_as_string_without_shallow_proof
```

## Catalog Saturation Transition Acceptance

Before implementation handoff or official-readiness posture:

```yaml
catalog_saturation_transition:
  transition_ref: string
  catalog_refs: []
  child_import_status:
    complete |
    representative |
    source_tail_required |
    scoped_deferred |
    blocked
  unresolved_child_count: int
  catalog_cardinality_posture: string
  score_ceiling_if_scoped: known | unknown | not_applicable
  intended_posture:
    method_test |
    scoped_catalog_repair |
    gold_catalog_attempt |
    source_tail_catalog_closure
  gold_posture_allowed: bool
  blocker_refs: []
```

Rule:

```text
OTB legality is not catalog saturation. A transition can be structurally legal
while still forbidden from claiming gold readiness.
```

## Public Matrix Adequacy Before Source-Tail

Required before source-tail authorization:

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
Low yield from poor probes is not saturation.
```

## BRL Compatibility Status

Dense-catalog handoffs must distinguish planned preservation from executed
no-regression certification:

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

Rule:

```text
A named preservation sentinel is not an executed replay lock unless the BRL
status says so.
```

## Worker Handoff Additions

Dense-catalog worker batons must include:

```text
root activation rows for nodes 13 and 14;
catalog cardinality posture;
catalog child status table;
entry subprogram rows for in-scope entries;
public matrix adequacy row;
source-tail authorization row if used;
BRL compatibility status for touched owners;
explicit scoped/gold/source-tail posture.
```

Forbidden baton:

```text
fix missing rules
make catalog complete
make formatter exact
```

Allowed baton:

```text
close these numbered catalog children, under this cardinality and readiness
posture, through these owners, while preserving these BRL-status sentinels.
```
