# Architecture ADEU Hierarchical Obligation Broker Family v0

Status: architecture / decomposition note for planned `HOB-0`.

Authority layer: architecture / decomposition.

This note does not authorize ontology generation, semantic adjudication,
obligation traversal runtime, probe execution, command execution, code edits,
worker dispatch, implementation authority, product authority, graph-memory
authority, recursive policy amendment, PR creation, commit, merge, release, or
future-family selection by itself. It defines the intended family boundary so
starter locks can select bounded implementation slices.

## Family Thesis

`HOB-0` should make the traversal consequences of semantic adjudication
deterministic.

The model remains responsible for bounded semantic judgment:

```text
parent class applies / does not apply
child is active / irrelevant / pass-through / deferred / blocked
warrant for the judgment
```

The broker is responsible for deterministic traversal:

```text
selected parent -> inherited children
inherited children -> required status rows
status rows -> closure/readiness validity
open rows -> next descent frontier
closed or scoped rows -> batch/handoff posture
```

Controlling invariant:

```text
Selected parent classes import child obligations.
Child obligations persist until covered, probe-matrix locked, proved
irrelevant, proved pass-through, conflict-isolated, blocked, or explicitly
deferred with expected risk.
```

## Source Stack Consumed

`HOB-0` consumes:

- semantic declaration / canonical lookup planning substrate, especially the
  distinction that lookup is not obligation expansion;
- v16 support doctrine on operationalization robustness;
- v17 support doctrine on deterministic hierarchical obligation inheritance;
- semantic compiler architecture doctrine on deterministic semantic blocks,
  stable IDs, canonical hashes, and fail-closed validation.

No consumed source becomes implementation authority, semantic truth authority,
runtime authority, product authority, or future-family selection by being
consumed.

## Family Slices

### `HOB-0-A`: Catalog, Activation, And Inherited Ledger

Starter surfaces:

- `repo_hierarchical_obligation_catalog@1`
- `repo_obligation_activation_assessment@1`
- `repo_inherited_obligation_ledger@1`
- `repo_obligation_traversal_validation_report@1`
- `repo_obligation_broker_non_authority_guardrail@1`

Purpose:

- make the numbered ontology catalog row-shaped and deterministic;
- record model-authored activation/adjudication rows without treating the tool
  as semantic judge;
- expand activated parent nodes into inherited child obligations;
- validate that every inherited child has a status row or an explicit blocker;
- reject parent closure and readiness promotion when inherited child obligations
  remain missing, open, or invalid;
- emit validation diagnostics, deterministic next-frontier rows, and
  non-authority guardrails.

Slice boundary:

```text
HOB-0-A validates row admissibility and emits blockers/frontiers.
HOB-0-B computes full subtree closure/readiness summaries.
```

Forbidden:

- probe-matrix generation;
- full subtree closure aggregation;
- implementation batch contracts;
- worker taskpacks;
- code edits;
- command execution;
- product claims;
- semantic adjudication by the tool;
- future-family selection.

### `HOB-0-B`: Closure, Frontier, And Operationalization Planning

Later surfaces:

- `repo_obligation_closure_report@1`
- `repo_obligation_next_frontier_report@1`
- `repo_obligation_probe_matrix_plan@1`
- `repo_obligation_implementation_batch_contract@1`
- `repo_obligation_operationalization_report@1`

Purpose:

- compute subtree closure posture from inherited obligation ledgers;
- emit the next deterministic descent frontier;
- compile closed or near-closed terminal nodes into probe-matrix planning rows;
- shape bounded implementation batches from selected subtrees;
- distinguish representative examples from matrix-locked or gold-ready
  subtrees;
- invalidate stale local ledgers when new inherited obligations are introduced.

Forbidden:

- executing probes;
- running reference or candidate programs;
- patching code;
- dispatching workers;
- treating a probe matrix plan as observed evidence;
- granting implementation authority by itself.

### `HOB-0-C`: Delta Attribution, Integration Handoff, And Closeout

Later surfaces:

- `repo_obligation_delta_attribution_ledger@1`
- `repo_obligation_stale_ledger_invalidation_report@1`
- `repo_obligation_broker_integration_handoff@1`
- `repo_obligation_broker_family_closeout_alignment@1`

Purpose:

- attribute local, official-like, or official pressure to numbered ontology
  nodes when supplied with admissible attribution rows;
- distinguish macro-closure success from representative-transfer success;
- record regressions and rows that moved to different failure classes;
- provide pressure-only handoffs to future probe execution, implementation,
  semantic compiler integration, or domain-specific adapters;
- close only the broker family.

Forbidden:

- claiming score truth;
- treating official failures as clean first-pass evidence;
- authorizing implementation, execution, or product state changes;
- selecting future families.

## Core Data Concepts

### Catalog Node

A catalog node is stable and numbered:

```yaml
catalog_id: "program_odeu_v17"
catalog_version: "0.1.0"
catalog_hash: "sha256:..."
catalog_authority: support | architecture | lock
node_id: "5.2.4.3"
node_label: "Resource reference binding in join/subquery contexts"
parent_id: "5.2.4"
node_kind: class | macro | branch | terminal_leaf
child_ids: []
default_inheritance: inherited_required | optional_observed | not_inherited
allowed_statuses: []
allowed_irrelevance_proof_types: []
closure_policy_ref: string
```

The family should use one shared vocabulary source across A/B/C for:

```text
activation_status
inheritance_status
obligation_status
readiness_status
proof_kind
proof_type
frontier_reason
authority_posture
closure_status
```

The implementation should export this vocabulary into JSON schema and avoid
slice-local string drift.

### Activation Assessment

The model supplies activation judgment:

```yaml
catalog_id: "program_odeu_v17"
catalog_version: "0.1.0"
catalog_hash: "sha256:..."
node_id: "5"
activation_status: applies | not_applicable_proven | candidate_pending | conflict_isolated
warrant_authority: visible_spec | public_help | public_reference_probe |
  implementation_observation | post_eval_pressure | methodological_equivalence |
  support_doctrine | none
warrant_text: string
evidence_refs: []
```

The broker validates the row shape and vocabulary. It does not decide the
semantic truth of the row.

### Inherited Obligation Row

The broker expands selected parents:

```yaml
catalog_id: "program_odeu_v17"
catalog_version: "0.1.0"
catalog_hash: "sha256:..."
node_id: "5.2.4.3"
inherited_from: "5"
inheritance_status: root_selected | inherited_required | locally_triggered |
  optional_observed | not_inherited
obligation_status: open | covered_terminalized | covered_by_probe_matrix |
  proved_pass_through | proved_irrelevant | scoped_deferred_with_expected_risk |
  gold_deferred_with_expected_risk | blocked_pending_observation |
  blocked_pending_equivalence | conflict_isolated
warrant_ref: string
expected_risk_if_deferred: string
probe_refs: []
implementation_owner: parser | router | binder | transformer | renderer |
  diagnostics | runtime | harness | none | unknown
```

Every inherited ledger binds to exactly one catalog id, version, hash, and
authority posture. A ledger from an earlier catalog version is stale unless a
later validation row explicitly proves compatibility.

## Proof Object Shapes

Proof-sensitive statuses require structured proof rows as a discriminated
union. Prose alone is not enough.

Common proof row fields:

```yaml
proof_ref: "PROOF-..."
proof_kind: irrelevance | pass_through | deferral | blocking
proof_type: string
protected_surfaces:
  stdout: true
  stderr: true
  exit: true
  files: true
  state: true
  row_universe: true
  aggregation_denominator: true
warrant_ref: string
proof_text: string
evidence_refs: []
```

### Irrelevance Proof

```yaml
irrelevance_proof:
  node_id: "5.2.4.3"
  proof_type:
    semantic_impossibility |
    public_schema_absence |
    negative_reference_behavior
  protected_surfaces:
    stdout: true
    stderr: true
    exit: true
    files: true
    state: true
    row_universe: true
    aggregation_denominator: true
  warrant_ref: string
  proof_text: string
  evidence_refs: []
```

### Pass-Through Proof

```yaml
pass_through_proof:
  node_id: "5.2.4.3"
  pass_through_scope: string
  protected_surfaces:
    stdout: true
    stderr: true
    exit: true
    files: true
    state: true
    row_universe: true
    aggregation_denominator: true
  warrant_ref: string
  proof_text: string
  evidence_refs: []
```

### Deferral Proof

```yaml
deferral_proof:
  node_id: "5.2.4.3"
  deferral_kind:
    scoped_deferred_with_expected_risk |
    gold_deferred_with_expected_risk
  expected_risk: string
  handoff_effect: scoped_ok | blocks_gold | blocks_implementation
  warrant_ref: string
  proof_text: string
```

### Blocking Proof

```yaml
blocking_proof:
  node_id: "5.2.4.3"
  blocker_kind:
    blocked_pending_observation |
    blocked_pending_equivalence
  required_next_evidence: string
  affected_surfaces:
    stdout: true
    stderr: true
    exit: true
    files: true
    state: true
    row_universe: true
    aggregation_denominator: true
  warrant_ref: string
```

`proved_irrelevant`, `proved_pass_through`, scoped/gold deferrals, and blocked
statuses are invalid without the matching proof object.

## Deterministic Validation Rules

The broker must fail closed when:

- a selected node is absent from the catalog;
- a ledger, activation row, or validation report omits catalog id, version,
  hash, or authority posture;
- a catalog node has duplicate or ambiguous child IDs;
- a selected parent has child nodes missing from the inherited ledger;
- a required child has no obligation status;
- a child is omitted without allowed proof;
- a scoped deferral is used as irrelevance proof;
- a proof-sensitive status lacks its required structured proof object;
- a parent closure claim has open, missing, blocked, representative-only, or
  invalid children;
- a gold-ready claim contains scoped deferrals or blocked children;
- `not_inherited` is used when the catalog default and parent activation do not
  allow it, unless an explicit proof places the child outside the active
  subtree;
- `optional_observed` is used to close a parent without local triggering or
  explicit promotion;
- an implementation batch references nodes outside its selected subtree;
- a stale local ledger is reused after new inherited nodes are introduced;
- unknown vocabulary appears in status, proof, readiness, or handoff fields.

## Next-Frontier Semantics

The broker emits deterministic next-frontier rows:

```yaml
frontier_row:
  node_id: "5.2.4.3"
  reason:
    inherited_required_missing_status |
    active_branch_needs_terminalization |
    irrelevance_proof_invalid |
    pass_through_proof_incomplete |
    blocked_pending_reference_observation |
    blocked_pending_methodological_equivalence |
    probe_matrix_required |
    parent_closure_blocked_by_child
  required_next_action:
    semantic_adjudication |
    terminalization |
    proof_repair |
    reference_observation |
    methodological_equivalence_check |
    probe_matrix_planning |
    deferral_risk_statement
```

These rows are the primary broker output. They tell the model where to descend
next without granting implementation authority.

## Readiness Posture

Supported readiness levels:

```text
not_ready
representative_examples_only
branch_matrix_partial
scoped_ready
gold_ready
blocked
```

Parent readiness must be no stronger than the weakest required child readiness.

Closure reports in `HOB-0-B` should include a closure basis, such as:

```text
all_children_gold_ready
all_children_scoped_ready
representative_only
blocked_by_child
blocked_by_A_validation
deferred_with_risk
```

## Package Boundary

Recommended package:

```text
packages/adeu_obligation_broker
```

Initial module shape:

```text
src/adeu_obligation_broker/models.py
src/adeu_obligation_broker/catalog.py
src/adeu_obligation_broker/activation.py
src/adeu_obligation_broker/inheritance.py
src/adeu_obligation_broker/closure.py
src/adeu_obligation_broker/frontier.py
src/adeu_obligation_broker/diagnostics.py
src/adeu_obligation_broker/export_schema.py
```

The package should remain deterministic:

- no network;
- no provider calls;
- no command execution;
- no wall-clock dependence;
- lexicographic ordering;
- canonical JSON hashes;
- `extra="forbid"` schemas;
- unknown vocabulary fails closed.

## Integration Boundary

`HOB-0` can later be consumed by:

- semantic compiler artifacts;
- ProgramBench reconstruction loops;
- UX decomposition flows;
- architecture review flows;
- resident-agent handoff flows.

This family does not select those integrations. It only creates the broker
substrate that later families can consume.

## Bottom Line

`HOB-0` makes a narrow institutional move:

```text
Model supplies semantic judgment.
Broker enforces deterministic traversal consequences.
```

That is the missing layer between semantic declaration and reliable
implementation planning.
