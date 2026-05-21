# ProgramBench HOB Application Protocol v0

Authority layer: support.

This note explains how to use
`docs/support/programbench_hob_obligation_catalog_v0.json` with the
`adeu_obligation_broker` package during ProgramBench reconstruction runs.

The catalog is a deterministic broker substrate for the current Program ODEU
meta-program. It is not a semantic judge and not a runner. A worker still reads
the README, public help, scout observations, and task packet to decide which
top-level ontology families apply. HOB then imports the inherited children,
validates status/proof rows, blocks false parent closure, and emits the next
frontier.

## Controlling Artifacts

```text
catalog:
  docs/support/programbench_hob_obligation_catalog_v0.json

catalog_id:
  programbench-odeu-meta-program-obligations

catalog_version:
  programbench-hob-v0

catalog_hash:
  sha256:ce171df30a0747750dbc2469a98d44f9b5da87acbc03a4095dd8525965d837e9

source doctrine:
  docs/support/principled_recursive_odeu_meta_program_experimental_v12.md
  docs/support/principled_recursive_odeu_meta_program_experimental_v14.md
  docs/support/principled_recursive_odeu_meta_program_experimental_v15.md
  docs/support/v16_meta_program_operationalization_robustness_patch.md
  docs/support/v17_deterministic_hierarchical_meta_ontology_enforcement.md
```

## Run Placement

Use HOB between semantic reconstruction and probe/implementation work:

```text
visible spec / README / public scout observations
  -> model-authored activation assessment
  -> HOB-A inherited obligation expansion
  -> model-authored status/proof/probe refs for inherited rows
  -> HOB-A traversal validation and frontier
  -> HOB-B closure, next frontier, probe-matrix plan, batch contract
  -> empirical probes and implementation outside HOB
  -> HOB-C delta attribution / stale-ledger / pressure handoff after results
```

## Step 1: Activation Assessment

The worker produces `repo_obligation_activation_assessment@1` after reading the
visible task packet and any allowed public observations. This is the only
semantic judgment stage. The broker validates shape, not truth.

Use only these activation statuses:

```text
applies
not_applicable_proven
candidate_pending
conflict_isolated
```

Example shape:

```json
{
  "schema": "repo_obligation_activation_assessment@1",
  "catalog_id": "programbench-odeu-meta-program-obligations",
  "catalog_version": "programbench-hob-v0",
  "catalog_hash": "sha256:ce171df30a0747750dbc2469a98d44f9b5da87acbc03a4095dd8525965d837e9",
  "semantic_judgment_authority_posture": "model_authored_broker_schema_validated",
  "activation_rows": [
    {
      "node_id": "1",
      "activation_status": "applies",
      "warrant_refs": ["warrant:visible-spec"],
      "activation_note": "The task exposes a CLI control plane."
    }
  ],
  "warrant_rows": [
    {
      "warrant_ref": "warrant:visible-spec",
      "warrant_kind": "visible_spec",
      "authority_layer": "support",
      "warrant_summary": "README and task packet expose command invocation behavior."
    }
  ]
}
```

The worker should normally activate only top-level families (`1` through `12`).
Child nodes become live by inheritance. If a public observation discovers a
behavior-bearing item that is not represented in the catalog, do not force it
into a poor fit; record the missing concept as a catalog-extension pressure.

## Step 2: Expand Inherited Obligations

Run HOB-A expansion:

```python
from pathlib import Path
from adeu_obligation_broker import (
    RepoHierarchicalObligationCatalog,
    RepoObligationActivationAssessment,
    expand_inherited_obligations,
)

catalog = RepoHierarchicalObligationCatalog.model_validate_json(
    Path("docs/support/programbench_hob_obligation_catalog_v0.json").read_text()
)
activation = RepoObligationActivationAssessment.model_validate_json(
    Path("activation.json").read_text()
)

ledger = expand_inherited_obligations(catalog, activation)
Path("inherited_obligation_ledger.json").write_text(
    ledger.model_dump_json(indent=2, exclude_none=True)
)
```

The generated ledger starts with all inherited rows as `open`. This is
intentional. The worker must then fill status rows, proof rows, probe refs, and
implementation owners as reconstruction proceeds.

## Step 3: Fill Status Rows

Every inherited child must end in one of the broker statuses:

```text
covered_terminalized
covered_by_probe_matrix
proved_pass_through
proved_irrelevant
scoped_deferred_with_expected_risk
gold_deferred_with_expected_risk
blocked_pending_observation
blocked_pending_equivalence
conflict_isolated
representative_examples_only
```

Only `covered_terminalized`, `covered_by_probe_matrix`,
`proved_pass_through`, `proved_irrelevant`, and `conflict_isolated` can support
gold parent closure. Scoped deferral and representative examples can support a
scoped run, but they must block gold readiness.

Proof-sensitive statuses require discriminated proof rows:

```text
proved_irrelevant -> irrelevance proof
proved_pass_through -> pass-through proof
scoped_deferred_with_expected_risk -> deferral proof
gold_deferred_with_expected_risk -> deferral proof
blocked_pending_observation -> blocking proof
blocked_pending_equivalence -> blocking proof
```

Do not use prose like "not relevant" as a substitute for a proof row.

## Step 4: Validate and Emit Frontier

Run HOB-A validation after each substantial reconstruction pass:

```python
from adeu_obligation_broker import (
    RepoInheritedObligationLedger,
    emit_frontier,
    validate_obligation_ledger,
)

ledger = RepoInheritedObligationLedger.model_validate_json(
    Path("inherited_obligation_ledger.json").read_text()
)

validation = validate_obligation_ledger(
    catalog=catalog,
    activation=activation,
    ledger=ledger,
)

Path("traversal_validation_report.json").write_text(
    validation.model_dump_json(indent=2, exclude_none=True)
)

frontier = emit_frontier(validation)
```

The frontier is the next deterministic worklist. A failed-closed validation is
not an implementation failure; it means the reconstruction tree is not yet
ready to hand off.

## Step 5: Closure and Probe Planning

When HOB-A validation is clean enough for the intended run scope, use HOB-B:

```python
from adeu_obligation_broker import (
    compute_obligation_closure,
    plan_next_frontier,
    plan_probe_matrix,
    build_implementation_batch_contract,
)

closure = compute_obligation_closure(
    catalog=catalog,
    ledger=ledger,
    validation_report=validation,
)
next_frontier = plan_next_frontier(
    validation_report=validation,
    closure_report=closure,
)
probe_plan = plan_probe_matrix(
    catalog=catalog,
    closure_report=closure,
)
batch = build_implementation_batch_contract(
    probe_matrix_plan=probe_plan,
    included_node_refs=probe_plan.terminal_node_refs,
    owner_ref="worker:implementation",
    max_macro_count=1,
)
```

The probe matrix is plan-only. HOB-B does not observe reference behavior, run
probes, dispatch workers, or authorize official submission.

## Step 6: After Results

After local probes or official eval pressure, use HOB-C to attribute deltas to
numbered nodes. Treat official failures as pressure unless methodological
equivalence and reached-product-behavior were established.

HOB-C should be used for:

```text
delta attribution by numbered node
stale-ledger invalidation when catalog or public schema changes
pressure-only integration handoff
family closeout alignment
```

## Worker Prompt Kernel

Use this prompt fragment when asking a reconstruction worker to use the catalog:

```text
Use docs/support/programbench_hob_obligation_catalog_v0.json.

First produce only repo_obligation_activation_assessment@1 over top-level nodes
1 through 12. The activation rows are your semantic judgment. After HOB expands
the inherited ledger, every inherited child must receive a status, proof/probe
refs where required, and an implementation owner if it will become code work.

Do not patch code until HOB-A validation and HOB-B closure/probe planning show
the intended scope. Do not claim a parent is fixed or gold-ready while inherited
children are open, representative-only, scoped-deferred, or blocked.
```

## Practical Interpretation

For a `trdsql`-like task, the worker may activate:

```text
1 control plane
2 public schema and mode family
3 input resource and route topology
4 input dialect and value-domain grammar
5 embedded language / transform substrate
6 subject, identity, binding, and aggregation
8 output router, renderer, and byte grammar
9 diagnostics, fatal gates, and channel contracts
10 runtime substrate and observation ecology
11 methodological equivalence and warrant
12 probe, readiness, and implementation handoff
```

Once these apply, leaves such as `3.5 wildcard / glob route`, `4.6 TBLN
grammar`, `5.6 joins / subqueries / repeated references`, `8.10 header /
null / final-newline policy`, and `10.2 packaged artifact equivalence` are not
optional. They must be closed, probed, deferred with expected risk, blocked for
specific evidence, or proved irrelevant / pass-through.
