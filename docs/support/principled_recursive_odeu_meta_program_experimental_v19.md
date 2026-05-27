# Principled Recursive ODEU Meta-Program Experimental v19

Authority layer: support / experimental meta-program revision.

v19 preserves the v15 product-theory repair doctrine, imports the v16-v18
operationalization and HOB lessons, and adds a blind intent / utility descent
branch. The new branch is not a second source of product truth. It is an
orthogonal discriminator generator that must later be reconciled back onto the
concrete program ontology.

Controlling inputs:

```text
docs/support/principled_recursive_odeu_meta_program_experimental_v15.md
docs/support/v16_meta_program_operationalization_robustness_patch.md
docs/support/v17_deterministic_hierarchical_meta_ontology_enforcement.md
docs/support/phase16_audit_of_audit_v18_patch.md
docs/support/programbench_hob_application_protocol_v2.md
docs/support/programbench_hob_node_question_cards_v0.md
docs/support/programbench_intent_utility_question_cards_v0.md
```

Evidence boundary:

```text
intent / utility reconstruction is visible-spec inference unless a later
observation phase explicitly marks public-observation evidence.

intent / utility rows are not implementation authority, official eval evidence,
source evidence, or clean proof of program behavior.
```

## 1. v19 Thesis

The prior meta-program branch is strong at mechanism descent:

```text
controls
  -> modes
  -> resources
  -> dialects
  -> embedded language / transform
  -> renderers
  -> diagnostics / exits
```

But some failures show that mechanism descent can still cut the program too
syntactically. A separate intent / utility pass can cut the same program through
the user's useful work:

```text
inspect data
query resources
join heterogeneous sources
convert formats
debug schema problems
export results
recover from malformed inputs
compose with downstream tools
```

The central v19 invariant is:

```text
Intent / utility descent must be blind to the program-ontology descent.
The two branches meet only in a reconciliation phase, where utility obligations
must land onto the concrete program ontology or become explicit blockers.
```

## 2. Dual-Descent Structure

Run two independent branches before reconciliation.

### Branch P: Program Ontology Descent

Allowed inputs:

```text
visible README / prompt packet
declared task metadata
public scout observations only after the run reaches an observation phase
```

Primary question:

```text
What kind of executable machine is this program?
```

Outputs:

```text
program ontology
HOB activation assessment
candidate HOB node statuses
mechanism-oriented probe pressure
```

Typical cuts:

```text
CLI grammar
public schema
resource topology
input dialects
embedded language or transform substrate
identity and binding
state / mutation
output routing and byte grammar
diagnostics and exits
runtime substrate
methodological equivalence
handoff readiness
```

### Branch U: Intent / Utility Descent

Allowed inputs:

```text
visible README / prompt packet
declared task metadata
visible examples in the prompt packet
```

Forbidden inputs:

```text
Branch P artifacts
HOB ledger
probe matrix
implementation notes
official failures
source code
postmortem audit
```

Primary question:

```text
What useful work is this program promising to let a user perform?
```

Outputs:

```text
user jobs
workflow slices
utility promises
implied affordances
data/resource ecology
failure-recovery expectations
negative utility cases
candidate workflow / negative / mechanism probe pressure
```

Use `docs/support/programbench_intent_utility_question_cards_v0.md` as the
starter question set.

## 3. Blindness and Contamination Gate

The two branches must carry input ledgers.

Required row:

```yaml
branch_input_ledger:
  branch_id: program_ontology | intent_utility
  allowed_input_refs: []
  forbidden_input_classes: []
  observed_input_hashes: []
  worker_or_phase_ref: string
  contamination_check:
    read_other_branch_artifacts: true | false
    read_implementation_artifacts: true | false
    read_official_failure_artifacts: true | false
    read_source_artifacts: true | false
  status: clean | contaminated | unknown
```

Reject:

```text
intent / utility branch restates the program ontology artifact
intent / utility branch cites HOB nodes before reconciliation
intent / utility branch uses official failures or source-derived facts
program branch imports utility conclusions as behavior without reconciliation
```

## 4. Utility Branch Question Cards

The first version is intentionally Socratic rather than schema-heavy.

Minimum required card families:

```text
universal_utility
workflow_composition
data_ecology
control_and_discoverability
negative_utility
```

Each active card must answer:

```text
what useful job is implied?
what workflow slice performs the job?
what program affordances would make the workflow possible?
what negative cases break the promise?
what evidence makes this visible-spec inference plausible?
what probe pressure would test this obligation later?
```

The worker may use prose, but each utility obligation must have a stable
`utility_ref` so reconciliation can map it.

## 5. Utility-to-Program Reconciliation Gate

Reconciliation is the only point where Branch P and Branch U meet.

Rule:

```text
The program ontology is the target substrate. Utility obligations enrich it;
they do not bypass it.
```

Required row:

```yaml
utility_to_program_mapping_row:
  utility_ref: string
  utility_summary: string
  program_node_target: string | null
  hob_node_target: string | null
  mapping_status:
    mapped_to_existing_program_node |
    creates_candidate_program_node |
    out_of_scope_with_evidence |
    unresolved_program_mapping_blocker
  mapping_warrant:
    visible_spec_text |
    visible_example |
    public_observation |
    semantic_class_inference |
    explicit_out_of_scope
  probe_pressure:
    - mechanism_probe
    - workflow_probe
    - negative_utility_probe
  notes: string
```

Validation:

```text
Every utility_ref must appear in exactly one mapping row.
No implementation handoff while any utility_ref is unresolved without blocker.
No utility row can mark a program behavior gold-ready.
Candidate program nodes must pass through HOB inheritance before probe locking.
Out-of-scope rows need evidence, not convenience.
```

## 6. Contraposition Questions

During reconciliation, ask both directions.

From utility to program:

```text
Which concrete mechanism makes this user job possible?
Which resource, dialect, renderer, diagnostic, or mode does it require?
Which sibling mechanism would break the same utility promise if omitted?
What negative probe would show the utility promise is false?
```

From program to utility:

```text
Which user job does this mechanism serve?
Is this a core affordance, compatibility branch, diagnostic branch, or no-op?
Does the mechanism need workflow coverage or only isolated branch coverage?
Can this mechanism be deferred without losing the declared utility class?
```

If a utility promise has no program landing point, create a candidate program
node or mark it as an unresolved blocker. Do not silently drop it.

## 7. Probe Construction Split

After reconciliation, build probes from three sources.

```text
mechanism probes:
  isolate exact branch behavior, byte grammar, resource identity, exits,
  diagnostics, and side effects.

workflow probes:
  compose the mechanisms required by one utility job.

negative utility probes:
  test malformed, missing, ambiguous, or misleading cases that would violate
  the utility promise even if the happy path works.
```

For a resource-backed embedded-language program, utility probes should often
cross at least:

```text
resource route
  x input dialect / schema
  x embedded-language binding
  x output consumer
  x diagnostic or failure-recovery expectation
```

This is not probe-count inflation for its own sake. The workflow probe exists
only when the utility branch identifies a user job that depends on the
composition.

## 8. HOB Integration

HOB remains the deterministic closure layer.

Process:

```text
1. Branch P produces initial HOB activation.
2. Branch U produces blind utility obligations.
3. Reconciliation maps utility obligations onto program/HOB nodes or creates
   candidate nodes.
4. HOB imports inherited children for every active or newly created parent.
5. HOB validation blocks false parent closure.
6. Probe planning uses mechanism, workflow, and negative utility pressure.
```

Reject:

```text
utility obligation mapped to a parent while inherited children vanish
workflow probe used as proof that sibling mechanism leaves are closed
utility branch used to skip HOB proof / deferral / blocker rows
HOB closure claimed with unresolved utility mapping blockers
```

## 9. Readiness Gates

Pre-implementation handoff requires:

```text
program branch input ledger clean
intent / utility branch input ledger clean
all utility rows reconciled
candidate program nodes routed through HOB
HOB validation has no missing inherited children for active scope
probe matrix identifies mechanism, workflow, and negative utility probes
known scoped gaps are marked as scoped and block gold posture
```

Implementation handoff is blocked by:

```text
unmapped utility obligation
utility row claiming behavior truth directly
program node with inherited children missing status rows
public scout schema item not re-entered
large audit bucket not compiled into HOB child nodes
probe matrix lacking workflow probes for workflow-dependent utility promises
```

## 10. trdsql-Class Example

For a `trdsql`-like program, Branch P may derive:

```text
input dialects
SQL resource binder
renderer byte grammars
config / database controls
diagnostic surfaces
```

Branch U should independently ask:

```text
How does a user inspect unknown tabular data before querying?
How does a user query ad hoc local resources without loading a database first?
How does a user join heterogeneous data sources?
How does a user project nested or semi-structured fields into tabular output?
How does a user convert query results for another tool?
How does a user diagnose wrong headers, missing fields, malformed rows, or bad
selectors?
```

Reconciliation should land those utility obligations onto concrete nodes such
as:

```text
analyze modes
header/default-column policy
JSON / JSONL / YAML / LTSV / TBLN / text / width importers
jq or selector handling
resource-to-SQL table identity
mixed-resource joins
CSV / JSON / markdown / raw / YAML / TBLN renderers
diagnostic channel and exit contracts
```

The result is an enriched program ontology, not a separate utility spec.

## 11. v19 Rejects

Reject:

```text
utility branch sees program branch before reconciliation
utility branch becomes vague product prose with no stable utility refs
utility row never lands on a program node, candidate node, out-of-scope proof,
or blocker
program branch ignores utility obligations because they are not in the first
mechanism tree
workflow probes replaced by isolated option probes when the utility promise is
compositional
happy-path workflow accepted without negative utility probes
implementation begins before utility-to-program reconciliation is complete
official failures used as utility evidence in a clean branch
source-derived facts laundered into intent / utility reconstruction
```

## 12. Bottom Line

v17 says:

```text
Selected ontology parents import child obligations deterministically.
```

v18 says:

```text
Audit pressure must be compiled into numbered HOB child nodes before worker
implementation.
```

v19 adds:

```text
Before HOB closure and probe construction, run a blind intent / utility descent
and reconcile it back onto the program ontology. The useful-work view supplies
orthogonal discriminator pressure, but only the reconciled program ontology can
drive probes and implementation.
```

