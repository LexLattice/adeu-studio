# Principled Recursive ODEU Meta-Program Experimental v32

Authority layer: support / experimental meta-program revision.

This v32 patch extends:

```text
docs/support/principled_recursive_odeu_meta_program_experimental_v31.md
docs/support/general_program_ontology_derived_v1_5.md
```

It changes the beginning of a ProgramBench-style reconstruction. The general
program ontology is now treated as:

```text
strong prior + obligation vocabulary + falsifiable catalog
```

not as a closed ontology into which every task is merely mapped.

The core move:

```text
README/spec
  -> fresh task-native ontology Ω_task?
  -> independent GPO projection Ω_gpo→task?
  -> optional intent/utility projection Ω_utility?
  -> reciprocal diff
  -> merged activation Ω*
  -> deterministic HOB import
```

Deterministic inherited-child import remains essential, but it must run only
after the task-native and GPO views have been compared.

---

## 1. New Pre-HOB Sequence

Replace the older opening shape:

```text
README/spec
  -> map onto GPO
  -> inherit HOB obligations
```

with:

```text
P1A  Blind task-native ontology pass
P1B  GPO-informed projection pass
P1C  Intent / utility projection pass
P1D  Reciprocal ontology diff
P1E  GPO amendment-candidate ledger
P1F  Merged activation / inherited obligations
```

Blocking rule:

```text
No deterministic HOB child import until P1A-P1E are complete.
```

This does not mean every task-native axis becomes a GPO amendment. It means
every axis must be accounted for before the run claims its ontology is ready
for implementation.

---

## 2. P1A Blind Task-Native Ontology

Input:

```text
README/spec/manual/examples/visible prompt only
```

Forbidden input:

```text
GPO catalog node list
existing task-specific ProgramBench ontology
official eval failures
source code
implementation plan
```

Question:

```text
What kind of program object is implied by this spec, in its own terms?
```

Required outputs:

```yaml
task_native_ontology:
  task_ref: string
  program_object_hypothesis: string
  native_entities: []
  resources: []
  states: []
  event_channels: []
  controls: []
  input_surfaces: []
  output_surfaces: []
  failure_laws: []
  user_promises: []
  hidden_couplings_suspected: []
  evidence_phrases:
    - phrase: string
      supports_node: string
```

The pass should use task-native language first. It may say "watcher",
"converter", "query tool", "visualizer", "formatter", "scheduler", or another
native category before translating it into GPO terms.

---

## 3. P1B GPO Projection

Input:

```text
same visible task packet
docs/support/general_program_ontology_derived_v1_5.md
```

Question:

```text
Given the existing 12-class ProgramOntology, what branches apply and what
children are inherited?
```

Required outputs:

```yaml
gpo_projection:
  activated_top_nodes: []
  activated_program_profiles: []
  inherited_child_obligations:
    - gpo_node_ref: string
      reason: string
      evidence_phrase_ref: string|null
      default_required_status: cover | prove_irrelevant | prove_pass_through | defer
  likely_underdescribed_by_native_pass: []
  irrelevance_proof_needed: []
```

This pass should be aggressive. If a parent applies, children are inherited by
default unless a later proof removes them.

---

## 4. P1C Intent / Utility Projection

Input:

```text
visible task packet only
```

Question:

```text
What useful work is promised to the user, and what workflows or affordances
would be broken if a mechanism axis were missing?
```

Required outputs:

```yaml
utility_projection:
  promised_workflows: []
  user_visible_affordances: []
  negative_utility_cases: []
  expected_resource_roles: []
  expected_control_roles: []
  expected_output_roles: []
  missing_mechanism_suspicions: []
```

Authority rule:

```text
Utility is a discriminator generator, not direct product truth.
```

Utility nodes must reconcile back into task-native or GPO mechanism nodes
before they can become implementation obligations.

---

## 5. P1D Reciprocal Ontology Diff

Required board:

```text
A = task-native mechanism ontology
B = GPO projection
C = intent / utility projection
```

Diffs:

```text
A ∩ B:
  high-confidence inherited task obligations

A - B:
  task-native axes that challenge the GPO or require local extension

B - A:
  likely task-native omissions requiring coverage, irrelevance proof,
  pass-through proof, or deferral

C - (A ∪ B):
  user-promise gaps not yet represented as mechanism

(A ∪ B) - C:
  internal mechanism obligations that may not be user-facing but affect behavior
```

Required schema:

```yaml
spec_native_gpo_reciprocal_diff:
  task_native_ontology_ref: string
  gpo_projection_ref: string
  utility_projection_ref: string|null

  gpo_catches_task_omissions:
    - task_gap_ref: string
      gpo_node_ref: string
      inherited_children: []
      required_status: cover | prove_irrelevant | prove_pass_through | defer

  task_challenges_gpo:
    - task_native_node_ref: string
      nearest_gpo_node_ref: string|null
      mismatch_type:
        missing_parent_class |
        missing_child_under_existing_parent |
        badly_factored_child |
        wrong_trigger_condition |
        too_task_specific_existing_node |
        cross_cutting_axis_not_expressed |
        status_or_warrant_gap |
        orchestrator_phase_gap
      proposed_generic_axis: string
      evidence_phrase: string
      risk_if_ignored: string
      scout_or_probe_pressure: string
      amendment_posture:
        local_extension_only |
        candidate_gpo_child |
        candidate_gpo_parent |
        defer_until_second_task |
        reject_as_task_specific

  utility_challenges_both:
    - utility_ref: string
      promised_workflow: string
      missing_mechanism_node: string|null
      missing_gpo_node_or_child: string|null
      probe_pressure: string

  merged_activation_status:
    blocked |
    ready_for_hob_import |
    ready_with_explicit_gap_risk
```

---

## 6. P1E GPO Amendment-Candidate Ledger

Task-native axes do not automatically mutate the GPO.

Promotion filter:

```text
candidate is generic across plausible programs
candidate is behavior-bearing
candidate is not already covered by a current node
or current coverage is too weak to trigger it early
```

If the filter fails, classify as:

```text
task-local child under existing GPO node
local extension candidate
rejected task-specific detail
defer until second task
```

Required row:

```yaml
gpo_gap_candidate:
  task_native_node: string
  implied_behavior_axis: string
  nearest_current_gpo_node: string|null
  mismatch_type: string
  evidence_phrase_from_spec: string
  proposed_generic_abstraction: string
  risk_if_ignored: string
  probe_pressure: string
  amendment_posture:
    local_extension_only |
    candidate_gpo_child |
    candidate_gpo_parent |
    defer_until_second_task |
    reject_as_task_specific
```

---

## 7. P1F Merged Activation

The merged activation is the only object that may enter deterministic HOB
import.

Required content:

```yaml
merged_activation:
  task_native_nodes_kept: []
  gpo_nodes_activated: []
  utility_nodes_reconciled: []
  inherited_children_to_import: []
  local_extensions: []
  gpo_gap_candidates: []
  irrelevance_proofs: []
  pass_through_proofs: []
  deferrals_with_risk: []
  unresolved_blockers: []
  hob_import_status: blocked | ready | ready_with_gap_risk
```

The HOB broker then imports the inherited child tree from this merged activation
deterministically.

---

## 8. Irrelevance / Pass-Through / Deferral Proof

The reciprocal diff makes proof hygiene more important. A child obligation
cannot disappear by prose.

Required proof shape:

```yaml
obligation_resolution_proof:
  node_ref: string
  claim: irrelevant | pass_through | deferred
  basis:
    absent_from_spec |
    contradicted_by_spec |
    impossible_under_program_class |
    public_schema_absence_pending_scout |
    intentionally_unsupported |
    substrate_not_present |
    equivalent_to_parent_leaf
  evidence_refs: []
  sibling_risk: low | medium | high
  revisit_trigger: public_scout | official_pressure | source_tail | never
```

Forbidden shortcut:

```text
not relevant
```

unless it is backed by the proof object above.

---

## 9. Worker / Orchestrator Contract

The orchestrator must run the three tracks separately enough to avoid semantic
contamination:

```text
P1A task-native worker:
  visible spec only, no GPO catalog.

P1B GPO projection worker:
  visible spec + GPO v1.5.

P1C utility worker:
  visible spec only, utility/user-job lens.

P1D/P1E reconciliation worker or orchestrator:
  all three outputs + GPO v1.5 + HOB protocol.
```

The same model may perform multiple tracks only if the artifact explicitly
records that independence is weaker. For clean experiments, use separate
workers.

---

## 10. v32 Bottom Line

The mature GPO should now be used in two directions:

```text
as a coverage prior:
  it catches what the fresh task ontology missed.

as a falsifiable catalog:
  the fresh task ontology catches what the GPO still lacks, under-factors, or
  fails to trigger early enough.
```

This gate is designed to reduce the failure mode:

```text
GPO is treated as complete enough
  -> task becomes a subset of the GPO
  -> missing axes are discovered only after failed implementation/eval
```

The new rule:

```text
Early reconstruction is a reciprocal diff between task-native ontology,
GPO projection, and intent/utility projection. HOB import starts only after
that diff is accounted for.
```
