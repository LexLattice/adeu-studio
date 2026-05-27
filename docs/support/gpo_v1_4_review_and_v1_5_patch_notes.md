# Review of General Program Ontology Derived v1.4

Authority layer: `support / review`

Input reviewed:

- `general_program_ontology_derived_v1_4.md`
- comparison context from the recent `trdsql`, `entr`, and `hwatch` reconstruction artifacts already incorporated into the project thread

## 1. Verdict

`general_program_ontology_derived_v1_4.md` is a strong consolidation. The most important improvement is that it clearly separates:

```text
meta-program      = universal method / descent / warrant / handoff
program ontology  = loadable domain vocabulary for software behavior
task instance     = concrete reconstruction target
witness bundle    = implementation/proof artifact under substrate and warrant
```

That is the right architectural split. It prevents the program ontology from becoming another giant prompt checklist, and it allows the HOB broker to stay ontology-agnostic.

The 12-class skeleton is also mostly right:

```text
1  Invocation and control-plane grammar
2  Public schema, mode families, and discoverability
3  Resource and route topology
4  Input dialect, reader, and value-domain grammar
5  Transform and embedded-language substrate
6  Subject, identity, binding, and aggregation
7  State, lifecycle, mutation, and row universe
8  Output router, renderer, and byte grammar
9  Diagnostics, fatal gates, and channel/exit contracts
10 Runtime substrate, dependency, and observation ecology
11 Methodological equivalence, warrant, and evidence authority
12 Orchestrator, handoff, anti-replay, and preservation governance
```

The main v1.5 patch should not be a rewrite. It should be a normalization pass that makes the ontology more executable:

```text
- split behavior ontology from proof/governance overlay;
- canonicalize all placeholder child IDs;
- move eval/run visibility out of the reactive-only section into the general status vocabulary;
- split evidence authority from coverage/readiness/posture;
- prevent official_pressure from appearing as a direct oracle;
- add explicit operationalization-equivalence / audit-to-baton equivalence;
- add several missing program-class profiles from earlier tasks.
```

## 2. What v1.4 gets right

### 2.1 The constructive-witness frame is stable

The central judgment is still the right one:

```text
W ; Π ; Σ ⊢ Cᴡ : Ω*
```

This is the cleanest compact expression of the overall regime: the implementation is a witness bundle, not the program itself; the program is the completed ontology; and verification is always relative to warrant, probes/checkers, and substrate.

Minor patch: later in the document the execution shape becomes:

```text
W_T ; L_T ; Σ ⊢ C_w : T
```

For consistency, v1.5 should use:

```text
W_T ; L_T ; Π_T ; Σ_T ⊢ C_w : Ω*_T
```

`T` is the task seed; `Ω*_T` is the completed theorem statement. The witness inhabits the completed program theorem, not the raw task prompt.

### 2.2 The loadable-ontology contract is exactly the right direction

The ontology-loading contract is one of the strongest sections. It says a loadable ontology must provide nodes, status vocabularies, proof schemas, activation questions, closure rules, irrelevance/pass-through/deferability rules, terminal leaf schema, baton schema, and forbidden promotion rules.

This is the basis for deterministic HOB inheritance:

```text
applies(P) ∧ child(P, C) -> obligation(C)
```

unless the run supplies a warrant for irrelevance, pass-through, blocking, or deferral.

That is the correct response to the repeated failure mode where a worker patches representative children under a parent while leaving siblings implicit.

### 2.3 The domain classes are safely abstracted

The `trdsql` lessons have been abstracted into general classes rather than copied as task specifics:

```text
Resource topology
Input dialect / reader / value domain
Transform / embedded-language substrate
Output router / renderer / byte grammar
Diagnostics / fatal gates / channel-exit contracts
Runtime substrate / dependency / observation ecology
```

The safe generalization is not “YAML/TBLN/jq/globs matter.” It is:

```text
public format names, resource routes, embedded transforms, renderers, and diagnostics
are subtrees of obligations, not labels.
```

### 2.4 The `entr` and `hwatch` lessons are integrated without overfitting

The broad `Reactive scheduler / watcher / supervisor` profile and the narrower `Reactive CLI/TUI command scheduler` profile are both justified.

The distinction is useful:

```text
entr-like class:
  filesystem/resource event topology, watch-list stream, selected-resource binding,
  status helper subprogram, process ecology, PTY control.

hwatch-like subclass:
  command substrate, batch/TUI duality, renderer byte domains,
  runtime-weighted triage, high-score transfer tail.
```

The document correctly warns not to promote task-local spellings, exact key meanings, exact diagnostics, or fixture names into the generic ontology.

## 3. Main structural patches for v1.5

### 3.1 Split the catalog into behavior ontology and proof/governance overlay

Classes `1` through `10` are primarily program-behavior ontology.

Classes `11` and `12` are not exactly behavior ontology. They are the method/warrant/governance overlay required to apply the ontology safely.

That is fine, but v1.5 should label the split explicitly:

```text
ProgramOntology.behavior_core:
  1-10

ProgramOntology.application_overlay:
  11-12
```

This prevents confusion when the ontology is loaded for a task. If the target program is itself an orchestrator, then class `12` can also become product behavior. Otherwise `12` governs the reconstruction process, not the target program.

### 3.2 Promote run visibility state into the general status vocabulary

`Oracle Visibility State Gate` currently lives under the reactive CLI/TUI command scheduler class. It should be general.

Move these states into section `E` or class `11/12`:

```text
artifact_not_readable
branch_not_run
partial_visibility_pressure
full_visibility_product_pressure
runtime_weighted_product_pressure
high_score_transfer_tail
final_green
```

Reason: `results.xml`/branch visibility happened in `hwatch`, but the invariant is general:

```text
Do not assign product meaning to failures until the observation artifact is readable
and the row actually reached product behavior.
```

That also covers port collisions, missing output files, substrate crashes, packaging errors, and resource-ecology failures.

### 3.3 Split evidence authority from evidence coverage

Section `E.2 Evidence Authority` currently mixes at least three things:

```text
authority source: reference_locked, source_tail_needed
coverage status: covered_by_conceptual_probe, covered_by_source_tail
repair posture: source_tail_needed
```

v1.5 should split them:

```text
EvidenceAuthority:
  visible_spec
  semantic_inference
  public_scout
  reference_observation
  target_substrate_probe
  sealed_or_metamorphic_probe
  source_tail
  official_post_eval_pressure
  rejected_patch_history

CoverageStatus:
  uncovered
  covered_by_conceptual_probe
  covered_by_reference_matrix
  covered_by_source_tail
  covered_by_target_substrate_probe
  covered_by_sealed_or_metamorphic_probe

RepairPosture:
  blind_reconstruction
  public_schema_reentry
  source_tail_compatibility
  post_eval_tail_repair
  target_substrate_repair
  scoped_experiment
  gold_attempt
```

This avoids accidental promotion from “covered somehow” to “authoritative oracle.”

### 3.4 Do not let `official_pressure` be an oracle

In the terminal leaf record, the `oracle.authority` field currently includes:

```text
official_pressure
```

That conflicts with the document’s own evidence-boundary rule that official failures are pressure, not clean first-pass facts.

Patch:

```yaml
oracle:
  authority:
    visible_spec | public_scout | reference_observation |
    sealed_or_metamorphic_probe | source_tail | target_substrate_probe

pressure_refs:
  official_post_eval_pressure: []
```

If official pressure is used in a tail phase, require:

```yaml
post_eval_tail_authorization:
  visibility_state: full_visibility_product_pressure | high_score_transfer_tail
  pressure_row_refs: []
  followup_oracle_required: reference_observation | source_tail | target_substrate_probe | sealed_probe
```

Official pressure can authorize re-entry. It should not directly become the expected-behavior oracle.

### 3.5 Add `OPERATIONALIZATION_EQUIVALENCE` explicitly

The document has worker batons and anti-replay gates, but the v16 lesson should be a named equivalence:

```text
W ⊢ AuditTheory ≃[operationalization, S, R] WorkerTask
```

Add this under class `11` or `12`:

```text
11.x Operationalization equivalence
  post-hoc audit theory
  -> numbered HOB nodes
  -> branch matrix
  -> probes
  -> baton
  -> worker task
```

Blocking rule:

```text
A worker task is not a valid test of an updated meta-program unless the audit’s
parent discriminators have been lowered into numbered obligations, probes,
owners, deferrals, closure metrics, and preservation sentinels.
```

This is the exact gap that caused “the theory identified the right parent, but the worker produced only partial improvement.”

### 3.6 Canonicalize all `1.x`, `7.x`, `8.x`, `12.x` nodes

Section `P` uses placeholder IDs. That is acceptable in a note, but not in a loadable ontology.

Promote them into the compact catalog:

```text
1.7 TokenRegionAuthority
1.8 OptionArityValueClass
1.9 RegionAwareHelpUnknownToken
1.10 ConfigCliMergeValidation

5.9 ControlSublanguageValidationTiming

7.8 NoninteractiveReactiveCompletionContract
7.9 RuntimeValidationTiming

8.6 AcceptedControlToRendererState
8.7 DiffDomainSelection
8.8 InteractiveViewportStateRenderer

10.7 BranchResultArtifactLiveness
10.8 RuntimeWeightedObservationCost

12.7 HighScoreTailExactnessPass
12.8 OperationalizationEquivalenceGate
12.9 ArtifactPartitionGate
```

Then replace the placeholder sections with references to these canonical IDs.

### 3.7 Move branch-result artifact liveness into class 10

`Branch Result Artifact Liveness Gate` is currently under the hwatch-specific class. It should be a generic observation-ecology child:

```text
10.7 BranchResultArtifactLiveness
```

Trigger:

```text
missing or unreadable result artifact
large not_run count
branch error
long branch duration with partial progress
observer timeout before result materialization
```

This generalizes cleanly beyond TUI programs.

### 3.8 Add proof schemas for irrelevance, pass-through, and deferral

The ontology repeatedly allows:

```text
proved_irrelevant
proved_pass_through
deferred_with_risk
```

but v1.4 does not fully specify proof-object shapes for those statuses.

Add:

```yaml
irrelevance_proof:
  node_ref: string
  reason_class: not_in_public_schema | impossible_by_program_class | unreachable_by_control_plane | substrate_absent | outside_declared_scope
  evidence_refs: []
  negative_probe_refs: []
  risk_if_wrong: string

pass_through_proof:
  node_ref: string
  input_surface: string
  output_surface: string
  consumers_unaffected: []
  identity_mapping: string
  evidence_refs: []
  negative_controls: []

deferral_record:
  node_ref: string
  deferral_scope: scoped | gold | tail
  expected_score_or_behavior_risk: string
  why_not_now: string
  required_future_evidence: []
```

Without these, workers can still use “not relevant” or “deferred” as prose escapes.

## 4. Missing or underrepresented program-class profiles

v1.4 has good profiles for CLI, resource-processing, language-over-resource, renderer-heavy, long-running/networked, config/stateful, and reactive scheduler tools.

Based on the broader history, I would add three more optional program classes.

### 4.1 Producer-stream reducer / event summarizer

This safely abstracts the `tparse`-style family.

Trigger:

```text
program consumes event records, logs, producer output, stream lines, or runtime reports
and accumulates state before rendering summaries or details.
```

Adds:

```text
producer schema candidate table
multi-consumer payload role split
event lifecycle/order
subject lifecycle and terminal events
raw vs structural output roles
aggregation denominators
failure-detail/body projection
side-effect/raw-follow surfaces
exit/status denominator
fixture morphology realism
```

This should not mention Go test, packages, race, panic, or trimpath. Those are task leaves. The generic parent is event-stream reduction.

### 4.2 Classifier / counter / source-tree analyzer

This safely abstracts the `scc`-style family.

Trigger:

```text
program classifies resources or records into categories, counts them, computes metrics,
or reports grouped summaries over a corpus.
```

Adds:

```text
matcher/classifier source policy
custom-vs-default matcher composition
identity normalization
include/exclude filter law
counter denominator and metric formula
classification-consumer split
projection/rendering consumer split
suggestion/diagnostic grammar
```

This is already partly present as matcher-policy in the older meta-program material, but it is not visible enough in the v1.4 program-class profile list.

### 4.3 Capability/protocol/visualizer program

This safely abstracts the `jplot` lessons.

Trigger:

```text
program renders through a terminal, graphical protocol, dashboard layout, live source,
or capability-negotiated output surface.
```

Adds:

```text
capability substrate
terminal/window/protocol negotiation
render graph topology
observable success contract
witness-scope budget
clocked source process
fatal-gate reachability witness
observer horizon
protocol byte grammar
```

This keeps jplot-specific terms out while preserving the ontology family.

## 5. Smaller textual and structural fixes

### 5.1 Remove duplicate promotion line

Section `E` repeats:

```text
scoped green != gold closed
scoped green != gold closed
```

Remove one.

### 5.2 Clarify `source_tail_needed`

Rename:

```text
source_tail_needed
```

to one of:

```text
source_tail_authorized_pending
source_tail_required_for_gold
```

Current wording mixes evidence state and required method.

### 5.3 Make `display-only` and `compatibility-only` statuses require owners

Section `2.4` says these are not escape hatches. Add fields:

```text
behavior_owner
implementation_owner
observable_surface_refs
preservation_sentinel_refs
```

because compatibility overlays often regress broad parser/renderer owners.

### 5.4 Separate public schema from public examples

Public examples should not automatically activate full schema closure. Add:

```text
public_schema_item
public_example_item
public_hint_item
```

Only schema items inherit mandatory child obligations immediately. Examples and hints should generate candidate obligations unless corroborated by public scout/reference behavior.

### 5.5 Add task-tail row exactness rule to general tail section

The high-score tail rule should say:

```text
At gold-tail stage, all remaining rows must sum exactly to the official tail count.
Approximate bucket counts are not worker-ready.
```

This came up in the trdsql Phase77 review and is still a generally useful rule.

## 6. Proposed v1.5 document shape

I would split the next version into these sections:

```text
A  Core thesis and constructive-witness judgment
B  Meta-program / ontology / task / witness separation
C  Ontology loading contract
D  Kernel operators
E  Status axes and proof-object schemas
F  Behavior core catalog, classes 1-10
G  Application overlay catalog, classes 11-12
H  Program-class activation profiles
I  Orthogonal semantic pools and discovery methods
J  Node / terminal leaf / baton schemas
K  Safe generalizations and forbidden over-generalizations
L  Versioned additions from trdsql, entr, hwatch, and earlier tasks
```

The key change is moving `P` and `Q` from “appendix refinements” into either:

```text
H Program-class activation profiles
```

or the canonical numbered catalog.

## 7. Bottom-line assessment

v1.4 is promotion-worthy as `support / synthesis`. I would not yet mark it as `architecture / lock` because several schema edges are still prose-level:

```text
official pressure as oracle
placeholder child IDs
run visibility status under reactive-only section
insufficient proof schemas for irrelevance/pass-through/deferral
missing operationalization equivalence
behavior ontology mixed with governance overlay without an explicit boundary
```

The safe next promotion is:

```text
GPO v1.5 = v1.4 + normalization into executable catalog form.
```

The strongest sentence to keep is:

```text
Programs fail reconstruction when one of these layers is treated as a label,
example, or broad owner instead of an inherited subtree of obligations.
```

That is the durable abstraction across `trdsql`, `entr`, `hwatch`, and the earlier reconstruction tasks.
