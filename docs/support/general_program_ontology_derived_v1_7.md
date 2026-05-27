# General Program Ontology Derived v1.7

Authority layer: `support / synthesis`

Scope: This note abstracts the general program ontology that has emerged from
the recent reconstruction work. It is intentionally **not** a task-specific
repair plan and **not** the universal meta-program. It is a domain ontology for
programs: a loadable object vocabulary that the universal meta-program can use
when the task domain is software/program behavior.

Primary source inputs:

```text
principled_recursive_odeu_meta_program_experimental_v29.md
test_group_feature_ontology_probe_mapping.md
entr_progression_generalization_v30.md
hwatch_phase18_v33_tail_schema_integration.md
hwatch_codex_output_review_v34.md
gpo_v1_4_review_and_v1_5_patch_notes.md
artifacts/manual_runs/programbench_hyperfine_v44_gpt55_high_run_C_20260526T145836+0300/phase_outputs/p18_run_evolution_win_groups.md
.codex/review-shell/chatgpt-downloads/hyperfine_run_evolution_review_v46.md
.codex/review-shell/chatgpt-downloads/mp_gpo_v45_v1_6_review.md
```

The task-specific examples that motivated these abstractions should remain in
their task artifacts. The reusable layer is the ontology structure below.

---

## A. Core Thesis

A program is best modeled as a structured abstract object with behavior-bearing obligations, not as a bag of tests and not as source files alone.

```text
visible statement / README / public interface
  -> candidate program ontology Ω?
  -> warranted program completion Ω*
  -> numbered behavior-obligation tree
  -> probes/checkers/oracles as obligation witnesses
  -> implementation witness bundle Cᴡ
  -> runtime model ⟦Cᴡ⟧Σ
```

The implementation is a witness bundle for an abstract program object. It is valid only relative to:

```text
W  = warrant / evidence / authority map
Π  = probes, checkers, reference observations, source-tail facts
Σ  = target substrate / runtime / packaging environment
Ω* = best warranted program ontology
```

Central judgment:

```text
W ; Π ; Σ ⊢ Cᴡ : Ω*
```

The ontology work exists to avoid proving the wrong theorem. Many observed failures across tasks were not implementation bugs in the narrow sense; they were cases where the theorem statement was under-derived, the witness bundle was not equivalent across substrates, or the orchestrator moved phases without a legal transition proof.

---

## B. Meta-Program / Ontology / Task Separation

The meta-program sits one level above this ontology.

```text
Meta-program
  universal method for reasoning, descent, warrant, equivalence, closure,
  repair, and handoff.

Domain ontology
  loadable object vocabulary for a class of problems.
  Example here: programs.

Task instance
  one concrete target reconstructed through that ontology.

Witness
  implementation, proof, analysis, model, or answer that claims to satisfy
  the task.
```

Formal split:

```text
M      = universal meta-program / reasoning method
O_D    = domain ontology for domain D
T      = concrete task/problem
A_T    = activation of relevant O_D branches for T
L_T    = inherited obligation ledger from HOB
W_T    = warrants/evidence/equivalence claims
C_w    = witness artifact
Σ      = substrate / execution / observation environment
```

Execution shape:

```text
M(O_D, T, W_T) -> A_T
HOB(O_D, A_T) -> L_T
W_T ; L_T ; Π_T ; Σ_T ⊢ C_w : Ω*_T
```

`T` is the task seed. `Ω*_T` is the completed theorem statement for the task.
The witness inhabits the completed program theorem, not the raw prompt.

The HOB broker must remain ontology-agnostic. It does not know what a renderer,
statute, theorem, paper section, or experimental method means. It knows only:

```text
catalog node
parent/child inheritance
activation
proof/status validity
closure validity
frontier emission
stale-ledger invalidation
```

Therefore the same meta-program and broker can load different domain ontologies:

```text
ProgramOntology
LawOntology
ScientificTheoryOntology
AcademicPaperOntology
HistoricalCausalityOntology
ProductDesignOntology
```

The ontology below is the `ProgramOntology` domain catalog candidate.

---

## C. Ontology Loading Contract

A loadable ontology must provide:

```yaml
ontology_id: string
ontology_version: string
authority_layer: support | planning | architecture | lock
domain_scope: string
catalog_nodes: []
status_vocabularies: {}
proof_object_schemas: {}
activation_question_templates: []
closure_rules: []
irrelevance_rules: []
pass_through_rules: []
deferability_rules: []
terminal_leaf_schema: {}
handoff_baton_schema: {}
forbidden_promotion_rules: []
```

The meta-program may ask semantic questions and generate activation judgments.
The HOB broker deterministically imports inherited child obligations from the
loaded ontology after activation.

Forbidden ontology-loading shortcuts:

```text
activating a parent without importing children
closing a parent because a representative child is green
using prose "not relevant" without a proof object
treating scoped-green local probes as gold readiness
transferring evidence across substrate/observer/witness states without
  typed equivalence
```

### C.1 Spec-Native / GPO Reciprocal Diff Schema

The GPO is a strong prior and inherited-obligation vocabulary, not a closed
universe. Early reconstruction must compile three views before deterministic
HOB import:

```text
task-native mechanism ontology
GPO projection
utility / intent projection
```

Required proof object:

```yaml
spec_native_gpo_reciprocal_diff:
  task_native_ontology_ref: string
  gpo_projection_ref: string
  utility_projection_ref: string | null

  gpo_catches_task_native_omissions:
    - task_gap_ref: string
      gpo_node_ref: string
      inherited_children: []
      required_status:
        cover | prove_irrelevant | prove_pass_through | defer

  task_native_challenges_gpo:
    - task_native_node_ref: string
      nearest_gpo_node_ref: string
      mismatch_type:
        missing_parent_class |
        missing_child_under_existing_parent |
        badly_factored_child |
        wrong_trigger_condition |
        cross_cutting_axis_not_expressed |
        status_or_warrant_gap |
        orchestrator_phase_gap
      proposed_generic_axis: string
      evidence_phrase: string
      risk_if_ignored: string
      amendment_posture:
        local_extension_only |
        candidate_gpo_child |
        candidate_gpo_parent |
        defer_until_second_task |
        reject_as_task_specific

  utility_challenges_both:
    - utility_ref: string
      promised_workflow: string
      missing_mechanism_node: string
      missing_gpo_node_or_child: string
      probe_pressure: string

  merged_activation_status:
    blocked | ready_for_hob_import | ready_with_explicit_gap_risk
```

Blocking rule:

```text
No deterministic HOB import until the reciprocal diff is complete.
```

The reciprocal diff may propose GPO amendments, but it does not mutate the
locked ontology catalog. Candidate amendments remain task-local until promoted
through the normal support-doc revision path.

---

## D. Kernel Operators

The ontology still uses the v8 kernel algebra:

```text
Factor      entity boundary + decomposition
Partition   value/state/error/grammar alternatives
Bind        roles, consumers, subjects, identities, denominators
Transform   computations, reducers, classifiers, formulas, embedded languages
Sequence    lifecycle, ordering, precedence, mutation, teardown
Expose      observable surfaces: bytes, files, status, routes, side effects
Compose     interactions, non-commutation, precedence, cross-products
Warrant     authority, evidence, readiness, equivalence, deferral
```

These operators should be treated as constructors of program obligations.

A node is not closed by naming it. Every active node must either:

```text
be terminalized,
be covered by an inherited child subtree,
be proved irrelevant,
be proved pass-through,
be blocked pending evidence,
or be explicitly deferred with expected risk.
```

---

## E. Status Vocabulary

The following vocabulary should be stored as separate status axes, not one flat
enum. Mixing discovery, evidence, readiness, tail state, and negative history in
one field lets workers accidentally promote weak evidence into closure.

### E.1 Discovery State

```text
candidate_inferred
  The node was inferred from visible semantics, not yet reference-locked.

public_schema_discovered
  Public help/schema/scout behavior exposed the node.

conceptually_probe_ready
  The branch has a named discriminator and probe shape, but no locked oracle yet.
```

### E.2 Evidence Authority Source

```text
visible_spec
  Public task text, README, manual, help text, or documented examples.

semantic_inference
  Model-derived inference from visible material. This can propose obligations
  but cannot close them alone.

public_scout
  Black-box observation of public program surfaces such as help, version,
  no-arg behavior, reference executable probes, and visible resource behavior.

reference_observation
  Reference executable or public oracle observation has locked expected behavior
  for the declared scope.

target_substrate_probe
  Probe executed inside the intended target substrate, package state, runtime,
  or evaluator-equivalent environment.

sealed_or_metamorphic_probe
  Probe designed to resist replay or fixture overfitting.

source_tail
  Source/library/fixture inspection authorized only after a tail or compatibility
  surface has been narrowed and labeled.

official_post_eval_pressure
  Official failure or score movement. This authorizes re-entry and repair
  hypotheses but is not itself a clean oracle.

rejected_patch_history
  Negative evidence from a tried patch class, regression, or zero-win repair.
```

### E.3 Coverage Status

```text
uncovered
  The node has no concrete coverage yet.

covered_by_conceptual_probe
  A conceptual/reference probe matrix discovered and bounded the behavior family.

covered_by_reference_matrix
  Reference/public observations cover the node's declared branch matrix.

covered_by_source_tail
  Source-tail inspection closed the narrowed compatibility surface.

covered_by_target_substrate_probe
  Target-substrate checks cover the behavior or packaging claim.

covered_by_sealed_or_metamorphic_probe
  A sealed or metamorphic probe covers replay-sensitive behavior.
```

### E.4 Repair Posture

```text
blind_reconstruction
  No post-eval or source-tail evidence is being used.

public_schema_reentry
  Public help/schema/scout evidence expanded the theorem statement.

source_tail_compatibility
  Narrowed source/library compatibility tail is active.

post_eval_tail_repair
  Official pressure has authorized a labeled tail repair.

target_substrate_repair
  Failure is owned by packaging, ABI, dependency, runtime, or observer
  equivalence.

scoped_experiment
  The run is testing a bounded method or subtree, not claiming gold closure.

gold_attempt
  All known scoped gaps are either closed or explicitly carried as blockers.
```

### E.5 Readiness State

```text
scoped_green_with_official_sibling_tail
  The local subtree is useful and preservation-worthy, but official pressure still names unclosed siblings under the same owner.

gold_tail_not_closed
  The global theorem is stable, but explicit gold-tail public dialect/byte-surface leaves remain open.
```

### E.6 Tail State

```text
remaining_hidden_tail
  The behavior owner is known and public/source parity is reached on available fixtures, but one hidden fixture still differs.
```

### E.7 Run Visibility State

```text
artifact_not_readable
  The run did not produce readable result artifacts or observation output.

branch_not_run
  Rows or branches were skipped/not-run before product behavior could be judged.

partial_visibility_pressure
  Some product surfaces are visible, but observer/resource failures still mask
  part of the row universe.

full_visibility_product_pressure
  Branches produce readable pass/fail rows and product behavior is reachable.

runtime_weighted_product_pressure
  Product behavior is visible, but runtime distribution is itself diagnostic.

high_score_transfer_tail
  The broad theorem is stable and remaining failures are compact transfer
  boundaries.

final_green
  Parsed official or target-equivalent row universe is green.
```

Rule:

```text
Do not assign product meaning to failures until the observation artifact is
readable and the row actually reached product behavior.
```

### E.8 Negative Constraint

```text
rejected_broad_patch
  A patch class was tried and invalidated by regressions or zero wins; it becomes a future constraint.
```

### E.9 Proof Object Schemas

```yaml
irrelevance_proof:
  node_ref: string
  claim: irrelevant
  basis:
    absent_from_public_schema |
    contradicted_by_spec |
    impossible_under_active_parent |
    user_visible_mode_absent |
    substrate_absent |
    equivalent_to_parent_leaf |
    explicitly_deferred_scope |
    outside_declared_scope
  evidence_refs: []
  negative_probe_refs: []
  protected_surfaces:
    stdout: bool
    stderr: bool
    exit: bool
    files: bool
    state: bool
    row_universe: bool
    aggregation_denominator: bool
  sibling_risk: low | medium | high
  revisit_trigger: public_scout | official_pressure | source_tail | never
  risk_if_wrong: string

pass_through_proof:
  node_ref: string
  claim: pass_through
  input_surface: string
  output_surface: string
  consumers_unaffected: []
  identity_mapping: string
  evidence_refs: []
  negative_controls: []
  sibling_risk: low | medium | high
  revisit_trigger: public_scout | official_pressure | source_tail | never

deferral_record:
  node_ref: string
  claim: deferred
  deferral_scope: scoped | gold | tail
  basis:
    evidence_unavailable |
    scope_cut |
    source_tail_required |
    target_substrate_required |
    official_pressure_required |
    intentionally_unsupported
  expected_score_or_behavior_risk: string
  why_not_now: string
  required_future_evidence: []
  sibling_risk: low | medium | high
  revisit_trigger: public_scout | official_pressure | source_tail | never
```

Plain prose such as "not relevant" or "deferred" is not a valid proof object.

The most important promotion rule:

```text
scoped green != gold closed
local green != target-substrate proof
source parity on visible fixtures != hidden-tail solved
rejected patch != useless evidence
```

---

## F. General Numbered Ontology Skeleton

This is the proposed reusable HOB-style top-level catalog. It should be used as an inherited obligation tree: if a parent applies, children are inherited unless a proof says otherwise.

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

v1.5 splits the catalog into two roles:

```text
ProgramOntology.behavior_core:
  Classes 1-10. These describe behavior-bearing surfaces of target programs.

ProgramOntology.application_overlay:
  Classes 11-12. These describe warrant, evidence transfer, handoff,
  preservation, and orchestration rules for applying the ontology safely.
```

If the target program is itself an orchestrator, workflow tool, verifier, or
agentic harness, class `12` may also become product behavior. Otherwise class
`12` governs the reconstruction process rather than the target program.

Each class below is general. Task-specific names should be attached later as children, not baked into this catalog.

---

## Class 1. Invocation and Control-Plane Grammar

Programs expose an invocation language. It is often the first hidden grammar.

### 1.1 Command shape

```text
binary name / executable identity
subcommand or no-subcommand shape
positional operands
stdin-vs-argv split
query/string/file arguments
`--` separator behavior
```

### 1.2 Flag/token grammar

```text
short vs long spelling
aliases
bool / int / float / string / enum / list / mapping values
--flag=value vs --flag value
missing value behavior
greedy next-token binding
negative integer ambiguity
repeated flag composition
unknown flag policy
suggestion grammar if present
```

### 1.3 Control precedence

```text
help/version/no-args precedence
invalid + help precedence
multiple mode flags
format flag precedence
explicit flag vs inferred/default setting
stdout/stderr/exit behavior for control-plane branches
```

### 1.4 Control-plane compatibility overlays

A program can have compatibility behavior that is not derivable from generic argparse. This is not a parser rewrite target. It is a branch-local overlay.

Closure requires:

```text
positive branch examples
negative sibling examples
stdout/stderr/exit split
help/usage byte surface
compatibility conflict labels when public/reference surfaces disagree
```

---

## Class 2. Public Schema, Mode Families, and Discoverability

Programs often reveal a schema larger than the README through help, version, analyze/list/debug/config modes, or public scout probes.

### 2.1 Public schema re-entry

Publicly discovered controls are not merely option-list updates. They must re-enter the ontology.

```text
observed schema item
  -> role bucket
  -> affected resources/dialects/transforms/renderers/diagnostics
  -> inherited child obligations
  -> probes or deferral
```

Separate public statement classes:

```text
public_schema_item
  A documented or observed control/mode/format/resource that directly expands
  the mandatory obligation tree.

public_example_item
  An example invocation or fixture. It proposes candidate obligations, but does
  not close the full schema unless corroborated by public scout/reference
  behavior.

public_hint_item
  A descriptive phrase, screenshot, marketing line, or README implication. It
  guides semantic search but needs warrant before inherited closure.
```

### 2.2 Mode-as-program

A mode can be a separate program with its own inputs, transforms, renderers, and diagnostics.

Common mode families:

```text
help / version / usage
analyze / inspect / explain
list / enumerate / catalog
config / debug / environment report
export / import
watch / follow / poll / serve
compare / diff / validate
```

### 2.3 Discovery and advice modes

A discovery mode is not a renderer string. It binds to:

```text
sampled input morphology
inferred schema/type
resource identity
format advice
query or command examples
driver/target-specific quoting
empty/header-only/no-data cases
```

### 2.4 Public schema closure rule

```text
A public schema item is not closed until it has been classified as:
  behavior-affecting,
  display-only,
  pass-through,
  compatibility-only,
  out-of-scope with evidence,
  or deferred with expected risk.
```

`display-only` and `compatibility-only` are not escape hatches. They still
require observable-surface closure for the surfaces they affect:

```text
display-only
  must name behavior_owner, implementation_owner, observable_surface_refs, and
  preservation_sentinel_refs, then close bytes/layout/channel/exit if the
  display is observable.

compatibility-only
  must name behavior_owner, implementation_owner, observable_surface_refs, and
  preservation_sentinel_refs, then close the branch discriminator, positive
  branch, negative siblings, and preservation sentinels.
```

---

## Class 3. Resource and Route Topology

Many programs operate over resources, not just values. Resource topology is a first-class ontology layer.

### 3.1 Resource identity

```text
path identity
logical name vs physical path
stdin aliases
URL or network resource
config/db/resource profile
wildcard/glob resource sets
resource suffix selectors
quoted resource tokens
extension-derived identity
cwd / environment / tilde behavior
```

### 3.2 Resource route lifecycle

```text
resolve
expand
open
decode
import/bind
transform
write/export
flush/close
teardown
```

### 3.3 Multi-resource topology

```text
one resource -> one subject
many resources -> concatenated stream
many resources -> separate named tables/entities
wildcard no-match behavior
multi-file header/schema behavior
ordering of expanded resources
per-resource diagnostics
```

### 3.4 Resource adapter ecology

Resources may pass through adapters:

```text
compression codecs
encoding/decoding
network clients/servers
temporary files
database connections
external helper tools
library-backed readers
filesystem side effects
```

Closure requires a route matrix, not a single file-open probe.

---

## Class 4. Input Dialect, Reader, and Value-Domain Grammar

A public input format is a sublanguage, not a label.

### 4.1 Input physical grammar

```text
record boundaries
line boundaries
field delimiters
headers / metadata / type rows
comments / unsupported lines
escaping / quoting
blank lines / whitespace lines
malformed forms
multi-document or streaming forms
```

### 4.2 Schema-bearing readers

Some formats declare schema inside the data.

```text
name rows
type rows
metadata rows
inferred column names
missing/duplicate columns
column count mismatch
schema binding into downstream subjects
```

### 4.3 Value-domain grammar

```text
string
empty string
missing value
null token
numeric-looking string
integer/float/decimal
boolean
binary / invalid UTF-8
nested array/object
date/time/timestamp
schema-declared type
runtime type after transform
```

### 4.4 Reader-local row lifecycle

Row controls are not necessarily global post-import filters. They may differ by reader.

```text
header handling
skip/order of skip vs header
limit/preread
row numbering
blank row filtering
sparse record union
wildcard/multi-file row union
binary decode policy
```

### 4.5 Dialect diagnostic grammar

Reader errors must be terminalized separately from successful parse behavior.

```text
invalid syntax
truncated record
bad delimiter
unsupported line
duplicate key/name
column mismatch
line/column numbering
channel and exit
category prefix / timestamp policy
```

### 4.6 Reader-writer pair closure

If a format exists as input and output, parser success and writer success are not independent.

Required surfaces:

```text
input only
output only
input -> raw output
input -> same-dialect output
input -> other renderer output
same-dialect output -> re-import if supported
null/type/value preservation
newline/final newline/escaping preservation
```

---

## Class 5. Transform and Embedded-Language Substrate

Programs often embed a language or transform substrate: SQL-like query, jq-like selector, regex-like matcher, expression language, calculation formula, or reducer.

### 5.1 Embedded-language recognition

```text
language-bearing argument
language-bearing file
resource suffix expression
selector path
filter expression
projection expression
mutation statement
aggregation formula
```

### 5.2 Language-to-resource binding

Language tokens may bind to resources or subjects. This requires a context-aware lexer/parser, not a global regex.

```text
relation/resource context
projection/expression context
quoted identifier context
string literal context
function argument context
comment/escape/nesting context
mutation target context
subquery context
```

### 5.3 Transform semantics

```text
selection
projection
join/composition
aggregation
mutation
ordering
typing/coercion
error propagation
multiple statements / repeated transforms
```

### 5.4 Selector sublanguages

Selectors must be closed as languages when public behavior supports operators.

```text
field access
array iteration
array index
pipes/composition
select/filter predicates
renaming / object construction
recursive descent
multiple extraction paths
type mismatch diagnostics
```

### 5.5 Transform vs renderer boundary

A transform can produce values that renderers later display. Do not repair transform bugs through renderer strings unless the failing leaf is genuinely renderer-owned.

---

## Class 6. Subject, Identity, Binding, and Aggregation

Programs create subjects: files, records, rows, tests, packages, commands, resources, sessions, entities, fields, tables, or rendered rows.

### 6.1 Subject identity

```text
raw identity
display identity
grouping identity
path/resource identity
schema/column identity
runtime/generated identity
alias identity
quoted/escaped identity
```

### 6.2 Binding

```text
input resource -> subject
subject -> transform variable
subject -> output row
field -> schema column
config key -> mode behavior
matcher -> subject class
```

### 6.3 Aggregation and denominators

Denominators are first-class.

```text
rendered rows denominator
selected rows denominator
hidden-but-counted rows denominator
exit/status denominator
summary denominator
side-effect denominator
```

### 6.4 Type and provenance authority

Type claims need a source:

```text
declared schema
reader-inferred type
runtime substrate type
transform-result type
renderer-local inference
reference-locked special case
```

A renderer should not invent type provenance from string shape when that class has known regression risk.

---

## Class 7. State, Lifecycle, Mutation, and Row Universe

A program has temporal structure. Many failures are ordering failures.

### 7.1 Lifecycle stages

```text
bootstrap
parse controls
resolve config/env/defaults
resolve resources
open/decode/import
bind subjects
run transform
render/export
flush/close
teardown
exit/status
```

### 7.2 Fatal gate ordering

When several errors could apply, the first winning fatal gate is part of program behavior.

```text
parse error vs semantic error
resource open error vs transform error
input diagnostic vs output diagnostic
mode error vs data error
terminal/substrate error vs source error
```

A later error can be a reachability witness proving an earlier branch was accepted.

### 7.3 Mutation and persistent state

```text
database state
config state
file updates
append/writeback behavior
temp/cached artifacts
coverage/profile/report artifacts
rollback/retry behavior
```

### 7.4 Row universe

The row universe is the set of records that exist before selection/rendering. It may depend on reader-local lifecycle, resource topology, and transform stage.

```text
physical row
semantic row
hidden row
generated row
numbered row
blank/empty/null row
multi-resource row
row after transform
rendered row
```

---

## Class 8. Output Router, Renderer, and Byte Grammar

Output is not one surface. It is routing plus renderer plus byte grammar plus side effects.

### 8.1 Output route

```text
stdout
stderr
file path
extension-inferred renderer
explicit renderer flag
compression/encoding adapter
append vs overwrite
missing output path / invalid path
```

### 8.2 Output format precedence

```text
explicit format vs output extension
first-wins vs last-wins
format aliases
stdout vs file behavior
output-without-guess controls
conflicting format flags
```

### 8.3 Renderer byte grammar

Every byte-sensitive renderer must split:

```text
header
body
row separator
group separator
blank lines
escaping
quoting
null rendering
numeric formatting
Unicode/binary handling
cell width/alignment/wrapping
final newline / CRLF
stdout/stderr/file split
```

### 8.4 Downstream-consumer contract

Some renderers are for downstream machines, not humans.

```text
raw streams
JSON/JSONL
YAML
CSV/TSV/LTSV
markdown/table formats
binary/compressed output
```

A downstream-consumer renderer must preserve parseable grammar and value semantics, not only human-readable resemblance.

### 8.5 Renderer-library equivalence

If the target program uses a different library, host output is not the oracle. The reconstruction must translate, emulate, replace, or perform source-tail repair on the target surface.

---

## Class 9. Diagnostics, Fatal Gates, and Channel/Exit Contracts

Diagnostics are behavior, not incidental strings.

### 9.1 Diagnostic ownership

```text
control-plane parse diagnostic
resource diagnostic
reader diagnostic
transform diagnostic
mode diagnostic
renderer/export diagnostic
substrate/dependency diagnostic
harness/observer diagnostic
```

### 9.2 Channel and exit contract

```text
stdout vs stderr
usage printed with error or success
exit 0 / 1 / 2 / signal/timeout
timestamp or prefix
category label
attached query/resource text
partial side effects before error
```

### 9.3 Diagnostic precedence

Diagnostics must be sequenced by fatal gate order. A row with the wrong diagnostic often means the program reached the wrong layer, not merely printed the wrong string.

### 9.4 Suggestion and compatibility diagnostics

Unknown-token suggestions are their own grammar:

```text
candidate source set
similarity metric
threshold
ordering/ties
maximum suggestions
namespace boundary
```

### 9.5 Host-library diagnostic translation

Different parser libraries emit different wording, line/column numbering, duplicate-key policy, and stream behavior. At gold-tail stage, this must be explicit.

---

## Class 10. Runtime Substrate, Dependency, and Observation Ecology

A program runs on a substrate. Substrate leakage is observable behavior when it reaches public surfaces.

### 10.1 Target-substrate equivalence

```text
interpreter/compiler version
runtime ABI
packaged artifact identity
dependency availability
external helper tools
locale/timezone
filesystem ordering
terminal/PTY capability
OS/network features
permissions
```

No local green result should be promoted unless the relevant substrate equivalence is proven or explicitly scoped.

### 10.2 Optional dependency contract

Optional modules, codecs, binaries, DB drivers, and OS facilities require:

```text
local availability probe
target-substrate availability probe
portable fallback or bundled dependency
failure diagnostic if absent
route behavior for input/output
```

### 10.3 Observation ecology

Some failures happen before product behavior is reached.

```text
ports/sockets
PTYs/terminals/tmux
subprocesses/long-running loops
signals/teardown
temp files/caches/coverage files
locks/DB files
parallel workers/reruns
```

Required labels:

```text
REACHED_PRODUCT_BEHAVIOR
RESOURCE_OWNER
COLLISION_EDGE
ECOLOGY_WARRANT
```

### 10.4 Observable success contract

Success may be defined by more than exit code or bytes.

```text
render accepted
loop alive
file flushed
coverage artifact exists
server handled requests
protocol witness accepted
observer can still read
```

### 10.7 Branch result artifact liveness

The observer must produce readable artifacts before product-tail attribution is
valid.

Trigger:

```text
missing or unreadable result artifact
large not_run count
branch error
long branch duration with partial progress
observer timeout before result materialization
```

Required row:

```yaml
branch_result_artifact_liveness:
  branch_id: string
  not_run_count: int
  branch_duration: string
  product_behavior_reached: yes | no | uncertain
  result_artifact_path: string
  artifact_written: yes | no | partial | unknown
  process_tree_clean: yes | no | unknown
  timeout_density: low | medium | high
  first_layer_owner: observation_ecology | candidate_liveness | harness | unknown
  product_tail_authorized: true | false
```

### 10.8 Runtime-weighted observation cost

For long-running, reactive, TUI, network, or branch-heavy programs, runtime
distribution is evidence about the failure layer.

Required split:

```text
semantic owner: what behavior is wrong
runtime owner: why observing it costs time
```

Common runtime owners:

```text
should_have_fast_failed
flag_leaked_to_child
shell_template_wait
batch_lifetime_wait
true_tui_state_wait
observer_horizon_wait
cleanup_contamination
```

---

## Class 11. Methodological Equivalence, Warrant, and Evidence Authority

Evidence transfer requires typed equivalence.

### 11.1 Equivalence judgment

```text
W ⊢ A ≃[L, S, R] B
```

Meaning:

```text
under warrant W,
A and B are equivalent at layer L,
within scope S,
under relation R.
```

Layers include:

```text
statement equivalence
public-interface equivalence
observation-oracle equivalence
witness-bundle equivalence
target-substrate equivalence
execution-topology equivalence
resource-ecology equivalence
behavioral terminal-leaf equivalence
warrant equivalence
```

### 11.2 Evidence classes

```text
visible_spec
semantic_inference
public_scout
reference_observation
local_candidate_probe
sealed_or_metamorphic_probe
official_post_eval_pressure
source_tail
target_substrate_probe
rejected_patch_history
```

### 11.3 Evidence boundary rules

```text
official failures are pressure, not clean first-pass facts
source-tail facts repair target compatibility, not original blind inference
public scout surfaces must re-enter ontology before implementation
local probes are regression evidence unless anti-replay sealed/metamorphic checks exist
rejected patches become negative constraints
```

---

### 11.4 Source-tail authorization

Source inspection is not the default method for blind reconstruction. It is
authorized when the run posture explicitly changes from blind conceptual
reconstruction to source-tail compatibility repair.

Allowed source-tail triggers:

```text
conceptual/reference probes have narrowed the behavior owner
official/post-eval pressure identifies terminal dialect or byte-surface drift
public/reference fixtures are insufficient to close a library/substrate surface
remaining failures are small enough to be treated as compatibility tail
the artifact explicitly labels source-derived facts as source_tail evidence
```

Source-tail facts may prove:

```text
target library/parser/renderer behavior
owner function/module for a tail leaf
diagnostic wording source
resource route lifecycle
type provenance source
negative patch class invalidity
```

Source-tail facts must not be laundered into:

```text
clean first-pass evidence
visible spec evidence
generic ontology truth
proof that hidden siblings are solved
permission for broad owner rewrites without preservation sentinels
```

### 11.5 Hidden-tail attribution

Hidden or sealed failures should be assigned to the earliest warranted layer
that can explain them.

```text
substrate failure -> target-substrate or package-artifact equivalence
not-run row -> visibility / observation ecology
runtime timeout -> liveness or observer horizon
compact high-score row -> transfer-boundary exactness
byte mismatch -> renderer byte domain or downstream consumer contract
```

Hidden-tail attribution does not close a node. It decides which node receives
the next observation, probe, source-tail, or implementation baton.

### 11.6 Operationalization equivalence

An audit theory is not automatically a worker-ready baton.

```text
W ⊢ AuditTheory ≃[operationalization, S, R] WorkerTask
```

Operationalization equivalence covers the descent from:

```text
post-hoc audit theory
  -> numbered HOB nodes
  -> branch matrix
  -> probes
  -> implementation owners
  -> deferrals/blockers
  -> preservation sentinels
  -> worker task
```

Blocking rule:

```text
A worker task is not a valid test of an updated meta-program unless the audit's
parent discriminators have been lowered into numbered obligations, probes,
owners, deferrals, closure metrics, and preservation sentinels.
```

---

## Class 12. Orchestrator, Handoff, Anti-Replay, and Preservation Governance

The orchestrator constructs the run witness. Worker outputs can be locally good while the run is invalid.

### 12.1 Phase transition law

Every phase transition must be:

```text
typed
gated
evidenced
recorded
```

The orchestrator must not move from ontology to implementation because a narrative seems plausible.

### 12.2 Worker baton fields

Any implementation baton should include:

```yaml
handoff_type: scoped_subtree_closure | compatibility_overlay | target_dependency_equivalence | gold_tail_batch
target_cluster: string
target_hob_nodes: []
primary_gate: string
allowed_implementation_owners: []
forbidden_implementation_owners: []
required_pre_patch_probes: []
required_reference_observations: []
required_target_substrate_observations: []
required_preservation_sentinels: []
official_tail_rows_used_as_pressure_only: []
local_matrix_closure_target: string
post_patch_report_must_include:
  - rows closed by numbered node
  - regressions by preservation sentinel
  - remaining sibling tail
  - readiness state after patch
```

### 12.3 Anti-replay and mechanism posture

If the program theorem is generative, the witness must be generative.

Disallowed as sufficient proof:

```text
exact argv dispatch
fixture-signature dispatch
known-output lookup
visible-heldout replay
byte snapshot without rule
```

Required:

```text
mechanism owner map
sealed or metamorphic probes
fallback coverage for valid siblings
literal-overlap audit
implementation-visible/checker-only split
```

### 12.4 Preservation governance

Every accepted win becomes an obligation.

```text
win-owner registry
implementation impact cone
preservation sentinel import
non-commutative axis check
rejected patch class ledger
```

---

## G. Orthogonal Semantic Pools

A single mechanism ontology can miss utility or substrate cuts. Use orthogonal semantic pools as discriminator generators, not as independent truth sources.

Default pools:

```text
P  Program-mechanism ontology
U  Intent / utility
S  Public schema / discovery surface
R  Resource ecology and route topology
D  Data dialect and value-domain grammar
T  Transform / embedded language substrate
O  Output / downstream-consumer projection
N  Negative utility / failure precedence
E  Methodological equivalence / substrate
H  Historical delta / regression conservation
M  Source/library method surface when source-tail is authorized
```

Rule:

```text
semantic pool output = discriminator pressure
reconciled HOB node = obligation candidate
observed/warranted probe = behavior evidence
implementation patch = witness attempt
```

No single pool may close a parent. Closure requires reconciliation into numbered nodes plus warrant.

---

## H. General Discovery Methods by Layer

Different failures require different discovery methods. More probes are not always the right answer.

| Layer | Failure smell | Best method |
| --- | --- | --- |
| L0 visible statement | README too small or ambiguous | semantic base ontology + utility pool |
| L1 native ontology -> recursive model | missing parent discriminator | ontology descent + public schema re-entry |
| L2 branch tree -> terminal leaves | labels without grammar | deterministic HOB inheritance + sublanguage closure |
| L3 terminal leaves -> reference lock | exact byte/error/exit unknown | public/reference empirical scout |
| L4 observation -> schema repair | help/scout reveals larger public grammar | public schema re-entry gate |
| L5 handoff | broad task too big | worker baton with owner/gate/sentinel constraints |
| L6 local gate | visible probes green but official poor | anti-replay sealed/metamorphic gate |
| L7 official pressure | broad failure buckets | audit-to-tree compilation + layer attribution |
| L8 source tail | library/dialect exactness still differs | source-tail repair with impact cones |
| L9 gold tail | small explicit tail | row-level ownership exactness + microgrammar closure |

---

## I. Safe Generalizations From the Recent Task

The following are safe to promote generally.

### I.1 Test namespace is not ontology

Official test groups are often arbitrary mixtures of:

```text
parser behavior
resource routing
row lifecycle
embedded sublanguage
renderer behavior
mode/config behavior
substrate/dependency behavior
diagnostic behavior
```

The stable unit is the behavior owner, not the test namespace.

Concrete mapping relation:

```text
official_test_namespace
  -> feature_surface
  -> behavior_owner
  -> implementation_owner
  -> ontology_node
  -> probe/source warrant
```

These relations are not interchangeable:

```text
test namespace
  names where pressure appeared.

behavior owner
  names the semantic mechanism that explains the pressure.

implementation owner
  names the code/substrate surface that a patch may touch.

ontology node
  names the inherited obligation that must be closed or deferred.
```

Any post-eval audit should build this mapping before patching. Otherwise a
worker may fix a namespace symptom through the wrong behavior or implementation
owner.

### I.2 Feature labels are not sublanguage closure

Names like `YAML`, `TBLN`, `JSON`, `width`, `jq`, `markdown`, `raw`, or `config` are labels until decomposed into:

```text
physical grammar
value domain
schema binding
row lifecycle
transform behavior
renderer byte grammar
diagnostics
option overlays
substrate/library equivalence
```

### I.3 Source-tail often means library equivalence

At the tail, remaining failures often reflect the exact behavior of a target library or source-owned helper:

```text
parser diagnostics
renderer scalar formatting
stream decoder lifecycle
fixed-width table inference
codec framing
glob/resource stream behavior
```

This should trigger source-tail or host-library translation, not broad ontology revision.

### I.4 Rejected patches are positive constraints

A rejected patch class is a learned impossibility or risk cone. It should be carried into future batons as:

```text
forbidden_patch_class
regression sentinel source
required alternative owner
impact-cone warning
```

### I.5 Score movement must be node-owned

Raw score deltas are insufficient. Each delta should be mapped to:

```text
node closed
owner touched
sentinels preserved
new regressions
remaining sibling tail
method used
```

### I.6 Hidden tails are layer-specific

A hidden official tail after public/source parity is not necessarily broad ontology failure. It may be:

```text
fixture morphology exactness
resource topology edge
library-dialect microgrammar
host-substrate mismatch
observer/harness edge
```

Classify it by earliest explanatory layer.

---

## J. Canonical Node And Terminal Leaf Records

Every ontology node should eventually be representable as:

```yaml
node_id: string
parent_id: string|null
semantic_name: string
program_class_role: string
kernel_operator_basis: [Factor|Partition|Bind|Transform|Sequence|Expose|Compose|Warrant]
active_status:
  one_of:
    - applies
    - inherited_required
    - proved_irrelevant
    - proved_pass_through
    - scoped_deferred_with_risk
    - gold_deferred_with_risk
    - blocked_pending_observation
    - blocked_pending_equivalence
primary_owner: string
secondary_owners: []
observable_surfaces: []
input_authorities: []
output_authorities: []
resource_or_substrate_refs: []
value_domain_refs: []
sequence_or_precedence_refs: []
diagnostics_refs: []
projection_refs: []
probe_refs: []
source_refs: []
preservation_sentinels: []
forbidden_patch_classes: []
readiness:
  scoped: string
  gold: string
  tail: string|null
closure_kind:
  open |
  exhaustive_public_schema |
  finite_enum_closed |
  matrix_closed |
  metamorphic_rule_closed |
  source_tail_equivalent |
  host_library_equivalent |
  fixture_corpus_equivalent |
  scoped_examples_only |
  blocked |
  deferred
```

### J.1 Terminal leaf record

A terminal leaf is the smallest behavior claim that can be locked, tested,
implemented, deferred, or preserved independently.

```yaml
leaf_id: string
parent_node_id: string
semantic_name: string
behavior_owner: string
implementation_owner: string
input_domain:
  argv: []
  stdin: string|null
  files: []
  env: {}
  cwd: string|null
  pre_state: {}
controls:
  flags: []
  modes: []
  inferred_defaults: []
preconditions: []
observable_surfaces:
  stdout: byte_contract | ignored | empty | contains | structured
  stderr: byte_contract | ignored | empty | contains | structured
  exit: int|string
  files: []
  side_effects: []
  timing_or_liveness: null|string
fatal_gate_order: []
oracle:
  authority: visible_spec | public_scout | reference_observation |
    sealed_or_metamorphic_probe | source_tail | target_substrate_probe
  oracle_ref: string
  comparison_mode: byte_exact | normalized | structured | substring |
    side_effect | liveness
pressure_refs:
  official_post_eval_pressure: []
post_eval_tail_authorization:
  visibility_state: null | full_visibility_product_pressure |
    runtime_weighted_product_pressure | high_score_transfer_tail
  pressure_row_refs: []
  followup_oracle_required:
    null | reference_observation | source_tail | target_substrate_probe |
    sealed_or_metamorphic_probe
preservation_sentinels: []
negative_patch_constraints: []
readiness:
  scoped: open | green | blocked | deferred
  gold: open | green | blocked | deferred
  residual_tail: string|null
closure_kind:
  open |
  exhaustive_public_schema |
  finite_enum_closed |
  matrix_closed |
  metamorphic_rule_closed |
  source_tail_equivalent |
  host_library_equivalent |
  fixture_corpus_equivalent |
  scoped_examples_only |
  blocked |
  deferred
```

Terminalization rule:

```text
A node with observable behavior is not terminalized until at least one terminal
leaf states its input domain, controls, pre-state, expected observable surfaces,
owner, oracle, preservation sentinels, and readiness.
```

---

## K. HOB Inheritance Rule

A parent class selection imports child obligations.

```text
applies(P) ∧ child(P, C) -> obligation(C)
```

unless there is a warrant for:

```text
irrelevant(C)
pass_through(C)
blocked(C)
deferred(C, scope, expected_risk)
```

This is the deterministic enforcement rule that prevents workers from patching representative children while leaving inherited siblings implicit.

---

## L. Worker-Handoff Rule

Never hand a worker a broad phrase such as:

```text
fix YAML
fix TBLN
fix input dialects
fix output renderer
fix SQL binder
fix remaining failures
```

A valid baton names:

```text
one bounded subtree
numbered node IDs
allowed owners
forbidden owners
required probes
required source/reference observations
preservation sentinels
negative-history patch classes
closure condition
expected residual sibling tail
```

---

## M. General Program Classes And Triggered Subtrees

This section is the class index and trigger summary. Detailed reusable profiles
live in later profile sections such as `P`, `Q`, and `R`. A loadable catalog
should not duplicate the same inherited children in multiple places; the class
index should point to the detailed profile definition by stable node IDs.

The ontology should be activated by program class.

### M.1 CLI tool

Triggers:

```text
1 Invocation grammar
2 Public schema
8 Projection surfaces
9 Diagnostics/channel/exit
11 Methodological equivalence
12 Handoff/anti-replay
```

### M.2 Resource-processing tool

Adds:

```text
3 Resource topology
4 Input dialects
6 Identity/binding
7 Lifecycle/row universe
10 Substrate/dependency
```

### M.3 Language-over-resource tool

Adds:

```text
5 Embedded language substrate
6 Subject binding and aggregation
7 Mutation/lifecycle
8 Downstream output contracts
```

### M.4 Renderer-heavy tool

Prioritizes:

```text
8 Byte grammar
9 Diagnostics paired with projection
10 Terminal/substrate if interactive
12 Anti-replay byte-snapshot guard
```

### M.5 Long-running / interactive / networked tool

Adds:

```text
10 Observation ecology
10 Observable success contract
7 teardown/liveness lifecycle
12 orchestrator resource gate
```

### M.6 Config/stateful tool

Adds:

```text
2 Mode-as-program
3 Config resource topology
7 Persistent state/mutation
9 Config diagnostics
10 dependency/substrate
```

### M.7 Reactive scheduler / watcher / supervisor tool

Trigger when the program:

```text
watches files/resources
runs commands after events
listens for keyboard, signal, timer, child-state, or filesystem events
restarts or supervises children
keeps a loop alive after work
generates or invokes command/status helper scripts as part of behavior
```

Adds:

```text
1 Multi-channel control plane
3 Watch resource topology
5 Command boundary language
5 Status filter/helper subprogram when present
7 Reactive scheduler lifecycle
7 Child process supervision
9 Reactive diagnostics/exit/liveness
10 Interactive/control-terminal observation topology
12 rejected-patch memory and preservation sentinels
```

Inherited child obligations:

```text
EVENT_CHANNEL_TOPOLOGY
  split configuration stream, runtime event stream, control stream,
  child-state stream, signal stream, timer stream, network stream, and
  filesystem watcher stream by role and observer.

CONFIG_STREAM_VS_CONTROL_STREAM
  if stdin configures the program and the program also has runtime controls,
  do not assume the controls also come from stdin. Model tty, PTY, signal, or
  other control resources separately.

RESOURCE_WATCH_REGISTRATION
  separate opened resource, registered watch identity, parent identity,
  direct-container identity, displayed identity, symlink target, hidden entry,
  deletion/replacement identity, and child metadata where relevant.

SCHEDULER_STARTUP_EVENT_LIVENESS
  split startup run, postponed startup, first event, debounce/consolidation,
  restart-before-run, exit-after-run, remain-live-after-run, and fatal-event
  after command.

COMMAND_BOUNDARY_AND_ARGUMENT_BINDING
  split direct argv execution, shell-string execution, placeholder or selected
  resource binding, argv0/$0 binding, cwd/env defaults, quoting, exec failure,
  and command-class-specific lifecycle.

CHILD_PROCESS_SUPERVISION
  split direct child versus process group, restart policy, termination signal,
  parent signal forwarding, already-exited child reaping, zombie prevention,
  terminal-close cleanup, child output ownership, and parent status derivation.

STATUS_FILTER_SUBPROGRAM
  if a helper script/filter/template transforms child status into reports,
  model generated template, custom preservation, path/env override, creation
  timing, permissions, input record grammar, exit/signal grammar, helper
  failure, and stdout/stderr/status projection.

INTERACTIVE_CONTROL_TERMINAL
  when keyboard/PTY/curses/terminal behavior appears, split control terminal
  presence, stdin configuration, key grammar, ignored keys, quit/trigger keys,
  composition with modes, nonblocking read, and observer horizon.

DIRECT_CONTAINER_CONFLICT_LATTICE
  if one resource can be both watched object and container of watched objects,
  split direct route versus derived-parent route, startup behavior, child-entry
  mutation behavior, hidden-entry policy, count-change fatal behavior,
  command-class-specific behavior, interactive composition, and exit/liveness
  consequence.
```

Safe abstraction boundary:

```text
Do not generalize task-local spellings such as concrete placeholder tokens,
specific env variable names, exact key meanings, exact diagnostic strings, or
specific flag names. Generalize only the behavior owner and inherited axes.
```

### M.8 Benchmark statistical command runner

Trigger when the program:

```text
runs one or more user commands repeatedly
measures timing or resource usage
supports warmup, run count, minimum/maximum run, or calibration controls
compares command results
exports structured benchmark results
expands parameter sweeps into command cases
shows progress or live status
controls child stdin/stdout/stderr
supports prepare/conclude/setup/cleanup hooks
has child failure or ignore policy
```

This class is distinct from a generic CLI, a command runner, or a renderer-heavy
tool. Its central object is a measured sample set. Its visible behavior is a
family of projections from that sample set: human summary, comparison,
structured exports, progress, warnings, and child-process side effects.

Adds or prioritizes:

```text
1 ControlPlane
  public option and command-boundary grammar
  value-option spelling matrix
  command payload region authority

7 LifecycleStateMutation
  pre-execution validation and fatal precedence
  command execution substrate
  warmup and measured-run scheduler
  child process lifecycle
  failure / ignore policy

6 SubjectIdentityBindingAggregation
  sample-set identity
  statistics reducers
  comparison denominator and reference binding

4 InputDialectAndValueDomain / 5 TransformSubstrate
  parameter sweep sublanguage
  command template substitution grammar

8 OutputRouterRenderer
  human summary renderer
  progress observer matrix
  structured export dialect schemas

10 RuntimeSubstrateObservationEcology
  observer topology for progress and child output
  benchmark runtime cost and calibration ecology

12 OrchestrationHandoffPreservation
  monotone tail preservation for high-score compatibility fixes
```

Inherited child obligations:

```text
1. public option and command-boundary grammar
2. pre-execution validation and fatal precedence
3. command execution substrate
4. warmup and measured-run scheduler
5. sample-set state object
6. statistics reducer
7. unit selector and projection
8. comparison denominator and renderer
9. parameter sweep sublanguage
10. child I/O lifecycle graph
11. failure and ignore policy
12. progress observer matrix
13. human summary renderer
14. structured export dialect schemas
15. tail compatibility and owner preservation
```

Closure warning:

```text
One successful command timing row does not close this class.
One export format does not close export dialects.
One parameter example does not close the parameter sublanguage.
One progress style does not close observer topology.
One comparison table does not close denominator/reference/sort behavior.
```

Safe abstraction boundary:

```text
Do not generalize task-specific benchmark names, exact diagnostic strings,
exact table wording, or official row IDs. Generalize only the state object,
subtree obligations, transition gates, and preservation rules.
```

### M.9 Producer-stream reducer / event summarizer

Trigger when the program:

```text
consumes event records, logs, producer output, stream lines, or runtime reports
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

Safe abstraction boundary:

```text
Do not generalize task-local event names, framework-specific record fields,
or exact fixture morphology. Generalize stream reduction, subject lifecycle,
denominators, projections, and status ownership.
```

### M.10 Classifier / counter / source-tree analyzer

Trigger when the program:

```text
classifies resources or records into categories, counts them, computes metrics,
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

### M.11 Capability / protocol / visualizer program

Trigger when the program:

```text
renders through a terminal, graphical protocol, dashboard layout, live source,
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

---

## N. What Should Not Be Generalized

Do not promote task-local facts into the generic ontology, such as:

```text
specific file names
specific library names
specific official test names
specific exact diagnostic strings
specific phase numbers
specific row counts
specific source file names
specific one-off fixture morphology
```

These belong in task-specific artifacts as warrant references. The generic ontology may promote only:

```text
behavior owner classes
operator/macro gates
warrant states
readiness states
orchestration rules
failure-layer taxonomy
negative patch-class memory
```

---

## O. Proposed General Catalog v0.1

A compact version suitable for future numbered HOB promotion:

```text
1. ControlPlane
  1.1 InvocationShape
  1.2 FlagTokenGrammar
  1.3 ControlPrecedence
  1.4 StreamExitContract
  1.5 CompatibilityOverlay
  1.6 MultiChannelControlPlane
  1.7 TokenRegionAuthority
  1.8 OptionArityValueClass
  1.9 RegionAwareHelpUnknownToken
  1.10 ConfigCliMergeValidation
  1.11 ControlSchemaReachability
  1.12 CommandBoundaryGrammar

2. PublicSchemaAndModes
  2.1 HelpSchemaReentry
  2.2 ModeAsProgram
  2.3 DiscoveryAdviceMode
  2.4 ConfigDebugListMode
  2.5 PublicSchemaItemLedger

3. ResourceTopology
  3.1 ResourceIdentity
  3.2 RouteResolution
  3.3 MultiResourceExpansion
  3.4 CodecOrAdapterRoute
  3.5 PathAndEnvironmentNormalization
  3.6 ResourceDiagnosticSurface
  3.7 WatchResourceTopology
  3.8 ResourceMutationLifecycle

4. InputDialectAndValueDomain
  4.1 PhysicalGrammar
  4.2 SchemaBearingGrammar
  4.3 ValueDomain
  4.4 ReaderLocalLifecycle
  4.5 DialectDiagnosticGrammar
  4.6 ReaderWriterPairClosure
  4.7 HostLibraryParserSurface
  4.8 ParameterSweepSublanguage

5. TransformSubstrate
  5.1 EmbeddedLanguageRecognition
  5.2 ResourceBindingInsideLanguage
  5.3 TransformSemantics
  5.4 SelectorSublanguage
  5.5 MutationSemantics
  5.6 TypeCoercionAndFunctionSemantics
  5.7 CommandBoundaryLanguage
  5.8 StatusFilterSubprogram
  5.9 ControlSublanguageValidationTiming
  5.10 CommandTemplateSubstitutionGrammar

6. SubjectIdentityBindingAggregation
  6.1 RawVsDisplayIdentity
  6.2 SchemaAndColumnIdentity
  6.3 BindingMap
  6.4 AggregationDenominators
  6.5 TypeProvenanceAuthority
  6.6 SampleSetStateObject
  6.7 ComparisonDenominatorRenderer
  6.8 StatisticsReducer
  6.9 UnitSelectorProjection

7. LifecycleStateMutation
  7.1 StartupToTeardownSequence
  7.2 FatalGatePrecedence
  7.3 RowUniverse
  7.4 PersistentState
  7.5 SideEffectLifecycle
  7.6 ReactiveSchedulerLifecycle
  7.7 ChildProcessSupervision
  7.8 NoninteractiveReactiveCompletionContract
  7.9 RuntimeValidationTiming
  7.10 BenchmarkWarmupMeasuredRunScheduler
  7.11 CommandExecutionIOLifecycleGraph
  7.12 FailureIgnorePolicy

8. OutputRouterRenderer
  8.1 OutputRoute
  8.2 FormatPrecedenceOverlay
  8.3 RendererByteGrammar
  8.4 DownstreamConsumerContract
  8.5 RendererLibraryEquivalence
  8.6 AcceptedControlToRendererState
  8.7 DiffDomainSelection
  8.8 InteractiveViewportStateRenderer
  8.9 StructuredExportResultSchema
  8.10 ProgressObserverTopology
  8.11 HumanSummaryRenderer

9. DiagnosticsExitChannels
  9.1 DiagnosticOwnership
  9.2 ChannelExitContract
  9.3 DiagnosticPrecedence
  9.4 SuggestionGrammar
  9.5 HostLibraryDiagnosticTranslation
  9.6 ReactiveDiagnosticsExitLiveness

10. RuntimeSubstrateObservationEcology
  10.1 TargetSubstrateEquivalence
  10.2 OptionalDependencyContract
  10.3 ObservationEcology
  10.4 ObservableSuccessContract
  10.5 PackageArtifactParity
  10.6 InteractiveObserverTopology
  10.7 BranchResultArtifactLiveness
  10.8 RuntimeWeightedObservationCost

11. WarrantEquivalenceAuthority
  11.1 EquivalenceJudgment
  11.2 EvidenceClass
  11.3 PromotionAuthority
  11.4 SourceTailAuthorization
  11.5 HiddenTailAttribution
  11.6 OperationalizationEquivalence

12. OrchestrationHandoffPreservation
  12.1 PhaseTransitionLaw
  12.2 WorkerBaton
  12.3 AntiReplayGate
  12.4 PreservationSentinelImport
  12.5 PatchImpactCone
  12.6 RejectedPatchLedger
  12.7 HighScoreTailExactnessPass
  12.8 ArtifactPartitionGate
  12.9 TaskTailRowExactnessGate
  12.10 OwnerAwareMonotonicTailGate
```

---

## P. v1.5 Canonical Reactive CLI/TUI Tail Nodes

The `hwatch` score-98 tail adds a reusable refinement for reactive CLI/TUI
programs. Once the broad program class is correct, remaining failures often
move from program-class discovery into adjacent transfer-boundary exactness.

Add the following optional children when the relevant parent class is active.

### 1.7 TokenRegionAuthority

Parent:

```text
1. ControlPlane
```

Distinguishes:

```text
option-control region
option-value region
command-payload region
post-`--` command region
subcommand-like payload region
config/env/default-injected region
```

Question:

```text
Where does parser authority end, and which formerly-special tokens become
ordinary child argv bytes after that boundary?
```

### 1.8 OptionArityValueClass

Parent:

```text
1. ControlPlane
```

Every option must declare:

```text
required value
optional value
forbidden value
repeatable / non-repeatable
dash-prefixed value policy
equals-form policy
missing-value diagnostic/exit
invalid-value diagnostic/exit
parser vs runtime validation timing
```

### 1.9 RegionAwareHelpUnknownToken

Parent:

```text
1. ControlPlane
```

Help, version, and unknown-token behavior is region-sensitive. A token such as
`--help` or `--unknown` may be an option in the control region and a command
payload after the command boundary.

### 1.10 ConfigCliMergeValidation

Parent:

```text
1. ControlPlane
```

Environment/config/default tokens must be checked against CLI tokens for:

```text
duplicate non-repeatable errors
override/shadow laws
repeatable accumulation
source-specific diagnostics
exit behavior
```

### 7.8 NoninteractiveReactiveCompletionContract

Parent:

```text
7. LifecycleStateMutation
```

Splits noninteractive reactive modes into:

```text
ordinary bounded command
ordinary bounded multi-frame command
command failure with parent-success policy
unknown-command payload
explicit timeout/liveness probe
invalid parser case
persistent stream
```

Rendered output is not sufficient evidence. Closure requires stdout, stderr,
exit code, process lifetime, and observer-timeout posture.

### 8.6 AcceptedControlToRendererState

Parent:

```text
8. OutputRouterRenderer
```

Every accepted display-control flag must have:

```text
parser acceptance
stored state
mode-builder propagation
renderer consumption
scoped byte-grammar effect
```

### 8.7 DiffDomainSelection

Parent:

```text
8. OutputRouterRenderer
```

Diff behavior must declare its comparison domain:

```text
raw bytes
UTF-8 decoded text
Unicode scalar values
grapheme clusters
terminal display cells
ANSI-tokenized semantic spans
ANSI raw escape fragments
```

### 5.9 / 7.9 ControlSublanguageValidationTiming

Parents:

```text
5. TransformSubstrate
7. LifecycleStateMutation
```

For mini-languages such as keymaps, filters, shell templates, or style grammars,
validation timing is a behavior surface:

```text
syntax accepted / rejected
semantic action accepted / rejected
unknown action tolerated / inert / runtime-only
multiple declarations union / replace / error
duplicate key first-wins / last-wins / error
parser / runtime / on-use / never validation
```

### 12.7 HighScoreTailExactnessPass

Parent:

```text
12. OrchestrationHandoffPreservation
```

Trigger:

```text
The broad ontology is stable, official/local failures form a compact tail, and
the remaining rows live at adjacent layer-transfer boundaries.
```

Required posture:

```text
Attach every remaining row to a primary ontology node, adjacent transfer
boundary, implementation owner, preservation sentinels, allowed patch scope,
and closure probes before any broad owner rewrite.
```

---

## Q. v1.5 Reactive CLI/TUI Command Scheduler Profile

The `hwatch` solved run promotes a reusable class that is narrower than all
reactive programs but broader than a task-specific TUI clone.

### Q.1 `REACTIVE_CLI_TUI_COMMAND_SCHEDULER`

Trigger when a program:

```text
runs or re-runs commands on an interval or event
maintains a live loop
has batch and interactive/TUI modes
controls child processes
projects changing command output
uses PTY, tmux, keyboard, mouse, or terminal control
has shell/direct-exec/template command forms
has aftercommands, logs, history, pane navigation, filters, or keymaps
```

Do not generalize task-local keys, flag names, exact diagnostics, fixture
names, or output literals. Generalize the scheduler/control/substrate/liveness
structure.

Inherited children:

```text
1. control-plane grammar and token-region authority
2. command boundary and child argv ownership
3. shell/direct-exec/template substrate
4. child process supervision and signal/exit law
5. batch/noninteractive lifetime contract
6. batch renderer and ANSI byte grammar
7. TUI control-terminal topology
8. TUI pane/history/filter/keymap state machine
9. log/aftercommand/resource side effects
10. diagnostic/fatal/liveness contracts
11. observation ecology and branch-result artifact liveness
12. runtime-weighted repair planning
13. high-score transfer-boundary exactness
```

Relationship to `entr`-style reactive scheduler:

```text
entr emphasized filesystem event topology, watch-list stream, command
substitution, status filters, process ecology, and PTY control.

hwatch adds child-command substrate, batch/TUI duality, renderer byte domains,
runtime-weighted branch triage, and high-score tail transfer exactness.
```

### Q.2 Oracle Visibility State Gate

Classify every official/local run before assigning product meaning to failures.
This gate is general; it is listed here because `hwatch` forced it into view,
but its vocabulary lives in `E.7 Run Visibility State`.

Allowed states:

```text
artifact_not_readable
branch_not_run
partial_visibility_pressure
full_visibility_product_pressure
runtime_weighted_product_pressure
high_score_transfer_tail
final_green
```

Blocking rule:

```text
Do not patch product ontology from not-run rows until the visibility state is
full_visibility_product_pressure or better.
```

### Q.3 Branch Result Artifact Liveness Gate

Trigger when an official run has:

```text
results.xml missing/unreadable
large not_run count
branch error
TUI/tmux/timeout-heavy branch
long branch duration with partial visible progress
```

Canonical node:

```text
10.7 BranchResultArtifactLiveness
```

Required row:

```yaml
branch_result_artifact_liveness:
  branch_id: string
  not_run_count: int
  branch_duration: string
  product_behavior_reached: yes | no | uncertain
  result_artifact_path: string
  artifact_written: yes | no | partial | unknown
  process_tree_clean: yes | no | unknown
  tmux_pty_state: clean | contaminated | unknown
  timeout_density: low | medium | high
  first_layer_owner: observation_ecology | candidate_liveness | harness | unknown
  product_tail_authorized: true | false
```

### Q.4 Runtime-Weighted Reactive Triage Gate

Trigger when a reactive/TUI branch dominates the feedback-loop runtime.

Canonical node:

```text
10.8 RuntimeWeightedObservationCost
```

Required split:

```text
semantic owner: what behavior is wrong
runtime owner: why observing it costs time
```

Required categories:

```text
should_have_fast_failed
flag_leaked_to_child
shell_template_wait
batch_lifetime_wait
true_tui_state_wait
observer_horizon_wait
cleanup_contamination
```

### Q.5 Command Substrate Gate

The watched command is an embedded substrate, not a string append.

Children:

```text
default shell string
custom shell wrapper
placeholder template
direct argv exec
aftercommand helper program
shell-vs-direct diagnostics
child exit vs parent exit policy
```

### Q.6 Batch Lifetime Contract Gate

Split noninteractive reactive modes into:

```text
bounded samples
bounded multi-frame samples
persistent streams
command-error liveness rows
parser fast-fail
child-error parent-success rows
```

Do not globally make batch one-shot or globally persistent.

### Q.7 Reactive Renderer Byte Domain Gate

Separate byte domains before renderer repair:

```text
raw command bytes
selected stdout/stderr/output projection
terminal ANSI control sequences
line diff
word diff
watch diff
line-number overlay
reverse/tab/display transformations
TUI state rendering
```

### Q.8 Local TUI Subtree Harness Gate

Full official eval must not be the inner loop for high-latency interactive
state machines.

Required local harnesses when applicable:

```text
tmux/libtmux parity harness
tui2cli/key feeding harness
pane focus/navigation harness
history accumulation harness
filter/keymap harness
help modal harness
observer-horizon harness
```

### Q.9 High-Score Transfer Tail Gate

Trigger when:

```text
score is high, broad ontology is stable, and remaining failures form a compact
tail at adjacent layer-transfer boundaries.
```

Rule:

```text
At high score, broad owner patches are forbidden unless row ownership proves
that the broad owner is still the earliest active failure layer.
```

Required row:

```yaml
high_score_tail_row:
  failure_ref: string
  primary_transfer_boundary:
    token_region | option_arity | lifetime | renderer_state |
    byte_domain | config_merge | validation_timing | other
  primary_owner: string
  preservation_sentinels: []
  forbidden_patch_classes: []
  local_tail_probe_refs: []
  official_authorization: scoped_tail | gold_tail
```

Tail row exactness rule:

```text
At gold-tail stage, all remaining rows must sum exactly to the official tail
count. Approximate bucket counts are not worker-ready.
```

### Q.10 Authority And Score Gates

Add an evidence authority state:

```text
post_eval_tail_authorized_source_surface
```

Meaning:

```text
official/local eval has exposed a compact tail with clean branch visibility;
source/test/branch-workspace inspection is allowed only to localize that tail;
the resulting facts remain post-eval pressure, not clean first-pass evidence.
```

Add a solved-status guard:

```text
rounded score 100 / solved marker != full green.
full green requires parsed official rows to be green.
```

## R. v1.6 Benchmark Statistical Command Runner Profile

The `hyperfine` full-green run adds a reusable profile for programs whose main
object is not merely a command invocation but a statistical benchmark plan and
sample set.

Canonical class:

```text
BENCHMARK_STATISTICAL_COMMAND_RUNNER
```

### R.1 Control Schema Reachability Gate

Canonical node:

```text
1.11 ControlSchemaReachability
```

Before product-mechanism repair, prove that valid public controls reach their
product branch and invalid controls fail at the correct fatal gate.

Required coverage:

```text
separated-value option form
inline equals option form
missing-value diagnostic
invalid-value diagnostic
value-begins-with-dash rule
command-boundary rule
cross-option validation rule
```

Rule:

```text
If a valid public token is rejected before product behavior is reached, the
failure is owned first by control/schema reachability, not by the product
mechanism that would have run behind it.
```

### R.2 Benchmark Sample State Object Gate

Canonical node:

```text
6.6 SampleSetStateObject
```

A statistical benchmarker must model the sample set explicitly.

Required state candidates:

```text
warmup scheduler
measured-run scheduler
timing array
exit-code array
mean / standard deviation / median / min / max / range
user/system CPU fields
memory/resource usage fields
time-unit projection
calibration or runtime-overhead adjustment where exposed
```

Rule:

```text
A single elapsed-time row is insufficient evidence of benchmarker closure.
Any renderer, comparison, export, warning, or progress surface that depends on
the whole measured sample set must be treated as a projection from sample state.
```

### R.3 Parameter Sweep Sublanguage Gate

Canonical node:

```text
4.8 ParameterSweepSublanguage
```

Parameter controls form a grammar and propagation law, not text replacement.

Required split:

```text
list versus scan declarations
duplicate names
mode mutual exclusion
cartesian product expansion
empty value versus empty domain
numeric scan parse/step/range law
visible display scale
escaping and delimiter law
exact placeholder parser
command-name and argument propagation
export/result metadata propagation
unused-parameter display
```

### R.4 Export Dialect Result Schema Gate

Canonical node:

```text
8.9 StructuredExportResultSchema
```

Structured exports are state projections with dialect-specific schemas.

Required split:

```text
format-specific field names and nullability
sample arrays versus aggregate fields
parameter columns/objects
time-unit display versus stored-unit exceptions
sort/reference/comparison effects
stdout route versus file route
intermediate liveness versus final write
quoting/escaping/final-newline grammar
```

Rule:

```text
One export dialect or one output route does not close sibling dialects.
```

### R.5 Progress Observer Topology Gate

Canonical node:

```text
8.10 ProgressObserverTopology
```

Progress and live status are observer-topology surfaces.

Required split:

```text
style modes
TTY versus non-TTY
color and ANSI selection
child output interleaving
show-output routing
progress suppression
progress forcing
timing normalization in live display
```

### R.6 Command Execution I/O Lifecycle Graph Gate

Canonical node:

```text
7.11 CommandExecutionIOLifecycleGraph
```

Child execution must be modeled as a lifecycle graph.

Required split:

```text
default shell
custom shell
direct argv execution
shell calibration / missing-shell diagnostics
stdin file
stdout/stderr suppression
stdout/stderr pass-through
output file
prepare/conclude/setup/cleanup hooks
child failure warnings
ignore-failure policy
```

### R.7 Owner-Aware Monotonic Tail Gate

Canonical node:

```text
12.10 OwnerAwareMonotonicTailGate
```

At high score, a patch that wins tail rows but regresses previously green owners
must be rejected.

Required row:

```yaml
monotonic_tail_patch:
  base_candidate_ref: string
  proposed_patch_ref: string
  new_wins: int
  regressions: int
  regressed_owner_nodes: []
  preservation_sentinels: []
  disposition: accept | reject_non_monotone | split_and_retry
  branch_from_last_monotone_candidate: bool
```

Rule:

```text
Tail repair must branch from the last monotone candidate unless a deliberate
regression is explicitly accepted with owner, warrant, and replacement proof.
```

### R.8 Safe Generalization Boundary

Do generalize:

```text
public option reachability before product claims
statistical sample state as the central object
parameter sweep as a sublanguage
exports as state projections
progress as observer-topology surface
command execution as lifecycle graph
non-monotone tail patch rejection
```

Do not generalize:

```text
task-specific benchmark names
specific exact diagnostic strings
specific table wording
official row names
one-off fixture morphology
```

## S. Bottom Line

The general program ontology derived so far is not a list of edge cases. It is a layered account of what can become behavior-bearing in a program:

```text
control grammar
public modes
resources and routes
dialects and value domains
embedded transforms
identity and binding
lifecycle and state
rendering and side effects
diagnostics and exits
substrate and observation ecology
warrant and equivalence
orchestration and preservation
```

The safe abstraction is:

```text
Programs fail reconstruction when one of these layers is treated as a label,
example, or broad owner instead of an inherited subtree of obligations.
```

The next mature meta-program should therefore compile README/spec semantics into this numbered tree, inherit children deterministically, reconcile orthogonal semantic pools into the same nodes, and allow implementation only through owner-bounded batons with preservation and anti-replay gates.
