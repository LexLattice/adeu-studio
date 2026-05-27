# General Program Ontology Derived So Far

Authority layer: `support / synthesis`

Scope: This note abstracts the general program ontology that has emerged from the recent reconstruction work. It is intentionally **not** a task-specific repair plan. It focuses on reusable ontology classes, node responsibilities, closure rules, and safe generalizations that can be promoted into future HOB-style numbered catalogs.

Primary source inputs:

```text
principled_recursive_odeu_meta_program_experimental_v29.md
test_group_feature_ontology_probe_mapping.md
```

The task-specific examples that motivated these abstractions should remain in their task artifacts. The reusable layer is the ontology structure below.

---

## 0. Core Thesis

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
Π  = probes, checkers, reference observations, source-postmortem facts
Σ  = target substrate / runtime / packaging environment
Ω* = best warranted program ontology
```

Central judgment:

```text
W ; Π ; Σ ⊢ Cᴡ : Ω*
```

The ontology work exists to avoid proving the wrong theorem. Many observed failures across tasks were not implementation bugs in the narrow sense; they were cases where the theorem statement was under-derived, the witness bundle was not equivalent across substrates, or the orchestrator moved phases without a legal transition proof.

---

## 1. Kernel Operators

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

## 2. Status Vocabulary

The following statuses are reusable across tasks.

```text
candidate_inferred
  The node was inferred from visible semantics, not yet reference-locked.

public_schema_discovered
  Public help/schema/scout behavior exposed the node.

conceptually_probe_ready
  The branch has a named discriminator and probe shape, but no locked oracle yet.

reference_locked
  Reference/public observation has locked expected behavior for the declared scope.

source_tail_needed
  Public/conceptual probes narrowed the owner, but exact target library/source behavior is still required.

covered_by_conceptual_probe
  A conceptual/reference probe matrix discovered and bounded the behavior family before source-tail repair.

covered_by_source_tail
  The family required source-informed dialect/library equivalence after conceptual probes narrowed the owner.

scoped_green_with_official_sibling_tail
  The local subtree is useful and preservation-worthy, but official pressure still names unclosed siblings under the same owner.

gold_tail_not_closed
  The global theorem is stable, but explicit gold-tail public dialect/byte-surface leaves remain open.

remaining_hidden_tail
  The behavior owner is known and public/source parity is reached on available fixtures, but one hidden fixture still differs.

rejected_broad_patch
  A patch class was tried and invalidated by regressions or zero wins; it becomes a future constraint.
```

The most important promotion rule:

```text
scoped green != gold closed
local green != target-substrate proof
source parity on visible fixtures != hidden-tail solved
rejected patch != useless evidence
```

---

## 3. General Numbered Ontology Skeleton

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

Each class below is general. Task-specific names should be attached later as children, not baked into this catalog.

---

## 1. Invocation and Control-Plane Grammar

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

## 2. Public Schema, Mode Families, and Discoverability

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

---

## 3. Resource and Route Topology

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

## 4. Input Dialect, Reader, and Value-Domain Grammar

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

## 5. Transform and Embedded-Language Substrate

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

## 6. Subject, Identity, Binding, and Aggregation

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

## 7. State, Lifecycle, Mutation, and Row Universe

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

## 8. Output Router, Renderer, and Byte Grammar

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

If the target program uses a different library, host output is not the oracle. The reconstruction must translate, emulate, replace, or source-postmortem the target surface.

---

## 9. Diagnostics, Fatal Gates, and Channel/Exit Contracts

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

## 10. Runtime Substrate, Dependency, and Observation Ecology

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

---

## 11. Methodological Equivalence, Warrant, and Evidence Authority

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
source_postmortem
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

## 12. Orchestrator, Handoff, Anti-Replay, and Preservation Governance

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

## 13. Orthogonal Semantic Pools

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

## 14. General Discovery Methods by Layer

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
| L8 source tail | library/dialect exactness still differs | source-postmortem with impact cones |
| L9 gold tail | small explicit tail | row-level ownership exactness + microgrammar closure |

---

## 15. Safe Generalizations From the Recent Task

The following are safe to promote generally.

### 15.1 Test namespace is not ontology

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

### 15.2 Feature labels are not sublanguage closure

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

### 15.3 Source-tail often means library equivalence

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

### 15.4 Rejected patches are positive constraints

A rejected patch class is a learned impossibility or risk cone. It should be carried into future batons as:

```text
forbidden_patch_class
regression sentinel source
required alternative owner
impact-cone warning
```

### 15.5 Score movement must be node-owned

Raw score deltas are insufficient. Each delta should be mapped to:

```text
node closed
owner touched
sentinels preserved
new regressions
remaining sibling tail
method used
```

### 15.6 Hidden tails are layer-specific

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

## 16. Canonical Node Record

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
```

---

## 17. HOB Inheritance Rule

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

## 18. Worker-Handoff Rule

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

## 19. General Program Classes And Triggered Subtrees

The ontology should be activated by program class.

### 19.1 CLI tool

Triggers:

```text
1 Invocation grammar
2 Public schema
8 Projection surfaces
9 Diagnostics/channel/exit
11 Methodological equivalence
12 Handoff/anti-replay
```

### 19.2 Resource-processing tool

Adds:

```text
3 Resource topology
4 Input dialects
6 Identity/binding
7 Lifecycle/row universe
10 Substrate/dependency
```

### 19.3 Language-over-resource tool

Adds:

```text
5 Embedded language substrate
6 Subject binding and aggregation
7 Mutation/lifecycle
8 Downstream output contracts
```

### 19.4 Renderer-heavy tool

Prioritizes:

```text
8 Byte grammar
9 Diagnostics paired with projection
10 Terminal/substrate if interactive
12 Anti-replay byte-snapshot guard
```

### 19.5 Long-running / interactive / networked tool

Adds:

```text
10 Observation ecology
10 Observable success contract
7 teardown/liveness lifecycle
12 orchestrator resource gate
```

### 19.6 Config/stateful tool

Adds:

```text
2 Mode-as-program
3 Config resource topology
7 Persistent state/mutation
9 Config diagnostics
10 dependency/substrate
```

---

## 20. What Should Not Be Generalized

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

## 21. Proposed General Catalog v0.1

A compact version suitable for future numbered HOB promotion:

```text
1. ControlPlane
  1.1 InvocationShape
  1.2 FlagTokenGrammar
  1.3 ControlPrecedence
  1.4 StreamExitContract
  1.5 CompatibilityOverlay

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

4. InputDialectAndValueDomain
  4.1 PhysicalGrammar
  4.2 SchemaBearingGrammar
  4.3 ValueDomain
  4.4 ReaderLocalLifecycle
  4.5 DialectDiagnosticGrammar
  4.6 ReaderWriterPairClosure
  4.7 HostLibraryParserSurface

5. TransformSubstrate
  5.1 EmbeddedLanguageRecognition
  5.2 ResourceBindingInsideLanguage
  5.3 TransformSemantics
  5.4 SelectorSublanguage
  5.5 MutationSemantics
  5.6 TypeCoercionAndFunctionSemantics

6. SubjectIdentityBindingAggregation
  6.1 RawVsDisplayIdentity
  6.2 SchemaAndColumnIdentity
  6.3 BindingMap
  6.4 AggregationDenominators
  6.5 TypeProvenanceAuthority

7. LifecycleStateMutation
  7.1 StartupToTeardownSequence
  7.2 FatalGatePrecedence
  7.3 RowUniverse
  7.4 PersistentState
  7.5 SideEffectLifecycle

8. OutputRouterRenderer
  8.1 OutputRoute
  8.2 FormatPrecedenceOverlay
  8.3 RendererByteGrammar
  8.4 DownstreamConsumerContract
  8.5 RendererLibraryEquivalence

9. DiagnosticsExitChannels
  9.1 DiagnosticOwnership
  9.2 ChannelExitContract
  9.3 DiagnosticPrecedence
  9.4 SuggestionGrammar
  9.5 HostLibraryDiagnosticTranslation

10. RuntimeSubstrateObservationEcology
  10.1 TargetSubstrateEquivalence
  10.2 OptionalDependencyContract
  10.3 ObservationEcology
  10.4 ObservableSuccessContract
  10.5 PackageArtifactParity

11. WarrantEquivalenceAuthority
  11.1 EquivalenceJudgment
  11.2 EvidenceClass
  11.3 PromotionAuthority
  11.4 SourceTailAuthorization
  11.5 HiddenTailAttribution

12. OrchestrationHandoffPreservation
  12.1 PhaseTransitionLaw
  12.2 WorkerBaton
  12.3 AntiReplayGate
  12.4 PreservationSentinelImport
  12.5 PatchImpactCone
  12.6 RejectedPatchLedger
```

---

## 22. Bottom Line

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
