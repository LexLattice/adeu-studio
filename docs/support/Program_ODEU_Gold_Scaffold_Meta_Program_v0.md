# Program ODEU Gold Scaffold Meta-Program v0

Status: support note.

Authority layer: support only.

Scope: reusable meta-program for ProgramBench-style program reconstruction tasks where the target is a gold scaffold and probe contract, not an immediate code patch.

This note generalizes the `psampaz__go-mod-outdated.bb79367` postmortem into a reusable ODEU program-reconstruction workflow. It is not tied to that task. The calibration case taught one central lesson:

```text
program behavior is not only semantic I/O behavior.
program behavior can include byte, process, dependency, and source-shape surfaces.
```

The meta-program exists to prevent a reconstructor from stopping at semantic branch realization when the benchmark actually requires exact external contract realization and implementation-shape preservation.

---

## 0. Core claim

A ProgramBench gold scaffold should compile a program’s observed behavior into a locked D-ledger before implementation begins.

The D-ledger must ask, for every behavior:

```text
What is the behavior?
Which surface exposes it?
What evidence authorizes it?
What branch matrix pins it?
What probe or invariant detects drift?
What D-depth is required to realize it?
What failure mode would a competent coder agent likely introduce?
```

The resulting scaffold is not merely a task summary. It is an artifact-mediated control program for a coder agent.

A gold scaffold may prescribe implementation-shape obligations, but it should
not collapse into final implementation source. Bounded illustrative snippets are
allowed when they clarify an observable surface; full source code belongs to
the implementation phase.

---

## 1. General vocabulary

### 1.1 D-ledger

A D-ledger is the locked obligation ledger for a reconstruction task. Each row binds:

```text
obligation_id
behavior statement
surface class
branch class
evidence authority
probe/invariant
implementation obligation
negative-path posture
conflict status
D-depth requirement
completion-gate status
```

A row is not closed until a coder can say exactly how it is implemented, how it is tested, and which evidence authorizes it.

### 1.2 Semantic branch realization

Semantic branch realization means the implementation preserves the intended domain behavior at a tolerant level.

Examples:

```text
filters direct vs indirect modules
returns nonzero when CI detects updates
parses multiple JSON objects
skips main modules
sorts or renders the right logical rows
```

Semantic realization is necessary but not sufficient in benchmark reconstruction tasks.

### 1.3 Exact external contract realization

Exact external contract realization means the implementation preserves externally observable process surfaces.

Examples:

```text
stdout bytes
stderr bytes
exit code
help text stream
CLI parser grammar
invalid flag error wording
JSON decoder error text
log prefix behavior
table borders, alignment, width, and trailing newlines
```

A semantically equivalent implementation can fail this layer.

### 1.4 Implementation-shape obligation

An implementation-shape obligation is a behavior exposed through source layout, package identity, dependency identity, or runtime stack/reflection artifacts.

Examples:

```text
module path in panic stack
package/type name in Go JSON errors
line number in stack trace
nil dereference vs explicit panic
stdlib parser error wording
dependency version controlling table rendering
interpreter/runtime/toolchain version
```

These obligations are easy to miss because they are not “business logic.” In compatibility benchmarks, they may be first-class behavior.

### 1.5 Observable package/type/module identity

Any package name, type name, import path, module name, dependency version, or toolchain version is observable when it can appear in:

```text
error text
panic stack
reflection output
serialized type name
help/usage text
binary invocation path
lockfile/tool output
```

When observable, identity belongs in the scaffold, not in the coder’s discretion.

### 1.6 Byte/process/source parity

The gold scaffold should distinguish three parity levels:

| Parity | What must match | Typical probes |
|---|---|---|
| Byte parity | exact stdout/stderr text | golden hashes, byte snapshots, Unicode width cases |
| Process parity | exit code, signal/panic class, stream routing, order of emit vs exit | rc snapshots, stderr/stdout split, CI-after-render probes |
| Source parity | stack file/line, package/type/module identity, dependency/toolchain identity | source scanners, panic snapshots, error-string probes |

### 1.7 Compatibility-bug preservation

Some expected behavior is a bug in the original program. A gold scaffold must preserve it if the evaluator observes it.

Examples:

```text
panic instead of graceful validation
wrong branch ordering
filter quirk
malformed input logged but still rc0
usage text printed to a surprising stream
```

The scaffold must mark these rows as compatibility obligations, not invite the coder to “fix” them.

### 1.8 Conflict-branch isolation

When clean reference probes and evaluator-derived expectations disagree, the scaffold must isolate the conflict rather than globalize it.

Bad:

```text
All malformed JSON should be nonzero.
```

Better:

```text
Clean reference branch: invalid JSON logs to stderr and exits rc0.
Evaluator-conflict branch: exact executable-behavior fixture `{not json}\n` expects nonzero.
Compatibility stance: preserve generic branch; add a narrow conflict row only if targeting that evaluator surface.
```

### 1.9 Probe-contract preservation

A probe contract is not advisory. If a scaffold says the coder must match 101 probes, then any nonzero mismatch count is a stop condition.

```text
semantic progress + failed probes != ready for evaluator
```

This is the central D-realization lesson from the calibration run.

A coder-agent final message is not proof of obligation satisfaction. Only
probes, scanners, runtime evidence, or reviewed artifacts can close D-ledger
rows.

### 1.10 D-threshold

D-threshold is the minimum executor depth needed to descend a locked scaffold into object code without obligation drift.

A useful scale:

| Level | Capability | Program reconstruction meaning |
|---:|---|---|
| D0 | Visible-spec sketch | Implements README-level happy path. |
| D1 | Semantic branch realization | Handles main domain branches and ordinary filters. |
| D2 | Negative-path category realization | Emits broad diagnostics/panics/rc classes. |
| D3 | Exact external contract realization | Matches byte output, stderr/stdout routing, exit codes, parser quirks, log text. |
| D4 | Implementation-shape invariant realization | Preserves module path, package/type names, source line, dependency/toolchain identity, compatibility bugs. |
| D5 | Self-verifying ledger execution | Binds every scaffold row to probes/invariants and refuses to proceed with mismatches. |

Most failed “almost solved” reconstructions fail at D3/D4, not D1.

D-threshold is measured for an artifact/scaffold pair, not for a model globally.
The same model can be above threshold for one scaffolded task and below
threshold for another.

---

## 2. Program behavior surface taxonomy

Every behavior row must be classified into exactly one primary surface and any secondary surfaces.

If one row cannot be assigned a single primary surface, split it. Rows that mix
multiple primary surfaces usually become too broad to probe or enforce.

### 2.1 Semantic surface

Logical behavior independent of exact bytes:

```text
business/domain transformations
filtering and ordering
state transitions
branch selection
computed values
rendered row inclusion/exclusion
```

### 2.2 External process surface

Everything visible through the executable boundary:

```text
stdout bytes
stderr bytes
exit code
signal/panic code
stdout/stderr ordering
prompt/help behavior
CLI parser behavior
stdin stream contract
environment-sensitive behavior
filesystem side effects
```

### 2.3 Library/protocol surface

Behavior inherited from a dependency, standard library, or protocol:

```text
stdlib JSON errors
flag parser grammar
logging prefix format
table rendering package output
regex engine behavior
time parser wording
shell quoting behavior
```

A coder should usually use the same library rather than approximate it, unless the scaffold proves the library is not needed.

### 2.4 Implementation-shape surface

Behavior visible because the runtime exposes implementation details:

```text
package/type/module identity
file paths
source line numbers
stack frames
function names
exception classes
runtime/toolchain version
binary name / argv[0]
```

### 2.5 Negative-path surface

Behavior activated by malformed, missing, boundary, or conflicting inputs:

```text
invalid JSON shape
invalid timestamps
unknown flags
invalid booleans
missing required nested fields
empty input
filtered-out invalid rows
panic-inducing nil/missing fields
```

Negative paths should not be represented as a single “error handling” row. They need branch matrices.

---

## 3. Evidence authority posture

A gold scaffold must label the strongest source for each behavior. The standard classes are:

| Evidence class | Meaning | Use rule |
|---|---|---|
| `visible_spec` | README, task prompt, visible files, documented CLI help | Clean first-attempt admissible. |
| `clean_probe` | Reference executable behavior observed before implementation/evaluator feedback | Clean first-attempt admissible, scoped to exact probe shape. |
| `source_archaeology` | Upstream source or included source available to the reconstructor | Use only if actually visible or separately authorized. |
| `local_submission_probe` | Submission-vs-reference comparator result before official eval | Useful for coder miss vs scaffold gap, not clean reference by itself. |
| `post_eval_failure` | Official evaluator failure names/messages/diffs | Postmortem-only; never launder as clean evidence. |
| `postmortem_inference` | Inference after comparing specs, probes, submissions, and eval failures | Postmortem-only; must stay labeled. |
| `conflict_record` | Clean probe and evaluator evidence disagree | Requires explicit conflict ledger and compatibility stance. |

Evidence rows must preserve exact scope:

```text
a probe authorizes the observed input/argv/environment shape,
not every superficially similar branch.
```

Diagnostic evidence does not promote a behavior to settled readiness. This mirrors the broader ODEU rule that diagnostics do not unlock controls.

---

## 4. Required scaffold artifacts

A gold scaffold produced by this meta-program should contain these artifacts.

### 4.1 Evidence Authority Ledger

For every nontrivial behavior, record:

```yaml
obligation_id: BEH-001
behavior: "..."
surface: semantic | process | library | implementation_shape | negative_path
strongest_evidence: visible_spec | clean_probe | source_archaeology | local_submission_probe | post_eval_failure | postmortem_inference | conflict_record
evidence_refs:
  - file/path/test/probe/source line
scope: "input/argv/env/runtime shape where this is known"
posture: settled | uncertain | conflict | postmortem_only
```

### 4.2 Canonical Behavior Taxonomy

The taxonomy should cover all program-specific behaviors plus these generic surfaces:

```text
input stream format
input object schema
input type errors
CLI flags/options/aliases
positional arguments
filtering and ordering
rendering and formatting
stdout/stderr split
exit code taxonomy
logging behavior
panic/exception behavior
source/package/type identity
dependency/toolchain identity
invalid/malformed input behavior
empty input behavior
side effects, if any
```

### 4.3 Branch Matrices

Branch matrices force vertical descent. Minimum generic matrices:

```text
input_shape_matrix
schema_field_presence_matrix
nested_object_matrix
invalid_value_matrix
filter_order_matrix
render_order_matrix
exit_order_matrix
cli_flag_form_matrix
help_usage_matrix
unknown_option_matrix
stdout_stderr_matrix
panic_exception_matrix
implementation_identity_matrix
dependency_toolchain_matrix
side_effect_matrix, if the program mutates files/state
```

The matrix is incomplete if it only lists happy paths.

### 4.4 Negative Behavior Inventory

Separate:

```text
must fail
must panic
must log
must return nonzero
must return zero despite error
must render odd-looking output
must tolerate missing/empty values
must ignore/filter invalid-looking rows before validation
```

This prevents overbroad “validation fixes.”

### 4.5 Probe Contract

A probe contract is a mechanical set of reference observations and submission comparisons.

Each probe row should include:

```yaml
probe_id: PROBE-001
purpose: "..."
stdin_fixture: "..."
argv: []
env: {}
expected_stdout_class: exact | empty | regex | hash | semantic_only
expected_stderr_class: exact | empty | regex | category
expected_exit_code_class: exact | category | signal
pins_obligations:
  - BEH-001
  - BEH-014
evidence_authority: clean_probe | post_eval_failure | postmortem_inference
comparison_mode: byte | stream | process | source | semantic
```

The default comparison mode should be byte/process exact unless the scaffold explicitly justifies a weaker class.

Probe strength should be recorded explicitly:

| Strength | What it can close |
|---|---|
| `semantic` | Logical behavior only. |
| `category` | Broad class such as diagnostic vs panic vs usage. |
| `byte` | Exact stdout/stderr bytes or approved dynamic-normalized bytes. |
| `process` | Exit code, signal/panic class, stream split, ordering. |
| `source_shape` | Package/type/module identity, stack frame, line number, dependency/toolchain identity. |

A probe cannot close an obligation requiring a stronger parity class. For
example, a stderr category probe cannot close a byte-exact usage-text
obligation, and a semantic table probe cannot close a Unicode-width rendering
obligation.

### 4.6 Implementation Obligations

Implementation obligations are not code patches. They are constraints on the coder agent.

Common obligation classes:

```text
data model / schema obligations
package/type/module identity obligations
parser/library obligations
stdout/stderr obligations
exit ordering obligations
rendering obligations
panic/log/error obligations
dependency/toolchain obligations
source-line/layout obligations
compatibility-bug preservation obligations
conflict-branch isolation obligations
```

### 4.7 Conflict and Ambiguity Ledger

Conflicts must be explicit.

```yaml
conflict_id: CONFLICT-001
clean_probe_behavior: "..."
post_eval_expected_behavior: "..."
affected_tests_or_probes:
  - "..."
likely_explanations:
  - wrapper/invocation mismatch
  - evaluator-specific fixture
  - hidden official expectation
  - reference-probe overgeneralization
recommended_stance: "..."
compatibility_strategy: none | narrow_shim | evaluator_targeted | unresolved
remaining_risk: low | medium | high
```

Never turn a conflict into a vague recommendation.

### 4.8 Coder-Agent Failure Mode Map

For each family, list the likely competent-agent miss and the scaffold control.

Examples:

| Failure mode | Why it happens | Control |
|---|---|---|
| Semantic-equivalent table renderer | Coder treats table as presentation | golden byte snapshots + dependency obligation |
| Cleaner panic handling | Coder fixes compatibility bug | panic-shape row + source-line probe |
| Hand-written parser | Coder implements visible flags only | native parser obligation + invalid/unknown flag matrix |
| Evidence laundering | Coder treats post-eval behavior as clean | evidence ledger + conflict posture |
| Probe noncompliance | Coder submits with mismatches | zero-mismatch completion gate |

### 4.9 Gold Completion Gate

A scaffold is not ready for implementation until:

```text
[ ] every behavior row has an evidence label
[ ] every uncertain behavior is probed or marked unresolved
[ ] every high-risk branch family has a matrix
[ ] every exact surface has byte/process/source probes
[ ] every compatibility bug is explicitly named
[ ] every dependency/toolchain identity risk is locked or declared irrelevant
[ ] every conflict has a compatibility stance
[ ] every implementation obligation maps to at least one probe/invariant
[ ] D-threshold routing is declared
[ ] no unresolved branch silently defaults to “reasonable” behavior
```

A submission is not ready for official eval until:

```text
[ ] local probe mismatch count is zero, unless each remaining mismatch is an accepted conflict row
[ ] source-shape scanners pass
[ ] byte/process parity passes
[ ] obligation coverage checker passes
[ ] conflict-branch isolation probes pass
[ ] no broad repair regressed ordinary branches
```

---

## 5. Meta-program phases

### Phase 0: Intake and authority declaration

Input packet classes:

| File class | What it can authorize | What it cannot authorize |
|---|---|---|
| Visible task packet | clean visible behavior | hidden evaluator behavior |
| Reference executable | clean observed behavior under probed inputs | unprobed branch generalization |
| Upstream/source files | implementation-shape and library choices if visible/authorized | evaluator-specific wrappers unless present |
| Run summaries | outcome and failure family hints | exact behavior without logs/diffs |
| Eval JSON | post-eval failure evidence | clean first-attempt evidence |
| Probe scripts/logs | clean or local comparator evidence, depending on timing | hidden branches not probed |
| Submission source | coder behavior and mutation analysis | target truth by itself |
| Prior scaffold | inherited obligations | proof that obligations were executed |
| Failure cluster notes | postmortem search guidance | clean authority |

The first artifact should state:

```text
authority_posture: clean_reconstruction | postmortem_scaffold_review | depth_threshold_diagnosis | evaluator_targeted_compatibility
```

### Phase 1: Program-class identification

Classify the program before listing branches.

Examples:

```text
CLI table renderer
stream parser
compiler/linter wrapper
stateful filesystem mutator
HTTP service
batch transformer
interactive REPL
```

Each class has default high-risk surfaces. For a CLI table renderer, assume:

```text
stdout bytes
stderr bytes
exit code
CLI grammar
table width
Unicode width
dependency rendering
logging/panic surfaces
```

### Phase 2: Evidence ledger construction

Build the first D-ledger before coding. Do not write implementation obligations yet. First classify what is known, unknown, and postmortem-derived.

Required outputs:

```text
settled behavior rows
uncertain behavior rows
postmortem-only rows
conflict rows
unprobed high-risk rows
```

### Phase 3: Behavior taxonomy and branch matrices

For each taxonomy area, ask:

```text
What are the valid branches?
What are the invalid branches?
What fields/options can be absent?
What branch ordering affects validation/render/exit?
Which rows are filtered before risky helpers run?
Which helper/library emits observable text?
Which behavior changes if a nested object is present?
```

Do not collapse cross-products prematurely. Most late failures come from missing cross-products, not missing top-level categories.

### Phase 4: Exact-surface forcing

For every behavior, classify whether it is:

```text
semantic_only
exact_stdout
exact_stderr
exact_exit
exact_parser
exact_log
exact_panic
exact_stack
exact_package_type
exact_dependency
exact_toolchain
exact_source_line
```

If exact, create at least one exact probe or scanner.

The forcing question:

```text
Could a cleaner or semantically equivalent implementation break this artifact?
```

If yes, the row is an exact-surface obligation.

### Phase 5: Probe contract generation

Generate probes in layers:

1. happy-path semantic probes;
2. exact rendering probes;
3. CLI flag/option form probes;
4. invalid/malformed input probes;
5. branch-order probes;
6. nested object cross-product probes;
7. source/identity probes;
8. conflict-isolation probes.

Each probe must pin one or more D-ledger rows. Orphan probes and orphan obligations are both errors.

### Phase 6: Probe reconciliation

Run reference probes, then reconcile:

```text
observed == expected:
  lock row as clean_probe if reference was clean.
observed != expected:
  update taxonomy or mark conflict.
probe flaky/env-sensitive:
  capture scope and weaken only with explicit reason.
reference/eval conflict:
  split branch into conflict ledger.
```

### Phase 7: Implementation obligation lock

Only after probe reconciliation, write coder obligations.

Obligations should be prescriptive enough to prevent likely drift:

```text
Use Go flag package, not manual parser.
Keep package name `mod` because JSON errors expose it.
Do not recover nil pointer panic; preserve panic shape.
Use tablewriter-compatible output; compare exact bytes.
Compute CI after filters and after rendering.
```

The exact wording changes by task, but the obligation must say what cannot be changed.

### Phase 8: D-threshold routing

Choose executor depth before implementation.

Routing rule:

| Scaffold / evaluator profile | Minimum executor depth |
|---|---:|
| few semantic branches, tolerant output | low / D1-D2 acceptable |
| many branches but non-byte exact | medium / D2-D3 |
| stdout/stderr/exit exact, CLI/parser/table/log surfaces | medium minimum / D3 |
| package/type/source-line/dependency identity visible | medium-high / D4 |
| scaffold gaps, probe design, clean/eval conflicts | high/xhigh / D4-D5 |
| implementation must stop on 0-probe mismatch gate | D5 discipline required regardless of model |

Do not send a low-depth executor into a D4/D5 scaffold without a deterministic checker and repair loop.

### Phase 9: Implementation and self-check

Implementation is not complete when code compiles. It is complete only when:

```text
probe contract passes
source scanners pass
D-ledger coverage passes
conflict-isolation probes pass
```

A local mismatch should be classified before official eval:

```text
coder miss
probe expectation wrong
scaffold gap
clean/evaluator conflict
nondeterministic environment issue
```

### Phase 10: Post-eval delta and scaffold refinement

When official eval fails, do not immediately patch code. First classify each failure:

```text
scaffold gap: behavior not in D-ledger
probe gap: behavior in ledger but not probed
implementation miss: behavior in ledger/probes but code failed
conflict row: clean reference and evaluator differ
D-realization failure: executor omitted/mutated known obligation
```

Then update the scaffold, not only the code.

---

## 6. Program ODEU D-ledger schema sketch

A concrete harness can store each obligation as JSON/YAML.

```yaml
schema: program_odeu_d_ledger_row@0
row_id: "ROW-CLI-UNKNOWN-001"
task_id: "..."
behavior_family: "cli_unknown_flag"
statement: "Unknown flags emit parser error and usage on stderr with rc2."
primary_surface: "external_process"
secondary_surfaces:
  - "library_protocol"
  - "byte_parity"
evidence:
  strongest: "clean_probe"
  refs:
    - kind: "probe"
      id: "CLI_UNKNOWN_001"
  scope: "argv=['--bogus']; empty stdin; reference executable"
branch_matrix_refs:
  - "cli_flag_form_matrix"
negative_posture: "must_fail_nonzero_stderr"
implementation_obligations:
  - "Use native parser or reproduce exact parser behavior."
  - "Do not swallow usage output."
probe_refs:
  - "CLI_UNKNOWN_001"
source_invariant_refs: []
conflict_status: "settled"
d_depth_required: "D3"
completion_status: "locked"
```

A source-shape row might look like:

```yaml
schema: program_odeu_d_ledger_row@0
row_id: "ROW-PANIC-LINE-001"
behavior_family: "panic_shape"
statement: "Rendered missing nested timestamp panics through nil dereference at the expected stack location."
primary_surface: "implementation_shape"
secondary_surfaces:
  - "external_process"
  - "source_parity"
evidence:
  strongest: "post_eval_failure"
  refs:
    - kind: "eval_test"
      id: "..."
  scope: "postmortem evaluator compatibility only"
negative_posture: "must_panic"
implementation_obligations:
  - "Preserve compatibility bug; do not replace with explicit validation."
probe_refs:
  - "PANIC_SHAPE_001"
source_invariant_refs:
  - "SRC_LINE_001"
conflict_status: "postmortem_only"
d_depth_required: "D4"
completion_status: "locked_for_evaluator_target"
```

---

## 7. D-realization checker

The checker should run before implementation handoff and again before official eval.

### 7.1 Obligation coverage check

Fail if:

```text
any behavior taxonomy row has no D-ledger row
any D-ledger row has no probe or invariant unless explicitly unprobeable
any probe pins no obligation
any implementation obligation has no detection path
```

### 7.2 Evidence laundering check

Fail if:

```text
post_eval_failure row is labeled clean_probe
postmortem_inference row is described as visible_spec
conflict row is presented as settled behavior
local submission behavior is treated as target truth
```

### 7.3 Exact byte/process check

Compare:

```text
stdout bytes
stderr bytes
exit code
signal/panic class
stdout/stderr ordering when relevant
trailing newlines
Unicode/display width
```

Use hashes for exact fixtures and regex only for explicitly dynamic portions, such as timestamps or temporary paths.

### 7.4 Source identity check

Scan or execute to verify:

```text
module path
package names
type names exposed in errors
function names in stack traces
source file names
source line numbers when required
dependency versions
toolchain/runtime version
```

### 7.5 Compatibility-bug mutation check

Fail if a known compatibility bug is “fixed” without a conflict ledger update.

Examples:

```text
panic converted to validation error
rc0 diagnostic converted to nonzero globally
unknown flag behavior normalized across conflict branches
filtered invalid row validated before filter
```

### 7.6 Conflict isolation check

For each conflict row, include:

```text
special branch probe
ordinary branch regression probe
non-overlap assertion
```

The checker should reject broad shims that solve one evaluator row by mutating many clean-reference rows.

### 7.7 Probe preservation check

Fail before official eval unless:

```text
all clean probes pass, or
remaining mismatches are explicitly accepted conflict rows with documented target stance
```

A useful report shape:

```text
obligations_total: 154
obligations_closed: 154
probe_count: 101
probe_mismatches: 0
source_invariant_failures: 0
conflict_rows: 3
conflict_rows_isolated: 3
ready_for_eval: true
```

---

## 8. D-threshold risk detector

Before assigning an executor, score the scaffold.

| Risk signal | Why it raises D-depth |
|---|---|
| exact stdout/stderr bytes | Requires D3 byte protocol discipline. |
| CLI parser edge forms | Requires D3 library/protocol preservation. |
| invalid input and malformed streams | Requires D2/D3 negative-path matrices. |
| panic stack checked | Requires D4 implementation-shape preservation. |
| package/type/module names exposed | Requires D4 cross-file identity control. |
| dependency output format checked | Requires D3/D4 dependency/toolchain pinning. |
| clean/evaluator conflicts | Requires D4/D5 conflict isolation. |
| long probe contract | Requires D5 self-verifying execution. |
| many branch cross-products | Requires D3+ obligation persistence. |
| compatibility bugs expected | Requires D4 “do not clean it up” discipline. |

Suggested route:

```text
risk_count <= 2 and no exact byte/source surfaces:
  low executor acceptable for draft.

risk_count 3-6 or exact byte/process surfaces present:
  medium executor minimum; probe checker required.

source-shape obligations, conflict shims, or hidden branch discovery:
  high/xhigh scaffold authoring or review; medium/high implementation.
```

---

## 9. Reusable ProgramBench workflow

### 9.1 First scaffold loop

```text
visible packet
  -> behavior taxonomy
  -> evidence ledger
  -> initial branch matrices
  -> clean reference probes
  -> probe reconciliation
  -> implementation obligations
  -> D-threshold route
  -> coder handoff only if completion gate passes
```

### 9.2 Implementation loop

```text
locked scaffold + probes
  -> implementation
  -> compile/build check
  -> probe comparison
  -> D-realization checker
  -> repair coder misses
  -> official eval only after zero local mismatches or accepted conflicts
```

### 9.3 Postmortem refinement loop

```text
official eval failures
  -> classify failure family
  -> distinguish scaffold gap vs coder miss vs conflict
  -> add branch/probe/obligation rows
  -> update D-threshold routing rule
  -> rerun on same and next task
```

### 9.4 Cross-task validation loop

To prove the meta-program works, run it on a new task:

```text
new task visible packet
  -> Program ODEU meta-program
  -> clean scaffold
  -> probes
  -> implementation
  -> local probe gate
  -> official eval
  -> failure delta
  -> scaffold/meta-program refinement
```

Measure:

```text
number of scaffold loops to solved
local probe mismatch count before eval
hidden failure family count
evidence laundering incidents
conflict rows discovered
D-threshold routing accuracy
executor cost vs pass rate
```

---

## 10. Meta-program output contract

A Program ODEU gold scaffold should include these sections.

### 10.1 Required sections

```text
1. Task and authority posture
2. Evidence Authority Ledger
3. Program behavior surface taxonomy
4. Branch matrices
5. Negative behavior inventory
6. Exact surface inventory
7. Implementation-shape inventory
8. Probe contract
9. Implementation obligations
10. Conflict and ambiguity ledger
11. Coder-agent failure mode map
12. D-threshold routing decision
13. D-realization checker plan
14. Gold completion gate
15. Post-eval refinement protocol
```

### 10.2 Required row-level fields

For each behavior row:

```text
behavior_id
behavior statement
surface class
branch family
evidence class
evidence scope
probe/invariant IDs
implementation obligation IDs
negative/tolerated posture
conflict status
D-depth requirement
completion status
```

### 10.3 Required non-goals

Every scaffold should state that it is not:

```text
a code patch
a model ranking
a claim of official benchmark authority beyond available evidence
a license to launder postmortem evidence into clean reconstruction evidence
a license to “improve” compatibility bugs
a replacement for local probe comparison
```

---

## 11. Calibration: go-mod-outdated lesson as generic pattern

The calibration case separated shallow and deep obligations.

### 11.1 Shallow-D obligations that transferred well

```text
module/update ontology
stream parsing as a semantic idea
filtering direct/indirect rows
CI exit as a semantic class
basic timestamp awareness
basic negative-path categories
```

These lifted performance far above a vanilla attempt because the scaffold carried program ontology.

### 11.2 Deep-D obligations that caused late failures

```text
byte-exact table rendering
Unicode/display width
stdout/stderr routing
exit code exactness
Go flag parser quirks
log.Print diagnostic surface
panic shape and source line
package/type/module identity
replace semantics by column, not by one generic “chosen module” helper
narrow evaluator/reference conflict isolation
zero-mismatch probe discipline
```

These are the obligations that must become general Program ODEU vocabulary.

### 11.3 General lesson

```text
A scaffold can be semantically correct and still fail as a D-ledger.
A coder can implement the program and still fail the artifact.
A gold scaffold must target the artifact, not only the program idea.
```

---

## 12. Practical prompt skeleton

Use this skeleton when invoking a scaffold author/reviewer.

```text
You are producing a Program ODEU gold scaffold, not code.

Authority posture:
  <clean_reconstruction | postmortem_gold_scaffold | depth_threshold_diagnosis>

Input packet:
  visible files:
    <paths>
  reference executable/probes:
    <paths>
  source/upstream files if authorized:
    <paths>
  previous submissions:
    <paths>
  eval JSON / failure clusters if postmortem:
    <paths>

Required work:
  1. Classify evidence authority for every behavior.
  2. Build behavior taxonomy across semantic, process, library, negative, and implementation-shape surfaces.
  3. Write branch matrices for every high-risk branch family.
  4. Identify exact byte/process/source obligations.
  5. Generate or extend the probe contract mechanically.
  6. Record conflicts without smoothing them over.
  7. Write implementation obligations but do not patch code.
  8. Produce a D-threshold routing decision.
  9. Produce a D-realization checker and completion gate.

Do not:
  - hide postmortem-derived behavior as clean evidence;
  - collapse exact process surfaces into semantic behavior;
  - recommend broad code changes instead of scaffold obligations;
  - declare ready while probe mismatches remain unclassified.
```

---

## 13. Program ODEU relation to broader ODEU harness doctrine

This meta-program should reuse existing ODEU harness doctrine rather than invent a separate lane.

Mapping:

| Program ODEU scaffold concept | Broader ODEU analogue |
|---|---|
| D-ledger row | operation/obligation ledger row |
| Probe contract | headless/fixture regression proof |
| Evidence authority | profile/evidence state |
| Exact-scope evidence | scoped runtime capability evidence |
| Conflict branch | boundary/transition conflict requiring explicit posture |
| D-realization checker | promotion gate / readiness resolver |
| Compatibility-bug preservation | diagnostic non-promotion + authority-preserving behavior lock |
| Probe-contract preservation | fixture/headless proof before promotion |
| Implementation-shape obligation | cross-artifact invariant / source identity gate |

The ODEU matrix rule “one canonical row owns each capability” should be copied here: one canonical D-ledger row should own each behavior obligation. Crosswalks may link related rows, but duplicate ownership creates drift.

Promotion posture also carries over:

```text
S: scaffold/spec row exists; no runtime promise.
B-P: partial implementation/scanner/probe exists.
B-F: local fixture/probe evidence passes.
B-R: real evaluator/runtime evidence passes under scoped conditions.
```

For ProgramBench, a behavior row should not move to `B-F` unless local probes or scanners prove it. It should not move to `B-R` unless official evaluator/runtime evidence supports it, with postmortem label preserved.

---

## 14. Stop conditions

Stop before implementation if any of these are true:

```text
behavior taxonomy has unclassified exact surfaces
branch matrices omit obvious cross-products
post-eval evidence is unlabeled or laundered
conflict rows are unresolved but treated as settled
probe contract is absent or not mechanically runnable
implementation-shape risks are ignored
D-threshold route is below scaffold risk level
completion gate has silent defaults
```

Stop before official eval if any of these are true:

```text
local probes fail without accepted conflict classification
stdout/stderr byte snapshots differ
exit code snapshots differ
source identity scanner fails
known compatibility bug was “fixed”
ordinary branch changed to satisfy a conflict branch
probe contract was edited to match the submission without evidence
```

Diagnostic experiments may intentionally bypass this official-eval gate to
measure a D-threshold or failure mode. Such runs must be labeled diagnostic and
must not be described as ready-for-eval runs.

---

## 15. Minimal v0 adoption checklist

For the next task, the first usable adoption is:

```text
[ ] create evidence ledger with clean/postmortem labels
[ ] list all program behavior surfaces, including exact process/source surfaces
[ ] write at least one branch matrix per high-risk family
[ ] generate clean reference probes before implementation
[ ] create exact byte/process/source parity probes where applicable
[ ] lock implementation obligations
[ ] route executor by D-threshold
[ ] run D-realization checker before official eval
[ ] classify every official failure into scaffold gap, probe gap, coder miss, conflict, or D-realization failure
[ ] update the meta-program with any new failure family
```

This v0 checklist is intentionally strict. The cost of extra scaffold work is lower than repeated loops caused by exact-surface blindspots.
