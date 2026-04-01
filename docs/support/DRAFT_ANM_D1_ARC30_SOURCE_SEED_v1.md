## A. Delta diagnosis

The previous ANM / D@1 draft was directionally correct but type-mixed in the places that matter most for long-term stability.

What was weak:

1. `MUST`, `EXPLICIT`, `EXACTLY_ONE`, `ONLY_IF`, and `UNLESS` were all described as “operators,” even though they belong to different semantic classes.
2. Clause syntax still tolerated the idea that qualifiers might behave like heads.
3. `EXPLICIT` was operationally useful, but its ADEU ownership was blurry: it is a deontic requirement over an epistemic property, not a purely deontic primitive.
4. Selectors were used directly without a clean statement of bootstrap vs long-term ownership.
5. The result model separated pass/fail from unknown only loosely.
6. The IR preserved origin labels, but not full diagnostic traceability.
7. The artifact set still lacked the live operational object that closeout and coding agents actually need.

This revision keeps the same architecture and scope, but tightens the constitution:

* **one modal head per clause**
* **one assertion body per clause**
* **qualifiers attach; they do not lead**
* **ordering constraints are a typed qualifier family**
* **`EXPLICIT` is an assertion constructor lowering to an epistemic predicate**
* **`EXACTLY_ONE` is an assertion constructor lowering to a cardinality predicate**
* **`REQUIRED` is an assertion constructor lowering to presence**
* **selectors are bootstrap-string now, O-owned handles later**
* **obligation ledger becomes first-class**

---

## 1. Revised clause constitution

The final typed clause model should be frozen as:

```text
Clause :=
  {
    label?: ClauseLabel,
    modal: ModalHead,
    assertion: AssertionBody,
    qualifiers: Qualifier*
  }
```

For **D@1 v0**, that becomes:

```text
ModalHead_v0 :=
  MUST
| MUST_NOT

AssertionBody_v0 :=
  AtomicAssertion
| Required(Path)
| Explicit(Path)
| ExactlyOne(Path)

AtomicAssertion :=
  PredicateCall
| Comparison

Qualifier_v0 :=
  OnlyIf(Condition)
| Unless(Condition)

Condition :=
  PredicateCall
| Comparison
```

And the reserved but not yet implemented qualifier subtype is:

```text
OrderingConstraint :=
  Before(Anchor)
| After(Anchor)
```

### Direct answers to the taxonomy questions

* **Is `MUST` the modal head?**
  Yes. In v0, `MUST` and `MUST_NOT` are the only live modal heads.

* **Is `EXPLICIT` a modal, a predicate, or authoring sugar?**
  In source syntax, `EXPLICIT` is an **assertion constructor**.
  In normalized semantics, it lowers to the epistemic predicate `explicit(path)`.

* **Is `EXACTLY_ONE` a top-level operator?**
  No. It is an **assertion constructor** lowering to `cardinality_eq(path, 1)`.

* **Are `ONLY_IF` / `UNLESS` / `BEFORE` / `AFTER` qualifiers rather than heads?**
  Yes. Always. In v0, only `ONLY_IF` and `UNLESS` are implemented. `BEFORE` and `AFTER` are reserved as the ordering-constraint qualifier family.

That is the clean model.

---

## 2. Revised architecture

The top-level architecture does not change. It is still a three-plane system.

### Authoring surface

A markdown-native source file, still readable as prose, still useful as architecture text.

* prose remains prose
* only fenced `D@1` blocks are normative
* `NOTE` is explanatory and non-semantic

### Semantic authority

`D@1` blocks compile into a typed D-AST, then into normalized D-IR.

The compiler is responsible for:

* validating clause shape
* lowering assertion constructors
* attaching trace metadata
* producing semantic hashes
* preparing obligation instantiation

### Checker execution

Checkers remain external and fact-oriented.

They do not decide compliance.
They produce typed observations with provenance.
The evaluator applies D semantics to those facts.

### Revised pipeline

```text
policy.adeu.md
  -> parse markdown + D@1 blocks
  -> typed D-AST
  -> normalized D-IR
  -> selector expansion / obligation instantiation
  -> obligation-ledger.json
  -> checker dispatch
  -> facts.json
  -> evaluator
  -> results.json
  -> ledger update
```

The important addition is the **obligation ledger** between compiled norms and ongoing implementation state.

---

## 3. Typed taxonomy and admissibility

## 3.1 Modal heads

### Live in v0

* `MUST`
* `MUST_NOT`

### Reserved for later

* `MAY`
* `SHOULD`

### Semantics

`MUST φ` means the assertion body `φ` must evaluate true.
`MUST_NOT φ` means `φ` must evaluate false.

`MUST` and `MUST_NOT` are the only clause heads in v0.

---

## 3.2 Assertion forms

Assertion forms are what the modal governs.

### Atomic assertions

These are not sugar.

* **Predicate call**
  Example: `bind_to(snapshot.identity)`

* **Comparison**
  Example: `snapshot.identity.visibility == repo_visible`

These survive into IR essentially unchanged.

### Assertion constructors

These are source-level structured forms that lower into normalized predicates.

* **`REQUIRED path`**
  Lowers to `present(path)`

* **`EXPLICIT path`**
  Lowers to `explicit(path)`

* **`EXACTLY_ONE path`**
  Lowers to `cardinality_eq(path, 1)`

These are not modal heads.
They are not free prose.
They are typed assertion constructors.

---

## 3.3 Qualifiers

Qualifiers modify clause applicability or exception handling.
They do not replace the head.

### Live in v0

* `ONLY_IF <condition>`
* `UNLESS <condition>`

### Reserved ordering qualifiers

* `BEFORE <anchor>`
* `AFTER <anchor>`

### Canonical semantics

`MUST φ ONLY_IF ψ`
means: the obligation is active only when `ψ` is true.

`MUST φ UNLESS ε`
means: the obligation is waived when exception condition `ε` is true.

These are clause qualifiers, never clause heads.

---

## 3.4 Admissibility rules for v0

To keep v0 hard and small:

* `MUST` may govern any v0 assertion form.
* `MUST_NOT` may govern only **atomic assertions** in v0.
* `MUST_NOT REQUIRED x`, `MUST_NOT EXPLICIT x`, and `MUST_NOT EXACTLY_ONE x` are rejected in v0.
* At most one `ONLY_IF` and one `UNLESS` may appear on a clause.
* No boolean `AND` / `OR` / nesting in v0 conditions.
* If more logic is needed, factor it into:

  * multiple clauses, or
  * a named atomic predicate.

This keeps the language governance-oriented rather than turning it into a general logic surface.

---

## 4. Revised concrete syntax

The surface stays markdown-native, but the clause line is now typed cleanly.

### Block form

```md
:::D@1 id=<block-id>
ON <selector>
NOTE "<optional non-semantic gloss>"
@<clause-label> <MODAL> <ASSERTION> [ONLY_IF <condition>] [UNLESS <condition>]
:::
```

### Canonical clause shape

```md
@label MUST bind_to(snapshot.identity)
@label MUST REQUIRED snapshot.staleness_state
@label MUST EXPLICIT snapshot.identity
@label MUST EXACTLY_ONE primary_carrier_class
@label MUST_NOT lexical_naming.override_higher_precedence == true
```

### What changed from the prior draft

* `ONLY_IF`, `UNLESS`, `BEFORE`, and `AFTER` are no longer in the head position.
* `EXPLICIT`, `REQUIRED`, and `EXACTLY_ONE` are no longer described as operators in the same class as `MUST`.
* a clause is structurally one head + one body + qualifiers

### Parsing discipline

The parser should reject:

* multiple modal heads
* headless qualifiers
* multiple assertion bodies
* constructor forms under `MUST_NOT`
* unimplemented reserved tokens in active syntax

Outside `D@1`, everything remains prose.

---

## 5. Revised minimal grammar sketch

```ebnf
document        ::= frontmatter? { markdown_chunk | d_block } ;

d_block         ::= ":::D@1" ws "id=" ident newline
                    on_line
                    note_line?
                    { clause_line }
                    ":::" newline? ;

on_line         ::= "ON" ws selector newline ;
note_line       ::= "NOTE" ws string newline ;

clause_line     ::= clause_label? modal ws assertion qualifier* newline ;

clause_label    ::= "@" ident ws ;

modal           ::= "MUST" | "MUST_NOT" ;

assertion       ::= atomic_assertion | assertion_constructor ;

atomic_assertion
                ::= predicate_call | comparison ;

assertion_constructor
                ::= "REQUIRED" ws path
                 |  "EXPLICIT" ws path
                 |  "EXACTLY_ONE" ws path ;

qualifier       ::= only_if | unless ;

only_if         ::= ws "ONLY_IF" ws condition ;
unless          ::= ws "UNLESS" ws condition ;

condition       ::= predicate_call | comparison ;

predicate_call  ::= ident "(" [ value { "," ws? value } ] ")" ;
comparison      ::= value ws comparator ws value ;

selector        ::= selector_token ;
path            ::= ident { "." ident | "[*]" } ;

value           ::= path | ident | string | integer | list ;
list            ::= "[" ws? value { "," ws? value } ws? "]" ;

comparator      ::= "==" | "!=" | "<" | ">" | "<=" | ">=" ;
ident           ::= letter { letter | digit | "_" | "-" } ;
```

### Lexically reserved for later, but not implemented in v0 grammar

* `MAY`
* `SHOULD`
* `AT_LEAST`
* `AT_MOST`
* `BEFORE`
* `AFTER`
* `DEFERRED`
* `FORBIDDEN`

`DEFERRED` is deliberately reserved but **not admitted into the v0 clause grammar**.
Its operational role exists in the ledger/result model before it exists as source syntax.

---

## 6. `EXPLICIT` as D-over-E

This needs to be stated with precision.

### Constitutional statement

`D@1` is allowed to say:

```md
@x MUST EXPLICIT snapshot.identity
```

But D does **not** own the truth conditions of explicitness.

What D owns is the normative claim:

* the subject is obliged to satisfy `explicit(snapshot.identity)`

What E owns, long-term, is the epistemic predicate:

* what counts as `explicit(path)`
* which carriers are approved
* which provenance modes count as direct
* what distinguishes direct representation from inference, defaults, reconstruction, or implication

### Bootstrap rule for v0

Because E@1 does not yet exist, D@1 v0 ships with an inlined bootstrap predicate contract:

```text
explicit(path)
```

with versioned semantics:

* **true**
  if an approved carrier for the subject was directly inspected and the value/state at `path` is directly carried there with provenance mode `direct`

* **false**
  if an approved authoritative carrier was inspected and:

  * the path is absent, or
  * the value/state is available only via inference, defaulting, reconstruction, or implication

* **unknown_evidence**
  if no approved carrier could be inspected, or inspection was inconclusive

* **unknown_resolution**
  if the subject/path cannot be resolved against the active selector/predicate environment

### Long-term ADEU ownership

In the long-term system:

* `explicit(path)` is an **E-layer predicate contract**
* D continues to write `MUST EXPLICIT path`
* the compiler lowers that to a predicate reference owned by E, not by D

So the source remains stable, but predicate ownership moves to the correct layer.

That is the clean D-over-E boundary.

---

## 7. Selector ownership

The previous proposal used selectors directly. That is acceptable in bootstrap mode, but it must be explicitly temporary.

### Bootstrap mode: live in v0

`ON artifact.emitted[*]`

Here, the selector is treated as a **bootstrap string selector**:

```json
{
  "selector_ref": {
    "kind": "bootstrap_string",
    "value": "artifact.emitted[*]"
  }
}
```

The compiler may carry it opaquely and rely on a local selector adapter / checker manifest to expand it.

### Long-term ADEU mode: deferred

Selectors become O-owned handles.

D does not define selector semantics.
D imports and consumes them.

Conceptually:

```md
IMPORT O adeu.core.entities@1 AS O

:::D@1 id=snapshot.binding
ON O.artifact.emitted
...
:::
```

or equivalent handle-based syntax.

### Boundary rule

* **v0**: D may consume raw selector strings.
* **later**: selector vocabulary, entity handles, and expansion contracts are owned by O registries.

This matters because selector resolution failure is not an evidence failure. It is a resolution failure.

---

## 8. Strengthened result-state model

The prior draft collapsed too much into “unknown.”
The revised model should separate:

* what was observed
* whether the clause applied
* what the effective closeout verdict is

### Result object shape

```text
Result :=
  {
    applicability: active | gated_off | excepted,
    observed_outcome: pass | fail | unknown_evidence | unknown_resolution,
    effective_verdict: pass | fail | waived | deferred | unknown_evidence | unknown_resolution
  }
```

### Meaning of each field

#### `applicability`

* `active`
  clause applied and was evaluated
* `gated_off`
  `ONLY_IF` condition was false
* `excepted`
  `UNLESS` condition was true

#### `observed_outcome`

This is the raw evaluation outcome before waiver/deferral overlays.

* `pass`
* `fail`
* `unknown_evidence`
* `unknown_resolution`

#### `effective_verdict`

This is what gates consume.

* `pass`
* `fail`
* `waived`
* `deferred`
* `unknown_evidence`
* `unknown_resolution`

### Why these distinctions matter

#### `fail`

Implementation or representation violates the policy.

#### `unknown_evidence`

The policy and subject were resolvable, but evidence was missing or inconclusive.
This is usually an instrumentation, carrier, or evidence-completeness problem.

#### `unknown_resolution`

The system could not even resolve the selector, path, predicate contract, or checker binding needed to evaluate.
This is a governance/toolchain integration defect and should be treated more severely than missing evidence.

#### `waived`

The obligation does not count as satisfied; it is inactive by exception.
Closeout should require a traceable waiver source.

#### `deferred`

The obligation is not satisfied now, but a time-bounded deferral exists.
It remains distinct from pass. It must carry owner, due state, and scope.

### Gate policy

Recommended v0 gate behavior:

* `pass` -> compliant
* `waived` -> nonblocking if traceable
* `fail` -> blocking
* `unknown_evidence` -> blocking
* `unknown_resolution` -> hard blocking
* `deferred` -> blocking in strict release gates; optionally allowed in managed non-release gates if an approved deferral record exists

Even when `deferred` is allowed, it must never be conflated with pass.

---

## 9. IR traceability and semantic hashing

The IR should preserve full traceability for diagnostics and stable operational references.

### Per-clause trace fields

Each normalized clause entry should preserve:

* `source_file`
* `block_id`
* `clause_label`
* `line_start`
* `line_end`
* optional `col_start`
* optional `col_end`

Column spans are worth preserving if the parser already has them cheaply.
They are useful for editors and precise diagnostics, but not required for v0 correctness.

### Recommended clause IR shape

```json
{
  "clause_ref": "adeu/policy/artifact-governance:snapshot.binding:explicit",
  "selector_ref": {
    "kind": "bootstrap_string",
    "value": "artifact.emitted[*]"
  },
  "modal": "MUST",
  "assertion": {
    "kind": "predicate_ref",
    "owner_layer": "E/bootstrap",
    "name": "explicit",
    "version": "0",
    "args": [
      { "kind": "path", "value": "snapshot.identity" }
    ]
  },
  "qualifiers": [],
  "trace": {
    "source_file": "policy.adeu.md",
    "block_id": "snapshot.binding",
    "clause_label": "explicit",
    "line_start": 7,
    "line_end": 7,
    "col_start": 1,
    "col_end": 39
  },
  "semantic_hash": "sha256:..."
}
```

### What should affect semantic hashes

A **clause semantic hash** should include only normalized clause semantics:

* canonical selector reference
* modal head
* normalized assertion
* normalized qualifiers
* referenced predicate contract identities / versions

### What should not affect semantic hashes

Do **not** include:

* source file path
* block id
* clause label
* line or column spans
* `NOTE`
* prose outside blocks
* whitespace
* markdown headings
* comments
* checker executable names
* checker manifest versions

### Use separate hashes

Use three distinct hashes, not one overloaded hash:

* **`source_hash`**
  exact bytes of the source file

* **`clause_semantic_hash`**
  normalized clause meaning

* **`runtime_bundle_hash`**
  optional bundle hash over semantic hashes plus runtime defaults and dispatch manifest identity

That separation prevents wording edits from pretending to be semantic changes.

---

## 10. Checker model, tightened but unchanged in principle

The checker model stays fact-oriented.

### Checker responsibilities

Checkers may:

* inspect carriers
* extract values
* report provenance
* report whether inspection was direct, indirect, or inconclusive
* emit typed facts

Checkers may **not** decide whether policy passed.

### Fact shape should carry provenance

Example:

```json
{
  "subject_ref": "artifact:dist/report.json",
  "fact_type": "value_observation",
  "path": "snapshot.identity",
  "values": ["git:7d9c1af"],
  "provenance": {
    "carrier": "dist/report.json.meta",
    "mode": "direct"
  },
  "checker": "artifact_manifest_reader@1"
}
```

The evaluator owns:

* constructor lowering
* truth evaluation
* qualifier handling
* verdict formation
* waiver / deferral overlay

That line stays sharp.

---

## 11. Obligation ledger artifact

This is the missing first-class artifact.

### Recommended artifact

`obligation-ledger.json`

### What it contains

The ledger contains **live obligation instances**, not just clause templates and not just run outputs.

Each row corresponds to:

```text
(clause semantic identity) × (resolved subject) × (work scope / target snapshot)
```

Recommended fields:

* `obligation_id`
* `clause_ref`
* `clause_semantic_hash`
* `subject_ref`
* `scope_snapshot`
* `latest_result_run`
* `latest_effective_verdict`
* `ledger_state`
* `owner`
* `required_evidence`
* `last_fact_refs`
* `waiver_ref`
* `deferral_ref`
* `remediation_ref`
* `updated_at`

### How it differs from IR

**IR** is normative and compiled. It contains clause meaning.
It does **not** contain:

* concrete subject instances
* owners
* remediation state
* waiver/deferral linkage
* latest run state

### How it differs from `results.json`

**`results.json`** is run-specific and mostly immutable.
It tells you what happened in one evaluation run.

The **ledger** is the operational stateful bridge across runs.
It answers:

* what obligations are currently open
* who owns them
* whether an exception or deferral exists
* what evidence is still missing
* what closeout remains

### Recommended ledger state vocabulary

* `satisfied`
* `violated`
* `waived`
* `deferred`
* `blocked_unknown_evidence`
* `blocked_unknown_resolution`

### How coding agents should use it

Coding agents should not start from raw policy text every time.
They should query the ledger for their target snapshot and filter to non-closed rows.

That gives them:

* exact clause ref
* source span
* normalized assertion
* affected subject
* latest evidence
* owner and remediation context

### How closeout should use it

Closeout should gate on the ledger’s current live state, not on prose and not on one-off checker output.

Recommended rule for strict closeout:

* no `violated`
* no `blocked_unknown_evidence`
* no `blocked_unknown_resolution`
* no `deferred` unless gate profile explicitly allows it

That is why the ledger must exist as a first-class artifact.

---

## 12. Harder v0 boundary

Freeze v0 smaller and harder.

### Implemented now

#### Modal heads

* `MUST`
* `MUST_NOT`

#### Assertion forms

* predicate call
* comparison
* `REQUIRED path`
* `EXPLICIT path`
* `EXACTLY_ONE path`

#### Qualifiers

* `ONLY_IF`
* `UNLESS`

#### Other live pieces

* markdown container with `D@1` fences
* bootstrap string selectors in `ON`
* normalized D-IR
* trace-rich IR spans
* fact-only checkers
* obligation ledger
* verdict split with `unknown_evidence` and `unknown_resolution`

### Reserved / explicitly deferred

#### Future modal heads

* `MAY`
* `SHOULD`

#### Future assertion constructors

* `AT_LEAST`
* `AT_MOST`
* `FORBIDDEN`

#### Future ordering qualifiers

* `BEFORE`
* `AFTER`

#### Future source-level disposition form

* `DEFERRED`

### Additional explicit v0 exclusions

* no general boolean algebra
* no `AND` / `OR`
* no nested clauses
* no quantifier language
* no imported O/E handles in source yet
* no negative constructor forms under `MUST_NOT`
* no source-level deferral syntax
* no attempt to formalize prose outside `D@1`

This is the right first implementation slice.

---

## 13. Revised end-to-end example

### 13.1 Source text

```md
01 :::D@1 id=snapshot.binding
02 ON artifact.emitted[*]
03 NOTE "All emitted artifacts bind to one explicit repo-visible snapshot identity."
04 @bind MUST bind_to(snapshot.identity)
05 @one MUST EXACTLY_ONE snapshot.identity
06 @visible MUST snapshot.identity.visibility == repo_visible
07 @explicit MUST EXPLICIT snapshot.identity
08 :::
09
10 :::D@1 id=snapshot.staleness
11 ON artifact.emitted[*]
12 NOTE "Stale-snapshot semantics must be explicit rather than implied."
13 @state MUST REQUIRED snapshot.staleness_state
14 @explicit MUST EXPLICIT snapshot.staleness_state
15 :::
16
17 :::D@1 id=schema.primary-carrier
18 ON schema.row[*]
19 NOTE "Schema rows carry one primary carrier class."
20 @carrier MUST EXACTLY_ONE primary_carrier_class
21 :::
22
23 :::D@1 id=classification.lexical-support
24 ON classifier.config
25 NOTE "Filename or naming-family cues are lower-precedence support only."
26 @support MUST lexical_naming.role == support
27 @rank MUST lexical_naming.rank == 4
28 @no_override MUST_NOT lexical_naming.override_higher_precedence == true
29 :::
30
31 :::D@1 id=classification.precedence
32 ON classifier.config
33 NOTE "Classification precedence is frozen."
34 @frozen MUST classification.precedence == [structural_signature, semantic_function, governance_role, lexical_naming]
35 :::
```

---

### 13.2 Parsed clause form

```yaml
blocks:
  - block_id: snapshot.binding
    selector: {kind: bootstrap_string, value: artifact.emitted[*]}
    clauses:
      - label: bind
        modal: MUST
        assertion:
          kind: predicate_call
          name: bind_to
          args: [snapshot.identity]
        qualifiers: []
      - label: one
        modal: MUST
        assertion:
          kind: constructor
          head: EXACTLY_ONE
          arg: snapshot.identity
        qualifiers: []
      - label: visible
        modal: MUST
        assertion:
          kind: comparison
          lhs: snapshot.identity.visibility
          cmp: eq
          rhs: repo_visible
        qualifiers: []
      - label: explicit
        modal: MUST
        assertion:
          kind: constructor
          head: EXPLICIT
          arg: snapshot.identity
        qualifiers: []

  - block_id: snapshot.staleness
    selector: {kind: bootstrap_string, value: artifact.emitted[*]}
    clauses:
      - label: state
        modal: MUST
        assertion:
          kind: constructor
          head: REQUIRED
          arg: snapshot.staleness_state
        qualifiers: []
      - label: explicit
        modal: MUST
        assertion:
          kind: constructor
          head: EXPLICIT
          arg: snapshot.staleness_state
        qualifiers: []

  - block_id: schema.primary-carrier
    selector: {kind: bootstrap_string, value: schema.row[*]}
    clauses:
      - label: carrier
        modal: MUST
        assertion:
          kind: constructor
          head: EXACTLY_ONE
          arg: primary_carrier_class
        qualifiers: []

  - block_id: classification.lexical-support
    selector: {kind: bootstrap_string, value: classifier.config}
    clauses:
      - label: support
        modal: MUST
        assertion:
          kind: comparison
          lhs: lexical_naming.role
          cmp: eq
          rhs: support
        qualifiers: []
      - label: rank
        modal: MUST
        assertion:
          kind: comparison
          lhs: lexical_naming.rank
          cmp: eq
          rhs: 4
        qualifiers: []
      - label: no_override
        modal: MUST_NOT
        assertion:
          kind: comparison
          lhs: lexical_naming.override_higher_precedence
          cmp: eq
          rhs: true
        qualifiers: []

  - block_id: classification.precedence
    selector: {kind: bootstrap_string, value: classifier.config}
    clauses:
      - label: frozen
        modal: MUST
        assertion:
          kind: comparison
          lhs: classification.precedence
          cmp: eq
          rhs: [structural_signature, semantic_function, governance_role, lexical_naming]
        qualifiers: []
```

---

### 13.3 Normalized IR

Representative normalized entries:

```json
[
  {
    "clause_ref": "adeu/policy/artifact-governance:snapshot.binding:bind",
    "selector_ref": {"kind": "bootstrap_string", "value": "artifact.emitted[*]"},
    "modal": "MUST",
    "assertion": {
      "kind": "predicate_ref",
      "owner_layer": "bootstrap",
      "name": "bind_to",
      "version": "0",
      "args": [{"kind": "path", "value": "snapshot.identity"}]
    },
    "qualifiers": [],
    "trace": {
      "source_file": "policy.adeu.md",
      "block_id": "snapshot.binding",
      "clause_label": "bind",
      "line_start": 4,
      "line_end": 4
    },
    "semantic_hash": "sha256:sem-bind"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:snapshot.binding:one",
    "selector_ref": {"kind": "bootstrap_string", "value": "artifact.emitted[*]"},
    "modal": "MUST",
    "assertion": {
      "kind": "cardinality_eq",
      "path": "snapshot.identity",
      "count": 1
    },
    "qualifiers": [],
    "trace": {
      "source_file": "policy.adeu.md",
      "block_id": "snapshot.binding",
      "clause_label": "one",
      "line_start": 5,
      "line_end": 5
    },
    "semantic_hash": "sha256:sem-one"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:snapshot.binding:explicit",
    "selector_ref": {"kind": "bootstrap_string", "value": "artifact.emitted[*]"},
    "modal": "MUST",
    "assertion": {
      "kind": "predicate_ref",
      "owner_layer": "E/bootstrap",
      "name": "explicit",
      "version": "0",
      "args": [{"kind": "path", "value": "snapshot.identity"}]
    },
    "qualifiers": [],
    "trace": {
      "source_file": "policy.adeu.md",
      "block_id": "snapshot.binding",
      "clause_label": "explicit",
      "line_start": 7,
      "line_end": 7
    },
    "semantic_hash": "sha256:sem-explicit-id"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:snapshot.staleness:state",
    "selector_ref": {"kind": "bootstrap_string", "value": "artifact.emitted[*]"},
    "modal": "MUST",
    "assertion": {
      "kind": "presence",
      "path": "snapshot.staleness_state"
    },
    "qualifiers": [],
    "trace": {
      "source_file": "policy.adeu.md",
      "block_id": "snapshot.staleness",
      "clause_label": "state",
      "line_start": 13,
      "line_end": 13
    },
    "semantic_hash": "sha256:sem-staleness-required"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:schema.primary-carrier:carrier",
    "selector_ref": {"kind": "bootstrap_string", "value": "schema.row[*]"},
    "modal": "MUST",
    "assertion": {
      "kind": "cardinality_eq",
      "path": "primary_carrier_class",
      "count": 1
    },
    "qualifiers": [],
    "trace": {
      "source_file": "policy.adeu.md",
      "block_id": "schema.primary-carrier",
      "clause_label": "carrier",
      "line_start": 20,
      "line_end": 20
    },
    "semantic_hash": "sha256:sem-primary-carrier"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:classification.lexical-support:no_override",
    "selector_ref": {"kind": "bootstrap_string", "value": "classifier.config"},
    "modal": "MUST_NOT",
    "assertion": {
      "kind": "comparison",
      "lhs": {"kind": "path", "value": "lexical_naming.override_higher_precedence"},
      "cmp": "eq",
      "rhs": {"kind": "bool", "value": true}
    },
    "qualifiers": [],
    "trace": {
      "source_file": "policy.adeu.md",
      "block_id": "classification.lexical-support",
      "clause_label": "no_override",
      "line_start": 28,
      "line_end": 28
    },
    "semantic_hash": "sha256:sem-no-override"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:classification.precedence:frozen",
    "selector_ref": {"kind": "bootstrap_string", "value": "classifier.config"},
    "modal": "MUST",
    "assertion": {
      "kind": "comparison",
      "lhs": {"kind": "path", "value": "classification.precedence"},
      "cmp": "eq",
      "rhs": {
        "kind": "list",
        "values": [
          "structural_signature",
          "semantic_function",
          "governance_role",
          "lexical_naming"
        ]
      }
    },
    "qualifiers": [],
    "trace": {
      "source_file": "policy.adeu.md",
      "block_id": "classification.precedence",
      "clause_label": "frozen",
      "line_start": 34,
      "line_end": 34
    },
    "semantic_hash": "sha256:sem-precedence"
  }
]
```

---

### 13.4 Obligation ledger view

Assume evaluation scope snapshot `git:7d9c1af`.

```json
[
  {
    "obligation_id": "obl:01",
    "clause_ref": "adeu/policy/artifact-governance:snapshot.binding:bind",
    "clause_semantic_hash": "sha256:sem-bind",
    "subject_ref": "artifact:dist/report.json",
    "scope_snapshot": "git:7d9c1af",
    "latest_effective_verdict": "pass",
    "ledger_state": "satisfied",
    "owner": "artifact-emitter",
    "required_evidence": ["artifact_manifest_reader@1", "repo_snapshot_resolver@1"],
    "waiver_ref": null,
    "deferral_ref": null
  },
  {
    "obligation_id": "obl:02",
    "clause_ref": "adeu/policy/artifact-governance:snapshot.staleness:state",
    "clause_semantic_hash": "sha256:sem-staleness-required",
    "subject_ref": "artifact:dist/report.json",
    "scope_snapshot": "git:7d9c1af",
    "latest_effective_verdict": "fail",
    "ledger_state": "violated",
    "owner": "artifact-emitter",
    "required_evidence": ["artifact_manifest_reader@1"],
    "waiver_ref": null,
    "deferral_ref": null
  },
  {
    "obligation_id": "obl:03",
    "clause_ref": "adeu/policy/artifact-governance:snapshot.staleness:explicit",
    "clause_semantic_hash": "sha256:sem-explicit-staleness",
    "subject_ref": "artifact:dist/report.json",
    "scope_snapshot": "git:7d9c1af",
    "latest_effective_verdict": "fail",
    "ledger_state": "violated",
    "owner": "artifact-emitter",
    "required_evidence": ["artifact_manifest_reader@1"],
    "waiver_ref": null,
    "deferral_ref": null
  },
  {
    "obligation_id": "obl:04",
    "clause_ref": "adeu/policy/artifact-governance:snapshot.binding:bind",
    "clause_semantic_hash": "sha256:sem-bind",
    "subject_ref": "artifact:dist/legacy.csv",
    "scope_snapshot": "git:7d9c1af",
    "latest_effective_verdict": "unknown_evidence",
    "ledger_state": "blocked_unknown_evidence",
    "owner": "artifact-emitter",
    "required_evidence": ["artifact_manifest_reader@1", "repo_snapshot_resolver@1"],
    "waiver_ref": null,
    "deferral_ref": null
  },
  {
    "obligation_id": "obl:05",
    "clause_ref": "adeu/policy/artifact-governance:schema.primary-carrier:carrier",
    "clause_semantic_hash": "sha256:sem-primary-carrier",
    "subject_ref": "schema.row:user.tags",
    "scope_snapshot": "git:7d9c1af",
    "latest_effective_verdict": "fail",
    "ledger_state": "violated",
    "owner": "schema-author",
    "required_evidence": ["schema_row_scanner@1"],
    "waiver_ref": null,
    "deferral_ref": null
  },
  {
    "obligation_id": "obl:06",
    "clause_ref": "adeu/policy/artifact-governance:classification.precedence:frozen",
    "clause_semantic_hash": "sha256:sem-precedence",
    "subject_ref": "classifier.config",
    "scope_snapshot": "git:7d9c1af",
    "latest_effective_verdict": "pass",
    "ledger_state": "satisfied",
    "owner": "classifier-maintainer",
    "required_evidence": ["classifier_config_reader@1"],
    "waiver_ref": null,
    "deferral_ref": null
  }
]
```

This is the bridge the earlier design was missing.

---

### 13.5 Example checker facts

```json
[
  {
    "subject_ref": "artifact:dist/report.json",
    "fact_type": "value_observation",
    "path": "snapshot.identity",
    "values": ["git:7d9c1af"],
    "provenance": {"carrier": "dist/report.json.meta", "mode": "direct"},
    "checker": "artifact_manifest_reader@1"
  },
  {
    "subject_ref": "artifact:dist/report.json",
    "fact_type": "value_observation",
    "path": "snapshot.identity.visibility",
    "values": ["repo_visible"],
    "provenance": {"carrier": "dist/report.json.meta", "mode": "direct"},
    "checker": "artifact_manifest_reader@1"
  },
  {
    "subject_ref": "artifact:dist/report.json",
    "fact_type": "binding_observation",
    "binding_kind": "repo_snapshot",
    "targets": ["git:7d9c1af"],
    "checker": "repo_snapshot_resolver@1"
  },
  {
    "subject_ref": "artifact:dist/report.json",
    "fact_type": "value_observation",
    "path": "snapshot.staleness_state",
    "values": [],
    "provenance": {"carrier": "dist/report.json.meta", "mode": "direct_absence"},
    "checker": "artifact_manifest_reader@1"
  },
  {
    "subject_ref": "artifact:dist/legacy.csv",
    "fact_type": "carrier_read",
    "carrier": "dist/legacy.csv.meta",
    "outcome": "inconclusive",
    "reason": "sidecar missing",
    "checker": "artifact_manifest_reader@1"
  },
  {
    "subject_ref": "schema.row:user.email",
    "fact_type": "value_observation",
    "path": "primary_carrier_class",
    "values": ["scalar:string"],
    "provenance": {"carrier": "schema/user.yaml", "mode": "direct"},
    "checker": "schema_row_scanner@1"
  },
  {
    "subject_ref": "schema.row:user.tags",
    "fact_type": "value_observation",
    "path": "primary_carrier_class",
    "values": ["list:string", "scalar:string"],
    "provenance": {"carrier": "schema/user.yaml", "mode": "direct"},
    "checker": "schema_row_scanner@1"
  },
  {
    "subject_ref": "classifier.config",
    "fact_type": "value_observation",
    "path": "classification.precedence",
    "values": [[
      "structural_signature",
      "semantic_function",
      "governance_role",
      "lexical_naming"
    ]],
    "provenance": {"carrier": "classifier/config.yaml", "mode": "direct"},
    "checker": "classifier_config_reader@1"
  }
]
```

---

### 13.6 Final evaluator verdicts

```json
[
  {
    "clause_ref": "adeu/policy/artifact-governance:snapshot.binding:bind",
    "subject_ref": "artifact:dist/report.json",
    "applicability": "active",
    "observed_outcome": "pass",
    "effective_verdict": "pass",
    "message": "artifact binds to repo-visible snapshot git:7d9c1af"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:snapshot.binding:one",
    "subject_ref": "artifact:dist/report.json",
    "applicability": "active",
    "observed_outcome": "pass",
    "effective_verdict": "pass",
    "message": "exactly one snapshot.identity observed"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:snapshot.binding:explicit",
    "subject_ref": "artifact:dist/report.json",
    "applicability": "active",
    "observed_outcome": "pass",
    "effective_verdict": "pass",
    "message": "snapshot.identity is directly carried"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:snapshot.staleness:state",
    "subject_ref": "artifact:dist/report.json",
    "applicability": "active",
    "observed_outcome": "fail",
    "effective_verdict": "fail",
    "message": "required path snapshot.staleness_state is absent"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:snapshot.staleness:explicit",
    "subject_ref": "artifact:dist/report.json",
    "applicability": "active",
    "observed_outcome": "fail",
    "effective_verdict": "fail",
    "message": "staleness semantics are not explicitly carried; implication does not satisfy EXPLICIT"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:snapshot.binding:bind",
    "subject_ref": "artifact:dist/legacy.csv",
    "applicability": "active",
    "observed_outcome": "unknown_evidence",
    "effective_verdict": "unknown_evidence",
    "message": "binding carrier inspection inconclusive"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:schema.primary-carrier:carrier",
    "subject_ref": "schema.row:user.email",
    "applicability": "active",
    "observed_outcome": "pass",
    "effective_verdict": "pass",
    "message": "exactly one primary_carrier_class observed"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:schema.primary-carrier:carrier",
    "subject_ref": "schema.row:user.tags",
    "applicability": "active",
    "observed_outcome": "fail",
    "effective_verdict": "fail",
    "message": "EXACTLY_ONE(primary_carrier_class) violated: found 2"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:classification.lexical-support:no_override",
    "subject_ref": "classifier.config",
    "applicability": "active",
    "observed_outcome": "pass",
    "effective_verdict": "pass",
    "message": "lexical naming does not override higher-precedence signals"
  },
  {
    "clause_ref": "adeu/policy/artifact-governance:classification.precedence:frozen",
    "subject_ref": "classifier.config",
    "applicability": "active",
    "observed_outcome": "pass",
    "effective_verdict": "pass",
    "message": "classification precedence matches frozen ordered sequence"
  }
]
```

This shows the revised semantics doing the right thing:

* explicit snapshot binding passes when directly carried
* implied staleness does not satisfy `EXPLICIT`
* schema ambiguity fails `EXACTLY_ONE`
* lexical naming remains support-only
* inconclusive evidence stays `unknown_evidence`, not silently coerced to pass or fail

---

## 14. Final recommendation

Freeze the design now around this stricter constitution.

### Freeze now

Freeze these as the ANM / D@1 core:

* **clause = one modal head + one assertion body + optional qualifiers**
* modal heads live: `MUST`, `MUST_NOT`
* assertion constructors live: `REQUIRED`, `EXPLICIT`, `EXACTLY_ONE`
* qualifiers live: `ONLY_IF`, `UNLESS`
* `EXPLICIT` lowers to `explicit(path)` and is explicitly treated as **D invoking an E-owned predicate**, with bootstrap inline semantics until E exists
* selectors in v0 are bootstrap string selectors
* result model distinguishes `unknown_evidence` from `unknown_resolution`
* IR preserves full source trace
* obligation ledger is a first-class artifact

### Keep bootstrap-only

These should be explicitly marked temporary:

* raw string selectors in `ON`
* inline bootstrap contract for `explicit(path)`
* local selector adapters
* local predicate registry for non-O/non-E-owned predicate refs like `bind_to`

### Keep deferred

Do not implement these in v0:

* `MAY`
* `SHOULD`
* `AT_LEAST`
* `AT_MOST`
* `BEFORE`
* `AFTER`
* `FORBIDDEN`
* source-level `DEFERRED`
* O-layer selector imports
* E-layer registry-owned explicitness contracts
* richer boolean condition language

The right move is not to widen the language.
It is to harden the constitution.

The converged recommendation is therefore:

**retain ANM as the markdown-native container, revise D@1 into a strictly typed single-head clause language, ship a small v0 with constructor lowering and an obligation ledger, and leave selector ownership and explicitness ownership visibly bootstrap-only until O and E exist.**
