# ANM / D@1 Bounded Completion Pass v0

Status: bounded seam-tightening companion note.

Purpose:

- tighten the current ANM / `D@1` seed bundle at the seams;
- freeze one recommended cross-doc mapping posture;
- avoid reopening the architecture beyond the accepted v0 direction.

This note is written to be merged back into the connected family docs rather than treated as a new broad architecture fork.

## 1. Seam Diagnosis

### 1.1 What is already stable

The current seed bundle is already strong on the constitutional direction:

- markdown-native container with authoritative fenced `D@1` blocks;
- no prose obligation inference outside `D@1`;
- small typed clause language with modal heads, constructor sugar, qualifiers, bootstrap selectors, and split unknowns;
- first-class ledger posture with row identity and explicit preservation of applicability / observed outcome / effective verdict;
- first-class bootstrap predicate-contract artifact rather than evaluator folklore.

### 1.2 What seam gaps remain

The main remaining seam gaps are now narrower:

1. the family still lacks a first-class `D-IR` companion draft;
2. the result-model to ledger-state mapping is still implicit;
3. the predicate-contract artifact role is right but still under-shaped for implementation planning;
4. ledger lifecycle posture is not yet frozen tightly enough;
5. the exact artifact boundary matrix is still distributed across docs rather than stated compactly in one place.

The recommendation in this pass is to converge on one bounded answer for each of those seams and stop there.

## 2. Cross-Doc Freeze Note: Result-Set To Ledger Mapping

### 2.1 Freeze objective

The `D@1` result model and the ledger state model should join by an explicit mapping rule rather than by reader interpretation.

The key freeze is:

- `applicability` remains part of the evaluation model and must still be preserved into the ledger row;
- `effective_verdict` maps into the ledger's operational state vocabulary;
- selector zero-match remains distinct from `gated_off`.

### 2.2 Recommended mapping table

The table below assumes a clause instance was formed against a resolved subject.

If resolution fails before a `subject_ref` can be formed, the failure remains a blocking evaluator result for that clause/scope but does not create a ledger row, because the row identity `(clause semantic identity) x (resolved subject) x (scope snapshot)` cannot yet be formed.

| Evaluation posture | Create / update ledger row? | Ledger state | Closeout treatment | Notes |
|---|---:|---|---|---|
| `pass` | yes | `satisfied` | closed / non-blocking | active obligation evaluated and satisfied |
| `fail` | yes | `violated` | open / blocking | active obligation evaluated and failed |
| `waived` | yes | `waived` | closed / non-blocking | row persists; source-semantic exception and external waiver share closeout posture |
| `deferred` | yes | `deferred` | open by default; blocking unless gate profile explicitly allows | v0 does not add source-level deferral syntax |
| `gated_off` | yes, if subject resolved | `gated_off` | non-active / non-blocking / excluded from open counts | not the same as zero-match |
| `unknown_evidence` | yes | `blocked_unknown_evidence` | open / blocking | subject and binding were resolvable but admissible evidence was missing or inconclusive |
| `unknown_resolution` | yes, if subject resolved | `blocked_unknown_resolution` | open / blocking | if resolution failed before subject instantiation, keep it as a clause-scope blocking result rather than fabricating a ledger row |

### 2.3 Explicit answers to the seam questions

#### Does `gated_off` create a ledger row?

Yes, when a subject was actually resolved.

Reason:

- `gated_off` is a non-active instantiated obligation row, not the absence of an obligation instance;
- preserving it keeps the distinction between `ONLY_IF false` and selector zero-match;
- preserving it also allows later transitions from non-active to active without losing row continuity.

#### Does `excepted` create or update a ledger row as `waived`?

Yes.

The frozen mapping should be:

- `applicability = excepted`
- `observed_outcome = not_evaluated`
- `effective_verdict = waived`
- `ledger_state = waived`

That row should still preserve `latest_applicability = excepted` so it remains visible that the waived closeout posture came from a source-level `UNLESS` exception rather than from the ledger minting authority.

#### Is `gated_off` absence of obligation instance or a non-active instance?

For a resolved subject, it is a non-active instance.

Only selector zero-match is absence of instantiated obligation rows.

That is the clean seam line.

### 2.4 Zero-match rule

Selector zero-match remains separate from the mapping table above.

Recommended freeze:

- if selector expansion is zero-match and no subject was resolved, no obligation rows are created;
- the evaluator emits an explicit zero-match notice;
- zero-match is not rewritten into `gated_off`;
- zero-match is not rewritten into `unknown_resolution` on first instantiation.

### 2.5 `waived` boundary rule

The bundle should distinguish two different reasons for reaching the same closeout posture:

1. source-semantic exception via `UNLESS true`;
2. external waiver artifact joined during evaluation.

Both map to `ledger_state = waived`.

But:

- `latest_applicability = excepted` should be preserved when the source clause was excepted;
- `waiver_ref` should only be populated when an explicit external waiver artifact actually exists;
- the ledger must not mint waiver authority merely because a row is stored as `waived`.

### 2.6 `deferred` boundary rule

Recommended bounded v0 freeze:

- `deferred` may appear in result sets and ledger rows;
- it does not come from new source-level `D@1` syntax in v0;
- it should only arise when an explicit external deferral artifact or equally explicit evaluation input says so;
- `deferral_ref` should therefore be expected whenever `ledger_state = deferred`.

### 2.7 Recommended closeout posture

Recommended strict default closeout posture:

- `satisfied`: closed, non-blocking;
- `waived`: closed, non-blocking;
- `gated_off`: non-active, non-blocking, excluded from open-obligation counts;
- `violated`: open, blocking;
- `blocked_unknown_evidence`: open, blocking;
- `blocked_unknown_resolution`: open, blocking;
- `deferred`: open and blocking by default unless the gate profile explicitly allows deferrals.

This is the recommended family-wide default mapping.

## 3. Tightened Predicate-Contract Shape

### 3.1 Recommended normalized contract shape for v0

A bounded v0 predicate contract should look like:

```text
PredicateContract_v0 :=
  {
    predicate_id: string,
    owner_layer: "bootstrap",
    version: string,
    argument_schema: ContractArgument_v0[],
    required_evidence_kinds: string[],
    truth_conditions: TruthCondition_v0[],
    evidence_failure_conditions: FailureCondition_v0[],
    resolution_failure_conditions: FailureCondition_v0[],
    notes?: string
  }

ContractArgument_v0 :=
  {
    name: string,
    kind: "path_ref" | "literal_int" | "anchor_ref",
    required: boolean
  }

TruthCondition_v0 :=
  {
    result: true | false,
    when: string
  }

FailureCondition_v0 :=
  {
    result: "unknown_evidence" | "unknown_resolution",
    when: string
  }
```

The point of the shape is not to create a theorem prover.

The point is to make the bootstrap predicate semantics explicit enough that:

- the dialect can reference them;
- IR can point to them;
- checkers know what evidence kinds to emit;
- evaluators know what counts as true, false, evidence failure, and resolution failure.

### 3.2 Shape notes

Recommended meaning of the main fields:

- `predicate_id`: canonical semantic identity, such as `present` or `bind_to`;
- `owner_layer`: `bootstrap` for v0, keeping long-term O/E ownership deferred but visible;
- `version`: semantic contract version, not merely code package version;
- `argument_schema`: normalized argument signature used by IR validation;
- `required_evidence_kinds`: admissible evidence kinds that may support truth evaluation;
- `truth_conditions`: deterministic true/false conditions once resolution and evidence are adequate;
- `evidence_failure_conditions`: cases where binding resolved but admissible evidence was missing or inconclusive;
- `resolution_failure_conditions`: cases where subject/path/anchor binding could not be resolved safely;
- `notes`: non-semantic gloss only.

### 3.3 Mini-contract: `present(path)`

```yaml
predicate_id: present
owner_layer: bootstrap
version: v0
argument_schema:
  - name: path
    kind: path_ref
    required: true
required_evidence_kinds:
  - subject_snapshot
  - path_presence_observation
  - path_cardinality_observation
truth_conditions:
  - result: true
    when: subject binding resolved AND path resolves against subject AND cardinality(path) >= 1
  - result: false
    when: subject binding resolved AND path resolves against subject AND cardinality(path) == 0
evidence_failure_conditions:
  - result: unknown_evidence
    when: subject binding and path resolution succeeded BUT admissible evidence does not establish whether the path is present
resolution_failure_conditions:
  - result: unknown_resolution
    when: subject binding cannot be resolved
  - result: unknown_resolution
    when: path cannot be resolved safely against the bound subject shape
notes: >-
  `present(path)` asks whether at least one value exists at the referenced path.
  It does not require direct lexical carriage; that stronger boundary belongs to `explicit(path)`.
```

### 3.4 Mini-contract: `explicit(path)`

```yaml
predicate_id: explicit
owner_layer: bootstrap
version: v0
argument_schema:
  - name: path
    kind: path_ref
    required: true
required_evidence_kinds:
  - subject_snapshot
  - path_presence_observation
  - explicit_carriage_observation
truth_conditions:
  - result: true
    when: subject binding resolved AND path resolves against subject AND the value at the path is directly and explicitly carried by the authoritative subject evidence
  - result: false
    when: subject binding resolved AND path resolves against subject AND the value is absent
  - result: false
    when: subject binding resolved AND path resolves against subject AND the value exists only by defaulting, inheritance, reconstruction, implication, or other non-explicit derivation
evidence_failure_conditions:
  - result: unknown_evidence
    when: subject binding and path resolution succeeded BUT admissible evidence cannot determine whether the value was explicitly carried
resolution_failure_conditions:
  - result: unknown_resolution
    when: subject binding cannot be resolved
  - result: unknown_resolution
    when: path cannot be resolved safely against the bound subject shape
notes: >-
  `explicit(path)` is the bootstrap v0 predicate for direct carriage.
  It intentionally keeps inference, defaulting, and reconstruction out of the truth condition.
```

### 3.5 Mini-contract: `cardinality_eq(path, 1)`

```yaml
predicate_id: cardinality_eq
owner_layer: bootstrap
version: v0
argument_schema:
  - name: path
    kind: path_ref
    required: true
  - name: expected
    kind: literal_int
    required: true
required_evidence_kinds:
  - subject_snapshot
  - path_cardinality_observation
truth_conditions:
  - result: true
    when: subject binding resolved AND path resolves against subject AND cardinality(path) == expected
  - result: false
    when: subject binding resolved AND path resolves against subject AND cardinality(path) != expected
evidence_failure_conditions:
  - result: unknown_evidence
    when: subject binding and path resolution succeeded BUT admissible evidence does not establish exact cardinality
resolution_failure_conditions:
  - result: unknown_resolution
    when: subject binding cannot be resolved
  - result: unknown_resolution
    when: path cannot be resolved safely against the bound subject shape
notes: >-
  `EXACTLY_ONE path` lowers to `cardinality_eq(path, 1)` in v0.
```

### 3.6 Mini-contract: `bind_to(snapshot.identity)`

```yaml
predicate_id: bind_to
owner_layer: bootstrap
version: v0
argument_schema:
  - name: anchor
    kind: anchor_ref
    required: true
required_evidence_kinds:
  - subject_identity_observation
  - anchor_value_observation
  - binding_observation
truth_conditions:
  - result: true
    when: subject binding resolved AND anchor resolves to exactly one value AND admissible evidence establishes that the bound subject is explicitly bound to that same anchor value
  - result: false
    when: subject binding resolved AND anchor resolves to exactly one value AND admissible evidence establishes that the subject is unbound from that value or bound to a different value
evidence_failure_conditions:
  - result: unknown_evidence
    when: subject binding and anchor resolution succeeded BUT admissible evidence does not establish whether the binding holds
resolution_failure_conditions:
  - result: unknown_resolution
    when: subject binding cannot be resolved
  - result: unknown_resolution
    when: anchor cannot be resolved safely in the current scope
  - result: unknown_resolution
    when: anchor resolves non-uniquely where the contract requires a single anchor value
notes: >-
  In the common v0 form `bind_to(snapshot.identity)`, the contract asks whether the
  evaluated subject is bound to the current snapshot identity in admissible evidence.
```

### 3.7 Bounded v0 recommendation

The recommendation is to freeze this normalized contract shape in the bootstrap predicate-contract draft now.

That is enough to start implementation planning without broadening into a general logic or proof system.

## 4. Tightened Ledger Lifecycle

### 4.1 Recommended v0 posture

The recommended v0 ledger posture is:

```text
mutable current-state rows + audit linkage to immutable result sets
```

That means:

- one current row per obligation instance identity;
- rows are updated across runs;
- immutable run history remains in evaluator result sets;
- the ledger keeps stable current posture plus linkage back to run history.

This is more useful than append-only rows for closeout, and safer than a purely mutable table with no lineage.

### 4.2 When a row is first created

A ledger row is first created when a clause is instantiated against a resolved subject for a scope snapshot.

Recommended creation rule:

- create a row on first instantiated result for `pass`, `fail`, `waived`, `deferred`, `gated_off`, `unknown_evidence`, or `unknown_resolution`;
- do not create a row when selector expansion is zero-match and no subject instance exists;
- do not fabricate a row when `unknown_resolution` occurred before a `subject_ref` could be formed. Keep that failure in the evaluator result set as a clause-scope blocker.

### 4.3 When a row is updated

A row is updated when a later run over the same obligation identity produces any of:

- a new evaluation posture;
- a new evidence set / fact refs;
- a new owner;
- a new remediation ref;
- a new waiver ref;
- a new deferral ref.

The row should preserve the latest current posture while keeping linkage to the runs that established that posture.

### 4.4 Whether rows persist across runs

Yes.

That is the point of the ledger.

Rows should persist across runs for the same obligation identity.

A row must not be deleted merely because it became satisfied, waived, or gated off.

### 4.5 Scope snapshot posture

The row identity already includes `scope_snapshot`.

Recommended interpretation:

- repeated runs against the same scope snapshot update the same rows;
- a new scope snapshot creates a new row space;
- prior-snapshot rows remain historical and queryable under their original scope snapshot.

So legitimate subject disappearance due to a changed target snapshot should normally appear as a new scope, not as silent mutation of an old row.

### 4.6 What happens when a subject disappears from scope

Recommended bounded rule:

- if the subject disappears because a new scope snapshot is being evaluated, old rows remain untouched as history for the old scope and new rows are created only for subjects in the new scope;
- if a subject previously tracked for the same scope snapshot can no longer be reconciled in a later run, do not silently delete the row; update it to `blocked_unknown_resolution` because the system can no longer safely resolve the obligation instance it previously tracked.

This avoids silent row loss.

### 4.7 What happens when selector expansion is zero-match

Recommended bounded rule:

- on first evaluation for a clause/scope, selector zero-match creates no rows and emits a notice only;
- if earlier rows already existed for that clause/scope in the same scope snapshot and a later run goes zero-match, the system should reconcile those existing rows rather than dropping them silently;
- the recommended reconciliation posture is to update the unreconciled existing rows to `blocked_unknown_resolution`.

That keeps zero-match distinct from `gated_off` while still fail-closing later reconciliation drift.

### 4.8 Whether closed obligations remain queryable as history

Yes.

Closed rows remain queryable.

At minimum, the ledger should preserve:

- the row identity;
- the latest state;
- the latest run linkage;
- trace back to the underlying clause and scope.

### 4.9 Minimal audit-linkage recommendation

To support the lifecycle posture above, the row model should have at least:

- `first_seen_run`
- `latest_result_run`
- `updated_at`

If the family later wants richer lifecycle audit, it can add more fields.

But this minimum is enough for v0.

## 5. Compact Artifact-Boundary Matrix

| Artifact | Does | Must not do |
|---|---|---|
| ANM source markdown | container for readable prose plus authoritative fenced blocks | must not cause policy inference from prose outside `D@1` |
| `D@1` dialect source blocks | authoritative normative source clauses with selectors, assertions, and qualifiers | must not be confused with normalized IR, checker facts, or ledger state |
| normalized `D-IR` | normalized semantic projection of authoritative `D@1` clauses | must not store markdown formatting, checker facts, run verdicts, or ledger state |
| checker fact bundle | typed observed facts emitted by fact-only checkers | must not define policy semantics or mint obligations |
| evaluator result set | run-specific evaluation of `D-IR` against facts and contracts | must not replace the ledger's cross-run current-state role |
| obligation ledger | cross-run current-state projection of instantiated obligation rows | must not mint policy authority, waiver authority, or deferral authority by itself |
| bootstrap predicate contracts | explicit bootstrap semantics for predicate identity, arguments, required evidence, and failure posture | must not be hidden inside checker code or widened into a general theorem-proving language |

## 6. Recommended Next Minimal Bundle

If this arc is promoted, the next minimal stable bundle should be:

1. `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`
2. `docs/DRAFT_D1_DIALECT_SPEC_v0.md`
3. `docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md`
4. `docs/DRAFT_CHECKER_FACT_BUNDLE_SPEC_v0.md`
5. `docs/DRAFT_POLICY_EVALUATION_RESULT_SET_SPEC_v0.md`
6. `docs/DRAFT_POLICY_OBLIGATION_LEDGER_SPEC_v0.md`
7. `docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md`

Recommended posture for promotion:

- merge the result-to-ledger mapping freeze into the `D@1` dialect spec and ledger spec;
- merge the tightened contract shape into the predicate-contract draft;
- merge the lifecycle section into the ledger draft;
- merge the artifact-boundary matrix into the top-level ANM family doc or a short family index section;
- do not create unnecessary extra permanent seam-note docs once the family texts are updated.

That is the minimal promoted bundle that keeps the pipeline explicit without reopening the architecture broadly.
