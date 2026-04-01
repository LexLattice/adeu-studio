# Draft D1 Dialect Spec v0

Status: working bounded companion draft for authoritative normative markdown.

Authority posture:

- this document is a support/planning-seed artifact;
- it is not a lock doc;
- it does not authorize implementation by itself;
- it describes the intended bounded `D@1` dialect shape for a possible first slice.

Related inputs:

- `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`
- `docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v1.md`
- `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`

## 1. Direct Answer

`D@1` should be a small typed clause language embedded inside markdown.

The frozen v0 target should be:

- one modal head per clause;
- one assertion body per clause;
- optional qualifiers that attach to the clause;
- no general boolean algebra;
- no obligation inference from prose outside `D@1`.

## 2. Clause Constitution

The intended normalized clause form is:

```text
Clause :=
  {
    label?: ClauseLabel,
    modal: ModalHead,
    assertion: AssertionBody,
    qualifiers: Qualifier*
  }
```

For `D@1 v0`:

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

## 3. Live v0 Forms

### 3.1 Modal heads

Live in v0:

- `MUST`
- `MUST_NOT`

Reserved for later:

- `MAY`
- `SHOULD`

### 3.2 Assertion constructors

Live in v0:

- `REQUIRED path`
- `EXPLICIT path`
- `EXACTLY_ONE path`

These are assertion constructors, not modal heads.

Lowering targets are:

- `REQUIRED path` -> `present(path)`
- `EXPLICIT path` -> `explicit(path)`
- `EXACTLY_ONE path` -> `cardinality_eq(path, 1)`

### 3.3 Qualifiers

Live in v0:

- `ONLY_IF <condition>`
- `UNLESS <condition>`

Reserved for later:

- `BEFORE <anchor>`
- `AFTER <anchor>`

Qualifiers never lead a clause.

They attach to the clause headed by `MUST` or `MUST_NOT`.

## 4. Admissibility Rules

To keep v0 small and crisp:

- `MUST` may govern any v0 assertion form;
- `MUST_NOT` may govern atomic assertions only in v0;
- `MUST_NOT REQUIRED x`, `MUST_NOT EXPLICIT x`, and `MUST_NOT EXACTLY_ONE x` are
  rejected in v0;
- at most one `ONLY_IF` and one `UNLESS` may appear on a clause;
- no `AND`, `OR`, nesting, or quantifier language is admitted in v0;
- if more logic is needed, the author should split it into multiple clauses or use a
  named predicate contract.

## 5. Concrete Syntax

The intended block form is:

```md
:::D@1 id=<block-id>
ON <selector>
NOTE "<optional non-semantic gloss>"
@<clause-label> <MODAL> <ASSERTION> [ONLY_IF <condition>] [UNLESS <condition>]
:::
```

Canonical examples:

```md
@bind MUST bind_to(snapshot.identity)
@state MUST REQUIRED snapshot.staleness_state
@explicit MUST EXPLICIT snapshot.identity
@carrier MUST EXACTLY_ONE primary_carrier_class
@no_override MUST_NOT lexical_naming.override_higher_precedence == true
```

## 6. Qualifier Semantics

Qualifier behavior should be frozen explicitly.

### 6.1 `ONLY_IF`

For `MUST φ ONLY_IF ψ`:

- if `ψ == true`:
  - clause remains `active`
  - evaluate `φ`
- if `ψ == false`:
  - `applicability = gated_off`
  - `observed_outcome = not_evaluated`
  - `effective_verdict = gated_off`
- if `ψ == unknown_evidence`:
  - `applicability = active`
  - `observed_outcome = unknown_evidence`
  - `effective_verdict = unknown_evidence`
- if `ψ == unknown_resolution`:
  - `applicability = active`
  - `observed_outcome = unknown_resolution`
  - `effective_verdict = unknown_resolution`

### 6.2 `UNLESS`

For `MUST φ UNLESS ε`:

- if `ε == true`:
  - `applicability = excepted`
  - `observed_outcome = not_evaluated`
  - `effective_verdict = waived`
- if `ε == false`:
  - clause remains `active`
  - evaluate `φ`
- if `ε == unknown_evidence`:
  - `applicability = active`
  - `observed_outcome = unknown_evidence`
  - `effective_verdict = unknown_evidence`
- if `ε == unknown_resolution`:
  - `applicability = active`
  - `observed_outcome = unknown_resolution`
  - `effective_verdict = unknown_resolution`

## 7. Selector Expansion Policy

Selector behavior should also be frozen explicitly.

### 7.1 Bootstrap selector ownership

In v0, `ON` consumes bootstrap string selectors only.

Example:

```text
ON artifact.emitted[*]
```

Long-term O-owned selector handles remain deferred.

### 7.2 Zero-subject policy

The v0 default should be:

- `zero_match_policy = allow_empty_with_notice`

Meaning:

- zero resolved subjects is not by itself a policy failure;
- no obligation instances are created for that selector expansion;
- the compiler/evaluator emits an explicit zero-match notice;
- later stricter population policies remain future work.

This avoids silently treating zero subject populations as ordinary success while also
avoiding overloading zero-match into `unknown_resolution`.

## 8. Comparison, Negation, And List Equality

### 8.1 `MUST_NOT`

In v0, the canonical negative comparison form is:

```text
MUST_NOT x == true
```

The normalized IR may preserve modal negation directly rather than rewriting every
clause into a positive predicate form.

The important freeze is semantic, not authoring prettiness:

- negative constructor forms remain rejected;
- negative atomic assertions remain allowed.

### 8.2 Ordered list equality

For list comparisons such as:

```text
MUST classification.precedence == [a, b, c, d]
```

v0 equality should mean:

- ordered equality;
- exact length equality;
- no extra items;
- no missing items;
- exact symbol equality, not fuzzy or set-like comparison.

## 9. Result Model

The result model should stay typed and split:

```text
Result :=
  {
    applicability: active | gated_off | excepted,
    observed_outcome: not_evaluated | pass | fail | unknown_evidence | unknown_resolution,
    effective_verdict: pass | fail | waived | deferred | gated_off | unknown_evidence | unknown_resolution
  }
```

The key v0 distinction is:

- `unknown_evidence` = subject/predicate was resolvable, but evidence was missing or
  inconclusive;
- `unknown_resolution` = selector/path/predicate/checker binding could not even be
  resolved safely.

## 10. Result-To-Ledger Mapping Freeze

The result model and the obligation ledger should join by explicit mapping rather than
reader interpretation.

The key rule is:

- `applicability` remains part of the evaluation model and must be preserved into the
  ledger row when a row exists;
- `effective_verdict` maps into the ledger's operational state vocabulary;
- selector zero-match remains distinct from `gated_off`.

### 10.1 Mapping table

The table below assumes a clause instance was formed against a resolved subject.

If resolution fails before a `subject_ref` can be formed, the failure remains a
blocking evaluator result for that clause/scope but does not create a ledger row.

| Evaluation posture | Create / update ledger row? | Ledger state |
|---|---:|---|
| `pass` | yes | `satisfied` |
| `fail` | yes | `violated` |
| `waived` | yes | `waived` |
| `deferred` | yes | `deferred` |
| `gated_off` | yes, if subject resolved | `gated_off` |
| `unknown_evidence` | yes | `blocked_unknown_evidence` |
| `unknown_resolution` | yes, if subject resolved | `blocked_unknown_resolution` |

### 10.2 `gated_off` versus zero-match

For a resolved subject:

- `gated_off` is a non-active instantiated obligation row.

For selector zero-match:

- no subject is resolved;
- no row is created on first instantiation;
- the evaluator emits a zero-match notice only.

### 10.3 `excepted` versus `waived`

The recommended freeze is:

- `applicability = excepted`
- `observed_outcome = not_evaluated`
- `effective_verdict = waived`

The ledger may therefore store `ledger_state = waived` while still preserving
`latest_applicability = excepted`.

## 11. Non-Goals

`D@1 v0` should not implement yet:

- `MAY`
- `SHOULD`
- `AT_LEAST`
- `AT_MOST`
- `FORBIDDEN`
- `BEFORE`
- `AFTER`
- source-level `DEFERRED`
- imported O-owned selector handles
- richer boolean condition language

## 12. Machine-Checkable Seed Summary

```json
{
  "schema": "d1_dialect_seed@1",
  "artifact": "docs/DRAFT_D1_DIALECT_SPEC_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_seed",
  "one_modal_head_per_clause_required": true,
  "one_assertion_body_per_clause_required": true,
  "live_modal_heads": [
    "MUST",
    "MUST_NOT"
  ],
  "live_assertion_constructors": [
    "REQUIRED",
    "EXPLICIT",
    "EXACTLY_ONE"
  ],
  "live_qualifiers": [
    "ONLY_IF",
    "UNLESS"
  ],
  "must_not_constructor_forms_forbidden": true,
  "bootstrap_string_selectors_required": true,
  "zero_match_policy_default": "allow_empty_with_notice",
  "ordered_list_equality_required": true,
  "split_unknown_model_required": true,
  "result_to_ledger_mapping_freeze_required": true,
  "gated_off_distinct_from_zero_match_required": true,
  "reserved_not_implemented": [
    "MAY",
    "SHOULD",
    "AT_LEAST",
    "AT_MOST",
    "FORBIDDEN",
    "BEFORE",
    "AFTER",
    "DEFERRED"
  ]
}
```
