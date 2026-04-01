# Draft D1 Normalized IR Spec v0

Status: working bounded companion draft for authoritative normative markdown.

Authority posture:

- this document is a support/planning-seed artifact;
- it is not a lock doc;
- it does not authorize implementation, schema release, or runtime behavior by itself;
- it defines the intended bounded shape of the normalized D-IR artifact that sits between source `D@1` and evaluation.

Related inputs:

- `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`
- `docs/DRAFT_D1_DIALECT_SPEC_v0.md`
- `docs/DRAFT_POLICY_OBLIGATION_LEDGER_SPEC_v0.md`
- `docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md`

## 1. Direct Answer

The ANM / `D@1` family needs a first-class normalized IR artifact.

That artifact should be `D-IR`.

`D-IR` is the normalized semantic projection of authoritative `D@1` clauses.

It should be:

- semantic rather than operational;
- typed rather than markdown-shaped;
- stable enough to support evaluation and ledger identity;
- explicitly distinct from source markdown, checker facts, evaluator result sets, and the obligation ledger.

## 2. Core Thesis

The family boundary should be frozen as:

```text
ANM source markdown
  -> authoritative D@1 source blocks
  -> normalized D-IR
  -> checker fact bundles
  -> evaluator result sets
  -> obligation ledger
```

`D@1` is the authoritative source dialect.

`D-IR` is the compiled semantic form used as the evaluator's policy input.

The key separation is:

- source markdown is for authoring and trace;
- `D-IR` is for normalized clause meaning;
- checker fact bundles are for observed facts only;
- result sets are for run-specific evaluation outcomes;
- the ledger is for cross-run obligation state.

## 3. What D-IR Is And Is Not

### 3.1 What D-IR is

`D-IR` is:

- the normalized semantic representation of source `D@1` clauses;
- the artifact that preserves clause meaning after source-level sugar is lowered;
- the artifact that the evaluator consumes together with checker facts and predicate contracts;
- a stable bridge artifact for clause identity, subject-instantiation, and result/ledger joins.

### 3.2 What D-IR is not

`D-IR` is not:

- source markdown;
- source `D@1` text;
- checker output;
- evaluator output;
- the obligation ledger;
- operational execution state;
- a general-purpose logic language.

More explicitly:

- `D-IR` is semantic, not operational state;
- `D-IR` is not source markdown;
- `D-IR` is not checker output;
- `D-IR` is not the ledger.

## 4. Relationship To Neighbor Artifacts

### 4.1 Relation to source `D@1`

`D@1` is authoritative source.

`D-IR` is its normalized semantic projection.

That means:

- only authoritative `D@1` content may compile into `D-IR`;
- prose outside `D@1` does not appear in `D-IR` as obligation semantics;
- source-level constructors such as `REQUIRED`, `EXPLICIT`, and `EXACTLY_ONE` are lowered into normalized assertion forms in `D-IR`;
- source trace remains linkable, but source formatting is not itself the IR.

### 4.2 Relation to checker facts

Checker fact bundles provide observed facts.

`D-IR` provides the policy semantics that tell the evaluator what to ask about those facts.

So:

- checker facts do not define clause meaning;
- `D-IR` does not inline observed fact payloads;
- `D-IR` may reference predicate contracts and selector refs that constrain what fact kinds are admissible;
- resolved evidence and fact payloads remain outside the IR.

### 4.3 Relation to evaluator results

Evaluator result sets are run-specific outputs of evaluating:

```text
D-IR x checker facts x predicate contracts x scope
```

So:

- `D-IR` is an input to evaluation, not an evaluation result;
- `D-IR` does not contain `pass`, `fail`, `waived`, `deferred`, `gated_off`, or `unknown_*` outcomes;
- result sets should carry the clause and subject join keys derived from `D-IR`;
- multiple result sets may exist over the same unchanged `D-IR`.

### 4.4 Relation to the obligation ledger

The obligation ledger is the cross-run operational projection of instantiated obligations.

`D-IR` is the source-semantic basis for those obligations, but it is not itself the ledger.

So:

- `D-IR` should provide the stable clause identity inputs used by the ledger;
- `D-IR` should not store live owners, remediation state, waiver refs, deferral refs, or latest closeout posture;
- the ledger may join back to `D-IR` for clause meaning and source trace;
- the ledger must not become a substitute for `D-IR`.

## 5. Artifact Role

The bounded v0 role of `D-IR` is:

1. preserve the normalized meaning of authoritative `D@1` clauses;
2. erase source-only sugar that should not survive into evaluation semantics;
3. preserve enough trace metadata to connect a normalized clause back to source;
4. provide stable clause-level semantic hashes and refs for result-set and ledger joins;
5. remain cleanly separate from fact bundles, result sets, and ledger rows.

That is enough for the first family slice.

It is deliberately less than a full execution language.

## 6. Recommended Root Shape

A bounded v0 root shape should look like:

```text
D1NormalizedIR_v0 :=
  {
    schema: "d1_normalized_ir@1",
    ir_version: "v0",
    dialect_source: "D@1",
    selector_refs: SelectorRef_v0[],
    clauses: NormalizedClause_v0[],
    trace_metadata?: RootTraceMetadata_v0,
    ir_semantic_hash: Sha256Hex
  }
```

Recommended notes:

- `schema` names the artifact family and schema line;
- `ir_version` freezes the bounded semantic shape;
- `dialect_source` makes the source dialect explicit;
- `selector_refs` and `clauses` are semantic contents;
- `trace_metadata` is allowed but non-semantic unless explicitly stated otherwise;
- `ir_semantic_hash` fingerprints the normalized semantic payload, not run state.

## 7. Normalized Clause Representation

A bounded v0 normalized clause should look like:

```text
NormalizedClause_v0 :=
  {
    clause_ref: ClauseRef_v0,
    clause_semantic_hash: Sha256Hex,
    subject_selector_ref: SelectorRefId,
    modal: must | must_not,
    assertion: Assertion_v0,
    qualifiers: Qualifier_v0[],
    trace_metadata?: ClauseTraceMetadata_v0
  }
```

### 7.1 Clause fields

#### `clause_ref`

`clause_ref` is the trace handle that points back to source.

A bounded v0 shape should look like:

```text
ClauseRef_v0 :=
  {
    source_document_ref: string,
    block_id: string,
    clause_label?: string
  }
```

This is for traceability and human/debug joins.

It should not be treated as the entire semantic payload of the clause.

#### `clause_semantic_hash`

This is the semantic fingerprint of the normalized clause meaning.

It should be computed over the canonical semantic payload of the clause and should exclude non-semantic trace fields.

#### `subject_selector_ref`

This points to the selector reference that determines which subjects the clause may instantiate against.

The resolved subjects themselves do not belong in `D-IR`.

#### `modal`

For v0, live values are:

- `must`
- `must_not`

`D-IR` should preserve modal polarity directly.

It should not require every negative clause to be rewritten into an invented positive predicate.

#### `assertion`

This is the normalized clause body after source-level sugar has been lowered.

#### `qualifiers`

This is the ordered list of normalized clause qualifiers.

For v0, the admissible qualifier kinds are:

- `only_if`
- `unless`

At most one of each may appear.

Canonical ordering for IR emission and semantic hashing should be:

1. `only_if`
2. `unless`

#### `trace_metadata`

This preserves source lineage and authoring context that may be useful to humans and diagnostics.

It is not operational state.

## 8. Selector Reference Representation

A bounded v0 selector reference should look like:

```text
SelectorRef_v0 :=
  {
    selector_ref: SelectorRefId,
    selector_kind: "bootstrap_string",
    selector_text: string,
    zero_match_policy: "allow_empty_with_notice",
    trace_metadata?: SelectorTraceMetadata_v0
  }
```

### 8.1 Required freeze points

For v0:

- selectors are bootstrap string selectors only;
- `selector_text` is the canonical normalized selector string;
- zero-match posture belongs here as a semantic policy property;
- resolved subject lists do not belong here;
- selector execution traces do not belong here.

### 8.2 What must stay out

A selector ref in `D-IR` must not contain:

- resolved subject populations;
- match counts from a particular run;
- checker-emitted selector observations;
- zero-match notices from a particular run.

Those are evaluation-time or checker-time artifacts, not IR.

## 9. Assertion Representation

The bounded v0 assertion union should look like:

```text
Assertion_v0 :=
  PredicateAssertion_v0
| ComparisonAssertion_v0
```

### 9.1 Predicate assertion representation

```text
PredicateAssertion_v0 :=
  {
    assertion_kind: "predicate_call",
    predicate_ref: PredicateRef_v0,
    args: Argument_v0[]
  }

PredicateRef_v0 :=
  {
    predicate_id: string,
    contract_version: string
  }
```

This keeps predicate meaning tied to the bootstrap predicate-contract artifact rather than implementation folklore.

### 9.2 Comparison assertion representation

```text
ComparisonAssertion_v0 :=
  {
    assertion_kind: "comparison",
    operator: "eq",
    left: ValueRef_v0,
    right: LiteralValue_v0,
    comparison_profile: "scalar_exact" | "list_ordered_exact"
  }
```

For the bounded v0 slice:

- equality is enough;
- ordered list equality must remain exact and ordered;
- list equality semantics belong in the assertion representation, not in checker prose.

### 9.3 Argument and value references

A bounded v0 argument/value reference shape should look like:

```text
Argument_v0 :=
  PathArg_v0
| LiteralArg_v0

ValueRef_v0 :=
  PathRef_v0

PathArg_v0 :=
  {
    arg_kind: "path_ref",
    value: string
  }

LiteralArg_v0 :=
  {
    arg_kind: "literal",
    value: string | number | boolean
  }

PathRef_v0 :=
  {
    value_kind: "path_ref",
    value: string
  }
```

This is intentionally small.

The point is to preserve the normalized semantic call shape, not to introduce a large expression language.

### 9.4 Lowering of source-level constructors

The following authoring forms should be lowered before landing in `D-IR`:

- `REQUIRED path` -> `predicate_call(present, [path])`
- `EXPLICIT path` -> `predicate_call(explicit, [path])`
- `EXACTLY_ONE path` -> `predicate_call(cardinality_eq, [path, 1])`

This means constructor sugar does not survive as a separate semantic form in IR.

What survives is the normalized predicate call.

A source trace may still preserve the original authoring form for diagnostics.

## 10. Qualifier Representation

A bounded v0 qualifier should look like:

```text
Qualifier_v0 :=
  {
    qualifier_kind: "only_if" | "unless",
    condition: Condition_v0,
    trace_metadata?: QualifierTraceMetadata_v0
  }

Condition_v0 :=
  PredicateAssertion_v0
| ComparisonAssertion_v0
```

### 10.1 Semantics posture

The evaluator semantics of qualifiers remain defined by the `D@1` dialect spec.

The role of `D-IR` is narrower:

- preserve the qualifier kind;
- preserve the normalized condition structure;
- preserve enough trace to connect back to source;
- avoid mixing evaluation outcomes into the IR itself.

### 10.2 What must stay out

Qualifier representations in `D-IR` must not contain:

- evaluated truth values;
- runtime applicability states;
- waiver or deferral issuance;
- ledger state.

Those are result-set or ledger concerns.

## 11. Trace Metadata

`D-IR` should allow bounded non-semantic trace metadata.

That metadata is for source lineage, diagnostics, and explainability.

It is not part of operational state.

### 11.1 Recommended root trace metadata

A bounded v0 root trace shape may carry:

```text
RootTraceMetadata_v0 :=
  {
    source_documents: string[],
    source_block_refs?: string[],
    normalization_profile?: string,
    compiler_profile?: string
  }
```

### 11.2 Recommended clause trace metadata

A bounded v0 clause trace shape may carry:

```text
ClauseTraceMetadata_v0 :=
  {
    source_span?: string,
    source_note_text?: string,
    original_assertion_form?: "required" | "explicit" | "exactly_one" | "predicate_call" | "comparison",
    normalization_steps?: string[]
  }
```

### 11.3 Non-semantic trace rule

Trace metadata should be explicitly non-semantic in v0 unless a later spec says otherwise.

So changes to:

- source span;
- note text;
- authoring whitespace;
- normalization-step labels;
- compiler profile strings

must not change clause meaning by themselves.

## 12. Semantic Hash Posture

The semantic hash posture should be explicit.

### 12.1 Clause semantic hash

`clause_semantic_hash` should be computed over the canonical semantic payload of the normalized clause.

That canonical semantic payload should include only:

- normalized modal;
- canonical selector reference payload as used by the clause;
- normalized assertion;
- normalized qualifiers in canonical order.

It should exclude:

- source markdown bytes;
- source document pathing details that are trace-only;
- source span metadata;
- note gloss;
- compiler build metadata;
- run identifiers;
- checker facts;
- evaluator results;
- ledger state.

### 12.2 Root IR semantic hash

`ir_semantic_hash` should fingerprint the canonical semantic contents of the full `D-IR` artifact.

It should include the normalized semantic clause set and selector references as semantic contents.

It should exclude trace-only metadata and all run-specific content.

### 12.3 Canonicalization posture

The v0 posture should be deterministic.

At minimum:

- canonical JSON serialization;
- stable key ordering;
- deterministic clause ordering;
- deterministic selector-ref ordering.

The important freeze is that semantically identical normalized content should produce the same semantic hash even when authoring whitespace or note text changes.

### 12.4 Hashes are fingerprints, not authority

A semantic hash is a semantic fingerprint.

It is not:

- a checker fact bundle hash;
- a run identifier;
- a waiver or deferral authority artifact;
- a substitute for the source trace handle.

In particular, the semantic hash alone should not be treated as the entire human-usable clause reference.

`clause_ref` must remain preserved for trace and disambiguation.

## 13. What Is Lowered Away Versus Preserved

### 13.1 Lowered away

The following should be lowered away from the semantic payload of `D-IR`:

- markdown fence syntax;
- surrounding prose outside `D@1`;
- authoring whitespace and keyword surface form;
- constructor sugar for `REQUIRED`, `EXPLICIT`, and `EXACTLY_ONE`;
- source block container shape except where needed for trace;
- non-semantic note text as semantic law.

### 13.2 Preserved semantically

The following should be preserved semantically in `D-IR`:

- modal polarity;
- selector reference semantics;
- zero-match policy posture;
- normalized predicate/comparison structure;
- exact comparison semantics such as ordered list equality;
- qualifier kind and normalized qualifier condition.

### 13.3 Preserved as trace only

The following may be preserved as trace-only metadata:

- source document ref;
- block id;
- clause label;
- note text;
- source span;
- original authoring constructor form.

## 14. What Belongs In IR Versus What Must Stay Out

### 14.1 Belongs in `D-IR`

`D-IR` should contain:

- normalized clause meaning;
- selector references;
- predicate references and versions;
- normalized comparison forms;
- normalized qualifiers;
- semantic hashes;
- source-trace metadata.

### 14.2 Must stay out of `D-IR`

`D-IR` must not contain:

- raw source markdown as authoritative payload;
- prose-derived obligations outside `D@1`;
- checker fact payloads;
- result verdicts;
- ledger states;
- waiver refs;
- deferral refs;
- remediation ownership;
- resolved subject populations;
- closeout decisions;
- runtime execution state.

This is the key family boundary.

## 15. Minimum Join Keys For Neighbor Artifacts

To keep family seams tight, the minimum cross-artifact join keys should be:

- `clause_ref`
- `clause_semantic_hash`
- `subject_ref` (outside IR; created at evaluation time)
- `scope_snapshot` (outside IR; evaluation/ledger context)

`D-IR` provides the clause-side half of that join.

Result sets and the ledger provide the run/scope/subject side.

## 16. Worked Mini Example

Source `D@1`:

```md
:::D@1 id=snapshot-bind
ON artifact.emitted[*]
NOTE "carrier identity rules"
@state MUST REQUIRED snapshot.staleness_state
@bind MUST bind_to(snapshot.identity) ONLY_IF present(snapshot.identity)
:::
```

Illustrative normalized `D-IR` fragment:

```json
{
  "schema": "d1_normalized_ir@1",
  "ir_version": "v0",
  "dialect_source": "D@1",
  "selector_refs": [
    {
      "selector_ref": "sel_snapshot_bind_on",
      "selector_kind": "bootstrap_string",
      "selector_text": "artifact.emitted[*]",
      "zero_match_policy": "allow_empty_with_notice"
    }
  ],
  "clauses": [
    {
      "clause_ref": {
        "source_document_ref": "docs/example.md",
        "block_id": "snapshot-bind",
        "clause_label": "state"
      },
      "clause_semantic_hash": "<sha256>",
      "subject_selector_ref": "sel_snapshot_bind_on",
      "modal": "must",
      "assertion": {
        "assertion_kind": "predicate_call",
        "predicate_ref": {
          "predicate_id": "present",
          "contract_version": "v0"
        },
        "args": [
          {
            "arg_kind": "path_ref",
            "value": "snapshot.staleness_state"
          }
        ]
      },
      "qualifiers": [],
      "trace_metadata": {
        "source_note_text": "carrier identity rules",
        "original_assertion_form": "required",
        "normalization_steps": [
          "constructor_lowered"
        ]
      }
    },
    {
      "clause_ref": {
        "source_document_ref": "docs/example.md",
        "block_id": "snapshot-bind",
        "clause_label": "bind"
      },
      "clause_semantic_hash": "<sha256>",
      "subject_selector_ref": "sel_snapshot_bind_on",
      "modal": "must",
      "assertion": {
        "assertion_kind": "predicate_call",
        "predicate_ref": {
          "predicate_id": "bind_to",
          "contract_version": "v0"
        },
        "args": [
          {
            "arg_kind": "path_ref",
            "value": "snapshot.identity"
          }
        ]
      },
      "qualifiers": [
        {
          "qualifier_kind": "only_if",
          "condition": {
            "assertion_kind": "predicate_call",
            "predicate_ref": {
              "predicate_id": "present",
              "contract_version": "v0"
            },
            "args": [
              {
                "arg_kind": "path_ref",
                "value": "snapshot.identity"
              }
            ]
          }
        }
      ]
    }
  ],
  "ir_semantic_hash": "<sha256>"
}
```

The important point is that the IR fragment contains normalized semantics and trace.

It does not contain checker facts, evaluation results, or ledger state.

## 17. Non-Goals

The bounded v0 `D-IR` slice should not:

1. preserve arbitrary markdown formatting as semantic content;
2. embed checker fact bundles;
3. embed run-specific evaluator results;
4. embed ledger ownership or remediation state;
5. widen into a general-purpose logic language;
6. add source-level deferral semantics;
7. infer obligations from prose outside `D@1`.

## 18. Machine-Checkable Seed Summary

```json
{
  "schema": "d1_normalized_ir_seed@1",
  "artifact": "docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_seed",
  "normalized_ir_required": true,
  "semantic_not_operational_required": true,
  "not_source_markdown_required": true,
  "not_checker_output_required": true,
  "not_ledger_required": true,
  "source_dialect": "D@1",
  "selector_bootstrap_string_only_required": true,
  "constructor_lowering_required": {
    "REQUIRED": "present(path)",
    "EXPLICIT": "explicit(path)",
    "EXACTLY_ONE": "cardinality_eq(path, 1)"
  },
  "modal_preservation_required": true,
  "qualifier_preservation_required": true,
  "trace_metadata_allowed_but_nonsemantic_required": true,
  "semantic_hash_posture_required": true,
  "facts_results_and_ledger_out_of_ir_required": true,
  "minimum_join_keys": [
    "clause_ref",
    "clause_semantic_hash",
    "subject_ref",
    "scope_snapshot"
  ]
}
```
