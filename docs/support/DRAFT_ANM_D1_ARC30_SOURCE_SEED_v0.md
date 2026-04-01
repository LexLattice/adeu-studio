## 1. Core diagnosis

Plain markdown is good at preserving intent, rationale, caveats, and design posture. It is bad at preserving obligation. An LLM agent can read a markdown plan, internalize the spirit, and still silently drop a negative constraint, flatten a precedence order, or convert “must be explicit” into “probably inferable.” The problem is not expressiveness. The problem is authority.

The key distinction is:

* **epistemic prose** explains what the author means and why;
* **deontic clauses** determine what is permitted, required, forbidden, waived, or deferred.

In normal markdown those are interleaved, so the reader must continuously guess which sentences are governance-bearing and which are explanatory. That makes the document readable, but not reliably executable.

The right answer is not to formalize all prose. That would destroy the document’s value. The right answer is to create an **opt-in authoritative sublanguage** embedded inside markdown, with a hard boundary between human explanation and machine-governed clauses.

That gives you three distinct things instead of one overloaded file:

* a readable authoring surface,
* a semantically authoritative layer,
* an executable checking layer.

That is the correct D-first move for ADEU.

---

## 2. Design principles

1. **Authority must be opt-in, not inferred.**
   Reserved operators become semantic only inside explicitly marked authority zones.

2. **Free prose stays free prose.**
   The compiler never tries to recover obligations from arbitrary English paragraphs.

3. **The normative core must be small and crisp.**
   D@1 should prefer one clause per line, explicit selectors, explicit operators, and minimal composition.

4. **Semantics and execution must be separated.**
   The source declares obligations. The IR normalizes them. Checkers gather facts. Checkers do not invent policy.

5. **Canonical lowering matters.**
   Authoring sugar is acceptable; runtime semantics must come from a small normalized IR.

6. **Unknown is not compliance.**
   If a hard clause cannot be evaluated, the result should be blocking by default.

7. **ADEU layers must remain distinct.**
   O defines what exists, E defines how it is known, D defines what is allowed or required, U defines how compliant options are optimized. They should interoperate, not merge.

8. **The first slice must be bounded.**
   Do not start with theorem proving, arbitrary boolean logic, or full temporal reasoning. Start with compileable governance over files, manifests, schemas, and configuration.

---

## 3. Proposed architecture

I recommend a single format container, a markdown-native file, with authoritative dialect blocks embedded inside it.

### The three planes

**Authoring surface**
A normal markdown document, rendered and read like markdown. Headings, prose, examples, rationale, and design notes live here.

**Semantic authority**
Delimited `D@1` blocks. Only these blocks compile into governance semantics. Inside these blocks, reserved tokens such as `MUST`, `EXPLICIT`, `EXACTLY_ONE`, `UNLESS`, and `ONLY_IF` are operators, not rhetoric.

**Checker execution**
External checker scripts or executables mapped by capability. They inspect a repo snapshot, artifact manifests, schema rows, config files, or test fixtures and emit normalized facts. An evaluator compares those facts against D-IR.

### Pipeline

`source .adeu.md`
→ markdown/fence parser
→ D-block AST
→ canonical D-IR
→ checker dispatch plan
→ checker fact bundle
→ evaluator
→ result set and release gate decision

### The critical separation

* The **document** is authoritative about norms.
* The **IR** is authoritative about compiled semantics.
* The **checkers** are authoritative only about observed facts.

A checker may say “this artifact has no explicit `snapshot.staleness_state` field.”
It may not say “that is acceptable because the timestamps imply staleness.”
That second judgment belongs to D semantics, not execution code.

---

## 4. Concrete syntax proposal

Use a markdown file as the canonical source, for example:

`artifact-governance.adeu.md`

Optional front matter carries compiler metadata, not norms:

```yaml
---
format: ANM
version: 1
doc_id: adeu/policy/artifact-governance
authority_default: prose_nonbinding
unknown_is_blocking: true
---
```

### Authority block form

```md
:::D@1 id=<block-id>
ON <selector>
NOTE "<human gloss>"
@<clause-id> <OPERATOR> <expression> [ONLY_IF <expression>] [UNLESS <expression>] [BEFORE <anchor>] [AFTER <anchor>]
@<clause-id> <OPERATOR> <expression>
:::
```

### Recommended conventions

* `ON` is mandatory.
* `NOTE` is optional and non-semantic.
* Clause labels like `@bind` or `@explicit` are strongly recommended for stable references.
* All clause lines within a block share the same subject selector.
* Conjunction is implicit across lines.
  If you want three hard constraints, write three lines.
* D@1 should support only a small expression language:

  * path references: `snapshot.identity`
  * comparisons: `snapshot.identity.visibility == repo_visible`
  * predicate calls: `bind_to(snapshot.identity)`
  * list literals: `[a, b, c]`
  * integers for cardinality

### What is not allowed in D@1

* arbitrary English normative sentences inside authority blocks,
* implicit parsing of prose bullets,
* free-form boolean logic trees,
* hidden defaults,
* checker script invocations embedded in the source.

That last point matters. The source should name semantic propositions; a separate manifest should map them to execution capabilities.

---

## 5. D-operators@1 with crisp semantics

Let a clause be evaluated per selected subject. Let atomic propositions return `true`, `false`, or `unknown` from checker evidence.

Evaluation order for a clause instance should be:

1. `UNLESS` check,
2. `DEFERRED` check if applicable,
3. proposition evaluation,
4. modal mapping to result status.

### Core modals

**`MUST φ`**
Hard obligation.
`true -> pass`
`false -> fail`
`unknown -> unknown(blocking by default)`

**`MUST_NOT φ`**
Hard prohibition. Equivalent to `MUST (not φ)`.
`true -> fail`
`false -> pass`
`unknown -> unknown(blocking by default)`

**`MAY φ`**
Permission record. Absence of `φ` is not a failure.
Operationally useful for conflict analysis and policy publication, but low value in the first slice.

**`SHOULD φ`**
Soft obligation.
`true -> pass`
`false -> warn`
`unknown -> warn_unknown`

### Qualifiers

**`ONLY_IF ψ`**
Gate on the immediately preceding proposition.
`α ONLY_IF ψ` means `α -> ψ`.
If `α` occurs while `ψ` is false, the clause fails.
This is a gate, not an independent obligation.

**`UNLESS ε`**
Exception. If `ε` is true, the clause becomes `waived`.
Waived is not pass. It is an inactive obligation due to a declared exception.

**`BEFORE τ`**
Temporal ordering. Valid only for event-valued or timestamped propositions.
`α BEFORE τ` means the satisfaction event for `α` must occur earlier than `τ`.

**`AFTER τ`**
Temporal ordering in the other direction.
`α AFTER τ` means the satisfaction event for `α` must occur later than `τ`.

### Cardinality

These operators are subject-local unless explicitly extended later.

**`EXACTLY_ONE x`**
`count(values(x)) == 1`

**`AT_LEAST n x`**
`count(values(x)) >= n`

**`AT_MOST n x`**
`count(values(x)) <= n`

### State / declaration operators

**`REQUIRED x`**
Authoring sugar for a hard obligation.

* If `x` is a path, lower to `MUST present(x)`.
* If `x` is a comparison or predicate, lower to `MUST x`.

This allows both:

* `REQUIRED snapshot.staleness_state`
* `REQUIRED snapshot.identity.visibility == repo_visible`

**`FORBIDDEN x`**
Authoring sugar for hard prohibition.

* If `x` is a path, lower to `MUST_NOT present(x)`.
* If `x` is a comparison or predicate, lower to `MUST_NOT x`.

**`EXPLICIT x`**
Hard requirement on representation posture.
Lower to `MUST explicit(x)`.

`explicit(x)` means:

* the value/state is directly carried in an approved representation,
* not merely inferred from other fields,
* not merely defaulted,
* not merely reconstructed by a checker.

This is the operator that gives you “explicit rather than implied.”

**`DEFERRED x`**
Intentional postponement, not silent incompleteness.
A valid `DEFERRED x` lowers to a requirement that an explicit deferral record exists for `x`, typically containing owner, reason, and due condition. Result status should be `deferred`, not `pass`.

### Important D@1 discipline

D@1 should have **no general boolean algebra** beyond these forms.
No inline `AND`, `OR`, nested parentheses, or arbitrary quantification.
If policy needs complexity, factor it into:

* multiple clause lines,
* named derived predicates implemented by checkers,
* later O/E extension.

That is how you keep the format governable instead of decorative.

---

## 6. Example rewrite of the policy fragment into the format

```md
---
format: ANM
version: 1
doc_id: adeu/policy/artifact-governance
authority_default: prose_nonbinding
unknown_is_blocking: true
---

# Artifact governance

This document explains artifact binding and classification discipline.
Only `D@1` blocks are normative.

## Snapshot binding

Every emitted artifact must be traceable to a repository-visible snapshot.

:::D@1 id=snapshot.binding
ON artifact.emitted[*]
NOTE "All emitted artifacts must bind to one explicit repo-visible snapshot identity."
@bind MUST bind_to(snapshot.identity)
@one EXACTLY_ONE snapshot.identity
@visible REQUIRED snapshot.identity.visibility == repo_visible
@explicit EXPLICIT snapshot.identity
:::

:::D@1 id=snapshot.staleness
ON artifact.emitted[*]
NOTE "Stale-snapshot semantics must be explicit rather than implied."
@state REQUIRED snapshot.staleness_state
@explicit EXPLICIT snapshot.staleness_state
:::

## Schema discipline

:::D@1 id=schema.primary-carrier
ON schema.row[*]
NOTE "Schema rows must carry one primary carrier class."
@carrier EXACTLY_ONE primary_carrier_class
:::

## Classification discipline

Lexical naming may assist classification, but it may not outrank structural or semantic evidence.

:::D@1 id=classification.lexical-support
ON classifier.config
NOTE "Filename or naming-family cues are lower-precedence support only."
@role REQUIRED lexical_naming.role == support
@rank REQUIRED lexical_naming.rank == 4
@no_override MUST_NOT lexical_naming.override_higher_precedence
:::

:::D@1 id=classification.precedence
ON classifier.config
NOTE "Classification precedence is frozen."
@frozen REQUIRED classification.precedence == [
  structural_signature,
  semantic_function,
  governance_role,
  lexical_naming
]
:::
```

This does the right thing:

* prose remains readable,
* the normative core is explicit,
* every hard claim is checkable,
* “explicit” is a true operator, not a stylistic flourish.

---

## 7. Sample IR design

The parsed clause form should still look source-like.
The IR should not.

The IR should be normalized, typed, and desugared.

### Suggested top-level IR shape

```json
{
  "ir_kind": "ANM-DIR",
  "ir_version": 1,
  "doc_id": "adeu/policy/artifact-governance",
  "semantic_hash": "sha256:...",
  "source_ref": {
    "path": "artifact-governance.adeu.md",
    "source_hash": "sha256:..."
  },
  "evaluation": {
    "unknown_is_blocking": true,
    "subject_quantification": "per_selected_subject"
  },
  "clauses": [
    {
      "id": "snapshot.binding.bind",
      "scope": {
        "selector": "artifact.emitted[*]",
        "quantifier": "each"
      },
      "severity": "error",
      "assertion": {
        "type": "predicate",
        "name": "bind_to",
        "args": [{ "type": "path", "value": "snapshot.identity" }]
      },
      "qualifiers": [],
      "origin": {
        "block_id": "snapshot.binding",
        "clause_label": "bind"
      }
    },
    {
      "id": "snapshot.binding.one",
      "scope": {
        "selector": "artifact.emitted[*]",
        "quantifier": "each"
      },
      "severity": "error",
      "assertion": {
        "type": "cardinality",
        "op": "eq",
        "count": 1,
        "path": "snapshot.identity"
      },
      "qualifiers": [],
      "origin": {
        "block_id": "snapshot.binding",
        "clause_label": "one"
      }
    },
    {
      "id": "snapshot.binding.visible",
      "scope": {
        "selector": "artifact.emitted[*]",
        "quantifier": "each"
      },
      "severity": "error",
      "assertion": {
        "type": "comparison",
        "lhs": { "type": "path", "value": "snapshot.identity.visibility" },
        "cmp": "eq",
        "rhs": { "type": "symbol", "value": "repo_visible" }
      },
      "qualifiers": [],
      "origin": {
        "block_id": "snapshot.binding",
        "clause_label": "visible"
      }
    },
    {
      "id": "snapshot.binding.explicit",
      "scope": {
        "selector": "artifact.emitted[*]",
        "quantifier": "each"
      },
      "severity": "error",
      "assertion": {
        "type": "explicit",
        "path": "snapshot.identity"
      },
      "qualifiers": [],
      "origin": {
        "block_id": "snapshot.binding",
        "clause_label": "explicit"
      }
    }
  ],
  "dispatch_hints": {
    "artifact.emitted[*]": [
      "artifact_manifest_reader@1",
      "repo_snapshot_resolver@1"
    ],
    "schema.row[*]": [
      "schema_row_scanner@1"
    ],
    "classifier.config": [
      "classifier_config_reader@1",
      "classifier_behavior_probe@1"
    ]
  }
}
```

### IR rules worth making explicit

* `REQUIRED` and `FORBIDDEN` should be lowered away.
* `NOTE` should not affect `semantic_hash`.
* `origin` should preserve traceability back to the source.
* `dispatch_hints` are advisory, not normative.
* The IR should be canonicalized for stable hashing and diffing.

That gives you semantic stability independent of wording changes in surrounding prose.

---

## 8. Checker model

The checker layer should be capability-driven, fact-oriented, and versioned.

### Checker contract

A checker receives:

* the evaluation snapshot,
* the subject selector or concrete subjects,
* the relevant assertion capabilities,
* optional config.

A checker returns normalized facts, not verdicts.

Example fact record:

```json
{
  "subject": "artifact:dist/report.json",
  "snapshot": "git:7d9c1af",
  "fact_type": "path_observation",
  "path": "snapshot.identity",
  "present": true,
  "value": "git:7d9c1af",
  "explicit": true,
  "provenance": {
    "carrier": "dist/report.json.meta",
    "mode": "direct"
  },
  "checker": "artifact_manifest_reader@1"
}
```

### Why checkers should not return pass/fail

Because that collapses semantics into tooling. Then every checker becomes a policy interpreter, and policy drift becomes invisible.

The evaluator should own verdict computation:

* hard obligation + false → fail
* hard obligation + unknown → unknown/block
* `UNLESS` true → waived
* valid deferral → deferred
* `SHOULD` false → warn

### Checker classes for the first slice

**Structural checkers**
Read manifests, file headers, schema rows, config files.

**Resolution checkers**
Resolve `snapshot.identity` to a repo-visible object.

**Behavioral probe checkers**
Useful where precedence or override behavior cannot be read from config alone. They run controlled fixtures and return observed precedence behavior as facts.

### Result model

Per clause instance:

```json
{
  "clause_id": "snapshot.staleness.explicit",
  "subject": "artifact:dist/report.json",
  "status": "fail",
  "observed": {
    "path": "snapshot.staleness_state",
    "present": false,
    "explicit": false
  },
  "evidence": [
    "artifact_manifest_reader@1"
  ],
  "message": "snapshot.staleness_state is not explicitly carried"
}
```

That is the right separation: observed fact, applied norm, resulting verdict.

---

## 9. ADEU extension path

The format should be one container with multiple authority dialects, not one mega-language.

### O-layer later: ontology / entities / structure

`O@1` should define:

* entities,
* selectors,
* fields,
* enums,
* carrier classes,
* relation names.

Example role:

* define what `artifact.emitted[*]` means,
* define `primary_carrier_class`,
* define the enum for classification signals.

### E-layer later: epistemics / evidence / derivation posture

`E@1` should define:

* evidence sources,
* direct vs derived observations,
* freshness expectations,
* derivation contracts,
* acceptable inference posture.

This is where you can later say:

* which facts may be inferred,
* which facts require direct evidence,
* whether a checker’s conclusion is structural, semantic, or heuristic.

D should consume E facts; it should not invent epistemics on the fly.

### D-layer first: obligations / permissions / prohibitions

`D@1` stays narrow:

* norms over named selectors and predicates,
* explicit exceptions,
* explicit cardinality,
* explicit gates.

### U-layer later: optimization pressure

`U@1` should define:

* objectives,
* weights,
* tie-breakers,
* cost/benefit scoring.

But U must sit behind D.
The rule should be:

**first satisfy D, then optimize with U among the compliant set.**

### The non-collapse rule

* O says **what exists**.
* E says **how it is known**.
* D says **what must or must not hold**.
* U says **which compliant state is preferred**.

If one layer starts doing another layer’s job, the format will decay into an untyped policy soup.

---

## 10. Anti-patterns and failure modes

### 1. Treating prose as latent policy

If the compiler “helpfully” extracts obligations from paragraphs, authority becomes ambiguous again.

### 2. Making D blocks English-like

If D blocks accept arbitrary sentences, you have rebuilt the original problem inside a fence.

### 3. Letting checkers encode semantics

A checker that returns “acceptable” rather than normalized facts is silently rewriting policy.

### 4. Overloading one clause with too much logic

Nested `AND/OR/NOT` trees make the format harder to author and harder to trust. D@1 should force factoring.

### 5. Hidden defaults that satisfy `EXPLICIT`

If a missing field can be synthesized by convention and still count as explicit, the operator is meaningless.

### 6. Inline script names in policy clauses

That couples governance text to execution implementation and makes refactoring dangerous.

### 7. Collapsing O/E/D/U into one surface syntax

That destroys type discipline and makes later reasoning murky.

### 8. No stable clause IDs

Without stable clause IDs, reports, waivers, and deferrals become operationally weak.

### 9. Allowing lexical cues to stand in for structure

This is exactly the sort of silent precedence drift your example is trying to prevent.

---

## 11. Minimal viable slice

The realistic first product is not “full ADEU.” It is **ANM with D@1 execution**.

### MVP scope

* markdown source container,
* `D@1` fenced authority blocks,
* `ON`, `NOTE`, clause labels,
* selectors as strings with wildcard support,
* expressions: path, comparison, predicate call, list literal,
* executable operators:

  * `MUST`
  * `MUST_NOT`
  * `SHOULD`
  * `REQUIRED`
  * `EXPLICIT`
  * `EXACTLY_ONE`
  * `AT_LEAST`
  * `AT_MOST`
  * `ONLY_IF`
  * `UNLESS`

### Reserved now, fully operational later

* `MAY`
* `BEFORE`
* `AFTER`
* `DEFERRED`
* `FORBIDDEN`

These should exist in the grammar and IR now, but runtime support can be staged if the first deployment is focused on repo artifacts, schema rows, and config precedence.

### Explicit non-goals for MVP

* arbitrary theorem proving,
* general-purpose rule engine semantics,
* cross-repo distributed evaluation,
* natural language interpretation,
* full O/E/U compilation.

That boundedness is a strength, not a weakness.

---

## 12. Recommended artifact set

For one policy package, I recommend these artifacts:

* `policy.adeu.md`
  The human-authored canonical source.

* `policy.d-ir.json`
  Canonical normalized D-IR.

* `policy.lock.json`
  Semantic hash, source hash, compiler version, checker manifest version.

* `checker-manifest.json`
  Capability-to-checker mapping.

* `facts.json`
  Raw normalized checker observations for a specific evaluation run.

* `results.json`
  Clause-by-clause evaluator verdicts.

* `report.md`
  Human-readable report rendered from `results.json`.

That is enough to support authoring, reproducibility, auditing, and CI gating.

---

## 13. Comparison against alternatives

### Plain markdown

Best for readability, worst for executable authority.
It preserves rationale but not obligation integrity.

### YAML / JSON policy only

Best for machine strictness, poor for authorial reasoning.
It tends to eject the useful prose into another file, which recreates drift between explanation and enforcement.

### Rego / CUE / code-first policy

Very powerful, but too implementation-centric as an authoring surface for mixed human/machine governance.
Good backends, poor primary documents for architecture plans and policy intent.

### Inline lint rules scattered across repos

Executable, but fragmented and semantically local.
You lose a single readable governance artifact and you embed policy in implementation details.

### The recommended design

Markdown as the container, authoritative D blocks as the semantic core, fact-oriented checkers as execution.
That is the right balance between readability and enforceability.

---

## 14. Final recommendation

Adopt a single markdown-native format with **fenced authoritative dialect blocks**, starting with `D@1`. Do not attempt to formalize free prose. Do not let checkers define semantics. Do not collapse O, E, D, and U into one grammar.

The recommended architecture is:

* **authoring surface:** normal markdown,
* **semantic authority:** `D@1` blocks with reserved operators,
* **checker execution:** external fact-producing checkers,
* **compiled target:** canonical D-IR with stable clause IDs and semantic hashing.

This gives you exactly what your diagnosis asks for: markdown remains epistemically useful, while hard clauses become executable governance.

---

## A. Proposed format name

**ADEU Normative Markdown**
Abbrev: **ANM**

---

## B. Minimal grammar sketch

```ebnf
document        ::= frontmatter? { markdown_chunk | d_block } ;

d_block         ::= ":::D@1" ws "id=" ident newline
                    on_line
                    note_line?
                    { clause_line }
                    ":::" newline? ;

on_line         ::= "ON" ws selector newline ;
note_line       ::= "NOTE" ws string newline ;

clause_line     ::= clause_label? operator ws expr qualifier* newline ;

clause_label    ::= "@" ident ws ;

operator        ::= "MUST"
                  | "MUST_NOT"
                  | "MAY"
                  | "SHOULD"
                  | "ONLY_IF"
                  | "UNLESS"
                  | "BEFORE"
                  | "AFTER"
                  | "EXACTLY_ONE"
                  | "AT_LEAST"
                  | "AT_MOST"
                  | "REQUIRED"
                  | "FORBIDDEN"
                  | "EXPLICIT"
                  | "DEFERRED" ;

qualifier       ::= ws "ONLY_IF" ws expr
                  | ws "UNLESS" ws expr
                  | ws "BEFORE" ws expr
                  | ws "AFTER" ws expr ;

expr            ::= comparison
                  | predicate
                  | path
                  | list
                  | integer ws path ;   // for AT_LEAST / AT_MOST

comparison      ::= value ws comparator ws value ;
predicate       ::= ident "(" [ value { "," ws? value } ] ")" ;
path            ::= ident { "." ident | "[*]" } ;
list            ::= "[" ws? value { "," ws? value } ws? "]" ;
value           ::= path | ident | string | integer | list ;
comparator      ::= "==" | "!=" | "<" | ">" | "<=" | ">=" ;
selector        ::= path ;
ident           ::= letter { letter | digit | "_" | "-" } ;
```

This is intentionally small. It is a governance grammar, not a programming language.

---

## C. Worked end-to-end example

### Source text

```md
:::D@1 id=snapshot.staleness
ON artifact.emitted[*]
NOTE "Stale-snapshot semantics must be explicit rather than implied."
@state REQUIRED snapshot.staleness_state
@explicit EXPLICIT snapshot.staleness_state
:::
```

### Parsed clause form

```json
{
  "block_id": "snapshot.staleness",
  "selector": "artifact.emitted[*]",
  "note": "Stale-snapshot semantics must be explicit rather than implied.",
  "clauses": [
    {
      "label": "state",
      "operator": "REQUIRED",
      "expr": { "type": "path", "value": "snapshot.staleness_state" },
      "qualifiers": []
    },
    {
      "label": "explicit",
      "operator": "EXPLICIT",
      "expr": { "type": "path", "value": "snapshot.staleness_state" },
      "qualifiers": []
    }
  ]
}
```

### IR

```json
[
  {
    "id": "snapshot.staleness.state",
    "scope": {
      "selector": "artifact.emitted[*]",
      "quantifier": "each"
    },
    "severity": "error",
    "assertion": {
      "type": "present",
      "path": "snapshot.staleness_state"
    }
  },
  {
    "id": "snapshot.staleness.explicit",
    "scope": {
      "selector": "artifact.emitted[*]",
      "quantifier": "each"
    },
    "severity": "error",
    "assertion": {
      "type": "explicit",
      "path": "snapshot.staleness_state"
    }
  }
]
```

### Checker-result concept

Suppose the checker inspects `artifact:dist/report.json` and finds:

* no `snapshot.staleness_state` field,
* timestamps suggest staleness,
* but nothing explicitly declares it.

Fact bundle:

```json
[
  {
    "subject": "artifact:dist/report.json",
    "path": "snapshot.staleness_state",
    "present": false,
    "explicit": false,
    "provenance": { "carrier": "dist/report.json.meta", "mode": "absent" },
    "checker": "artifact_manifest_reader@1"
  }
]
```

Evaluator result:

```json
[
  {
    "clause_id": "snapshot.staleness.state",
    "subject": "artifact:dist/report.json",
    "status": "fail",
    "message": "required field snapshot.staleness_state is absent"
  },
  {
    "clause_id": "snapshot.staleness.explicit",
    "subject": "artifact:dist/report.json",
    "status": "fail",
    "message": "staleness is not explicitly declared; implied semantics do not satisfy EXPLICIT"
  }
]
```

That is the point of the format.
The prose said “explicit rather than implied.”
The D-layer turned that into executable governance.
