I grounded this against the actual repo and built a small runnable prototype bundle outside the tree: [prototype bundle](sandbox:/mnt/data/adeu_symbol_audit_v0_bundle.zip), [sample census](sandbox:/mnt/data/adeu_symbol_audit_v0/sample_symbol_census.json), [sample coverage report](sandbox:/mnt/data/adeu_symbol_audit_v0/sample_symbol_audit_coverage_report.json).

## 1. Module framing

I would frame the module as `adeu_symbol_audit`: a read-only ADEU-native closure engine that turns “audit this code” from an open-ended semantic task into a finite, typed worklist.

The core problem it solves is omission. Architectural audits drift because the auditor is free to skip, merge, or forget symbols. Parser-first grounding fixes that by splitting the work into two layers:

**A. Deterministic closure / completion**
A parser establishes the bounded universe of explicit code entities in scope. Completion becomes a set-accounting problem over canonical `symbol_id`s.

**B. Semantic correctness / architectural truth**
An SPU then makes evidence-backed claims about each symbol. Those claims may be insightful, weak, or wrong. They are hypotheses, not authority.

That distinction is the whole point. The module is successful when it can say, mechanically:

* these are the only explicit symbols in this scope
* every one has exactly one audit record
* no symbol was silently omitted
* some audit records remain low-confidence or unresolved

It is **not** successful merely because it emitted confident prose.

Why this is ADEU-native:

* **O**: explicit AST-backed code entities and their relations
* **E**: source spans, decorators, base classes, signatures, call summaries, file membership
* **D**: canonical symbol identity law, schema law, closure law, fail-closed completion gate
* **U**: omission reduction, legibility, overlap surfacing, abstraction-candidate surfacing without granting refactor authority

There is also direct repo precedent for parser-first grounding. `packages/adeu_repo_description/src/adeu_repo_description/extract.py:1331-1393` already derives a repo symbol catalog from Python AST, and `packages/adeu_repo_description/src/adeu_repo_description/models.py:1082-1150` defines `repo_symbol_catalog@1`. That is good prior art, but it is not a one-audit-per-symbol closure module.

## 2. Chosen bounded v0 scope

I would use a **small real Python slice** inside `packages/adeu_architecture_ir`:

Included:

* `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py`
* `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py`
* `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`

Excluded:

* `packages/adeu_architecture_ir/src/adeu_architecture_ir/root_family.py`
* `packages/adeu_architecture_ir/src/adeu_architecture_ir/__init__.py`
* tests
* every non-Python surface

Why this is the right v0 cut:

1. It is a semantically coherent slice. `analysis_request.py` and `analysis_settlement.py` are the V41-A / V41-B contract surfaces; `export_schema.py` is their schema emission edge.
2. It is bounded enough to audit manually and mechanically. On a prototype AST pass, this slice yields **62 explicit executable symbol defs**:

   * 31 functions
   * 15 classes
   * 15 methods
   * 1 nested `local_function`
3. It has enough variety to make the module real: pure helpers, hashing, materialization, Pydantic models, post-validators, boundary loaders, and an IO-emitting entrypoint.
4. It exposes an actual repo blind spot worth fixing: the existing `repo_symbol_catalog@1` extraction is broader, but it does not capture the nested local `_validate_ref` inside `AdeuArchitectureAnalysisRequest._validate_request`; v0 should treat that as an explicit syntactic symbol rather than silently dropping it.
5. Excluding `root_family.py` keeps the first pass principled. That file alone is large enough to swamp the implementation exercise.

So the pilot scope is not fantasy-wide, but it is real enough to prove the governance pattern.

## 3. Worked architecture for v0

### End-to-end pipeline

1. **Scope freeze**
   V0 should not start with repo-wide discovery. It should start from an explicit allowlist manifest of exact file paths for the pilot slice. That avoids scope drift when new files appear.

2. **Source load**
   Read the exact files, verify UTF-8, compute per-file `sha256`.

3. **Syntactic parse**
   Use Python stdlib `ast.parse`. No model involvement. No semantic inference.

4. **Symbol census emission**
   Walk the AST and emit one deterministic `SymbolCensusEntry` for every explicit:

   * `ClassDef` → `class`
   * top-level `FunctionDef` / `AsyncFunctionDef` → `function`
   * function directly under a class → `method`
   * function nested inside a function/method → `local_function`

   V0 should **not** attempt latent/runtime symbol inference:

   * no decorator-generated methods
   * no metaclass synthesis
   * no monkeypatch surfaces
   * no dynamic `exec` / `eval`

5. **Frozen worklist**
   Sort symbol rows deterministically by `(file_path, start_line, end_line, symbol_kind, fq_name)`.
   Assign `census_index`.
   Compute `census_hash`.

   After this point the work universe is closed.

6. **SPU semantic pass**
   Iterate the frozen census in order. For each symbol:

   * gather deterministic evidence
   * emit exactly one `SymbolSemanticAuditEntry`
   * never skip
   * unresolved is allowed
   * omission is not allowed

7. **Coverage / closure check**
   Compare census ids vs audit ids:

   * missing ids
   * duplicate primary audit ids
   * unexpected ids
   * schema-invalid entries
   * unresolved / low-confidence counts

8. **Stop-gate**
   Fail closed on incomplete coverage.
   Do **not** fail completion merely because semantic certainty is low.

### Where determinism ends

Deterministic machinery ends at:

* source-file allowlist
* AST parse
* symbol extraction
* canonical id assignment
* ordered worklist freeze
* set comparison for closure

Fallible inference begins at:

* role summary
* architectural purpose
* overlap candidate detection
* abstraction-candidate notes
* canonical-family guesses

So:

* `symbol_census@1` is authoritative about symbol existence
* `symbol_semantic_audit@1` is authoritative only about what the SPU claimed
* `symbol_audit_coverage_report@1` is authoritative about completion status

## 4. Authoritative artifact family for v0

I would keep the artifact family small and rigid.

### `adeu_symbol_census@1`

**Purpose:** authoritative frozen inventory of explicit parsed symbols in scope.

**Authoritative status:** authoritative for “what symbols exist in the chosen slice.”

**Stop-gate role:** all later artifacts bind to `census_hash`; if the census changes, the audits are stale.

```json
{
  "schema": "adeu_symbol_census@1",
  "scope_id": "architecture_ir.analysis_request_settlement_export.v0",
  "language": "python",
  "source_files": [
    { "file_path": "…", "sha256": "…" }
  ],
  "symbol_kinds_included": ["class", "function", "method", "local_function"],
  "symbol_count": 62,
  "census_hash": "sha256:…",
  "symbols": [
    {
      "symbol_id": "symbol:<file_path>:<fq_name>:<symbol_kind>",
      "fq_name": "AdeuArchitectureAnalysisRequest._validate_request._validate_ref",
      "symbol_name": "_validate_ref",
      "symbol_kind": "local_function",
      "language": "python",
      "file_path": "packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py",
      "start_line": 523,
      "end_line": 536,
      "parent_symbol_id": "symbol:…:AdeuArchitectureAnalysisRequest._validate_request:method",
      "signature_text": "def _validate_ref(ref: str, *, field_name: str, expected_kind: CapturedInputKind) -> None",
      "decorators_or_modifiers": [],
      "class_bases": [],
      "docstring_excerpt": null,
      "census_index": 48,
      "parser_version": "python.ast@3.11",
      "parser_confidence": "authoritative_for_explicit_parseable_defs",
      "parse_status": "parsed"
    }
  ]
}
```

**Identity law:** use the same textual pattern as `compute_symbol_id` in `adeu_repo_description/models.py:502-505`:

`symbol:{file_path}:{fq_name}:{symbol_kind}`

V0 should stay text-compatible with that law, while extending `symbol_kind` with `local_function`.

### `adeu_symbol_semantic_audit@1`

**Purpose:** canonical SPU claim ledger over the frozen symbol set.

**Authoritative status:** authoritative about what the SPU emitted, not about whether those claims are true.

**Stop-gate role:** must contain exactly one primary entry per census symbol.

```json
{
  "schema": "adeu_symbol_semantic_audit@1",
  "scope_id": "architecture_ir.analysis_request_settlement_export.v0",
  "census_hash": "sha256:…",
  "spu_name": "adeu_symbol_audit.heuristic_spu",
  "spu_version": "0.1.0",
  "audit_entry_count": 62,
  "audit_hash": "sha256:…",
  "audit_entries": [
    {
      "symbol_id": "symbol:…",
      "audit_status": "audited_hypothesis",
      "role_summary": "Post-parse contract validator",
      "architectural_purpose": "Supports the V41-A analysis request contract…",
      "local_behavior_summary": "Rewrites/normalizes fields after model parse and enforces cross-field invariants.",
      "inputs_outputs_summary": "def _validate_scope(self) -> AnalysisRequestScope",
      "side_effect_profile": ["in_process_only"],
      "dependency_position": "validation_or_boundary_bridge",
      "likely_canonical_family": "pydantic_post_validation",
      "overlap_candidate_symbol_ids": ["symbol:…"],
      "abstraction_candidate_notes": null,
      "evidence_refs": [
        { "evidence_kind": "source_span", "detail": "…#L211-L241" },
        { "evidence_kind": "decorator", "detail": "model_validator(mode='after')" },
        { "evidence_kind": "call_summary", "detail": "_normalize_repo_relative_path | object.__setattr__ | sorted | set" }
      ],
      "uncertainty_notes": ["No docstring present in symbol body."],
      "confidence_band": "medium"
    }
  ]
}
```

Recommended `audit_status` enum:

* `audited_hypothesis`
* `audited_low_confidence`
* `unresolved`

That lets the module close coverage even when semantics are weak.

### `adeu_symbol_audit_coverage_report@1`

**Purpose:** deterministic closure artifact.

**Authoritative status:** authoritative for completion accounting.

**Stop-gate role:** this is the machine-decidable completion verdict.

```json
{
  "schema": "adeu_symbol_audit_coverage_report@1",
  "scope_id": "architecture_ir.analysis_request_settlement_export.v0",
  "census_hash": "sha256:…",
  "audit_hash": "sha256:…",
  "expected_symbol_count": 62,
  "audited_symbol_count": 62,
  "missing_symbol_ids": [],
  "unexpected_symbol_ids": [],
  "duplicate_audit_symbol_ids": [],
  "schema_valid_count": 62,
  "unresolved_count": 0,
  "low_confidence_count": 21,
  "completion_status": "closed_with_low_confidence",
  "completion_gate_reason": "100% coverage reached; low-confidence hypotheses still require review"
}
```

### Validation and law set

**Schema law**
Every artifact validates. Every audit entry must have `symbol_id`, `audit_status`, `confidence_band`, and at least one evidence ref.

**Closure law**
Closure is satisfied iff:

* `expected_symbol_count == audited_symbol_count == schema_valid_count`
* `missing_symbol_ids == []`
* `duplicate_audit_symbol_ids == []`
* `unexpected_symbol_ids == []`

**Truth law**
Not part of closure. Semantic correctness is external review over evidence-backed hypotheses.

## 5. Arc and slice plan

### V0 arc

`v0.symbol_audit_frozen_worklist_closure`

This arc is done when the pilot slice can be parsed into a closed symbol inventory and audited to 100% worklist coverage without silent omission.

### Slice 1 — frozen pilot scope + deterministic census

Deliverables:

* explicit scope manifest / default file allowlist
* Python AST collector
* canonical sort
* `adeu_symbol_census@1`

Acceptance:

* repeated runs over identical bytes produce identical `census_hash`
* pilot slice yields the same 62-symbol inventory
* nested `_validate_ref` is present as `local_function`
* no duplicate `symbol_id`s

### Slice 2 — canonical identity + parentage law

Deliverables:

* symbol id law
* parent-child linkage
* stable `census_index`
* compatibility note with `compute_symbol_id`

Acceptance:

* every non-root symbol has a valid parent where expected
* every parent id resolves inside the same census
* symbol ids remain stable under repeated runs

### Slice 3 — heuristic SPU scaffold

Deliverables:

* `SymbolSemanticAuditEntry` schema
* `SemanticAuditSPU` interface
* simple heuristic SPU v0 using name/decorator/baseclass/call cues

Acceptance:

* exactly one audit entry emitted per census symbol
* every entry carries explicit uncertainty and evidence
* no entry claims semantic authority

### Slice 4 — fail-closed coverage gate

Deliverables:

* closure checker
* nonzero exit on incomplete coverage
* explicit incomplete/closed status separation

Acceptance:

* delete one audit entry → `completion_status=incomplete`
* duplicate one `symbol_id` → `completion_status=incomplete`
* insert unexpected `symbol_id` → `completion_status=incomplete`

### Slice 5 — advisory diagnostics

Deliverables:

* overlap candidate surfacing
* abstraction-candidate notes
* ranked follow-up questions

Acceptance:

* `_validation_context` pair is surfaced as overlap/abstraction candidate
* canonicalize/materialize family is surfaced as repeated pattern
* diagnostics do not affect closure verdict

### Non-goals for v0

* repo-wide audit
* non-Python parsing
* attributes/module sentinels/test surfaces
* refactor generation
* automated edits
* proof of semantic correctness

## 6. Projected code structure

I would make this a new package adjacent to `adeu_repo_description`, not a patch into app code.

```text
packages/adeu_symbol_audit/
  pyproject.toml
  src/adeu_symbol_audit/
    __init__.py
    models.py
    census.py
    spu.py
    coverage.py
    cli.py
    export_schema.py
  schema/
    adeu_symbol_census.v1.json
    adeu_symbol_semantic_audit.v1.json
    adeu_symbol_audit_coverage_report.v1.json
  tests/
    test_symbol_census_pilot.py
    test_symbol_local_function_inclusion.py
    test_symbol_id_stability.py
    test_symbol_semantic_audit_coverage.py
    test_symbol_coverage_fail_closed.py
    test_symbol_audit_export_schema.py
```

Artifact emission path:

```text
artifacts/symbol_audit/v0/architecture_ir.analysis_request_settlement_export/
  symbol_census.json
  symbol_semantic_audit.json
  symbol_audit_coverage_report.json
```

CLI shape:

```bash
python -m adeu_symbol_audit.cli \
  --repo-root . \
  --out-dir artifacts/symbol_audit/v0/architecture_ir.analysis_request_settlement_export
```

V0 should default to the pilot file allowlist. General subtree/glob support can wait.

## 7. Actual minimal implementation proposal

I generated a runnable prototype bundle here: [adeu_symbol_audit_v0_bundle.zip](sandbox:/mnt/data/adeu_symbol_audit_v0_bundle.zip). It is not repo-integrated, but it is concrete and produces real sample artifacts for the chosen slice.

### Core census logic

```python
def _symbol_id(*, file_path: str, fq_name: str, symbol_kind: str) -> str:
    return f"symbol:{file_path}:{fq_name}:{symbol_kind}"

class _Collector(ast.NodeVisitor):
    def __init__(self, *, file_path: str) -> None:
        self.file_path = file_path
        self.symbols = []
        self._stack = []

    def _add_symbol(self, node: ast.AST, *, name: str, symbol_kind: str) -> None:
        fq_name = ".".join([entry["symbol_name"] for entry in self._stack] + [name])
        self.symbols.append(
            {
                "symbol_id": _symbol_id(
                    file_path=self.file_path,
                    fq_name=fq_name,
                    symbol_kind=symbol_kind,
                ),
                "fq_name": fq_name,
                "symbol_name": name,
                "symbol_kind": symbol_kind,
                "file_path": self.file_path,
                "start_line": node.lineno,
                "end_line": getattr(node, "end_lineno", node.lineno),
                "parent_symbol_id": self._stack[-1]["symbol_id"] if self._stack else None,
                "signature_text": _signature_text(node),
                "decorators_or_modifiers": [ast.unparse(d) for d in getattr(node, "decorator_list", [])],
                "class_bases": [ast.unparse(base) for base in getattr(node, "bases", [])],
                "parse_status": "parsed",
            }
        )
        self._stack.append({"symbol_id": self.symbols[-1]["symbol_id"], "symbol_name": name, "symbol_kind": symbol_kind})
        self.generic_visit(node)
        self._stack.pop()

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._add_symbol(node, name=node.name, symbol_kind="class")

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        parent_kind = self._stack[-1]["symbol_kind"] if self._stack else None
        if parent_kind == "class":
            kind = "method"
        elif parent_kind in {"function", "method", "local_function"}:
            kind = "local_function"
        else:
            kind = "function"
        self._add_symbol(node, name=node.name, symbol_kind=kind)
```

That is the right v0 shape: stdlib AST, no model dependence, explicit local-function handling, canonical id law.

### SPU interface

I would formalize the SPU boundary even if v0 only ships a heuristic implementation.

```python
class SemanticAuditSPU(Protocol):
    name: str
    version: str

    def audit_symbol(
        self,
        *,
        census: SymbolCensus,
        symbol: SymbolCensusEntry,
        node: ast.AST,
        source_text: str,
    ) -> SymbolSemanticAuditEntry: ...
```

Then the runner is deterministic:

```python
audit_entries = []
for symbol in census.symbols:  # already sorted
    node = symbol_nodes[symbol.symbol_id]
    audit_entries.append(
        spu.audit_symbol(
            census=census,
            symbol=symbol,
            node=node,
            source_text=file_texts[symbol.file_path],
        )
    )
```

The crucial rule is not “be smart.” It is “emit exactly one entry per frozen symbol.”

### Coverage / stop-gate logic

```python
def build_coverage_report(*, census: SymbolCensus, audit: SymbolSemanticAudit) -> SymbolAuditCoverageReport:
    census_ids = [entry.symbol_id for entry in census.symbols]
    audit_ids = [entry.symbol_id for entry in audit.audit_entries]

    duplicate_ids = sorted(symbol_id for symbol_id, count in Counter(audit_ids).items() if count > 1)
    missing_ids = sorted(set(census_ids) - set(audit_ids))
    unexpected_ids = sorted(set(audit_ids) - set(census_ids))

    if missing_ids or unexpected_ids or duplicate_ids or audit.audit_entry_count != len(census_ids):
        status = "incomplete"
        reason = "fail_closed: expected one schema-valid audit entry per census symbol and no extras or duplicates"
    elif any(entry.audit_status == "unresolved" for entry in audit.audit_entries):
        status = "closed_with_unresolved"
        reason = "100% coverage reached, but unresolved audit entries remain"
    elif any(entry.confidence_band == "low" for entry in audit.audit_entries):
        status = "closed_with_low_confidence"
        reason = "100% coverage reached; low-confidence hypotheses still require review"
    else:
        status = "closed_clean"
        reason = "100% coverage reached with no unresolved or low-confidence entries"
```

That is the mechanical completion law. It does not pretend to judge semantic truth.

## 8. Worked example over real repo symbols

These are drawn from the actual chosen slice.

### Example 1 — `_normalize_repo_relative_path`

From `analysis_request.py:88-106`

Census shape:

* `symbol_id`: `symbol:packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py:_normalize_repo_relative_path:function`
* `symbol_kind`: `function`
* `parent_symbol_id`: `null`
* `signature_text`: `def _normalize_repo_relative_path(raw_path: str, *, field_name: str) -> str`

Audit shape:

* `audit_status`: `audited_hypothesis`
* `role_summary`: `String/ref/path normalization helper`
* `architectural_purpose`: supports V41-A request boundary normalization
* `evidence_refs`: source span, local calls like `strip`, `replace`, `_WINDOWS_ABSOLUTE_PATH_RE.match`, `ValueError`
* `confidence_band`: `medium`
* uncertainty: no docstring

This is a good example of a symbol that is easy to close mechanically and relatively safe to summarize semantically, but still not “proven true.”

### Example 2 — `AnalysisRequestScope._validate_scope`

From `analysis_request.py:211-241`

Census shape:

* `symbol_kind`: `method`
* parent: `AnalysisRequestScope`
* decorator: `model_validator(mode='after')`

Audit shape:

* `role_summary`: `Post-parse contract validator`
* `likely_canonical_family`: `pydantic_post_validation`
* `local_behavior_summary`: normalizes scope fields and enforces cross-field invariants
* evidence: decorator, source span, calls to `_normalize_repo_relative_path`, `object.__setattr__`, `sorted`, `set`
* confidence: `medium`

This is a good example where semantic evidence comes mostly from deterministic structure, not prose.

### Example 3 — nested local function `_validate_ref`

From `AdeuArchitectureAnalysisRequest._validate_request`, `analysis_request.py:523-536`

Census shape:

* `symbol_kind`: `local_function`
* parent: `AdeuArchitectureAnalysisRequest._validate_request`
* signature: `def _validate_ref(ref: str, *, field_name: str, expected_kind: CapturedInputKind) -> None`

Audit shape:

* `role_summary`: `Nested helper scoped to outer validator`
* `audit_status`: `audited_low_confidence`
* evidence: source span, local calls to `source_item_by_path.get`, `captured_input_ids.get`, `ValueError`
* uncertainty: explicitly notes that the role inference comes from the enclosing method and local calls, not a public contract

This symbol is important because it shows why v0 should not silently collapse “function” into only top-level defs. It is explicit syntax and it materially participates in validator behavior.

### Example 4 — duplicated helper `_validation_context`

There are two real instances:

* `analysis_request.py:73-79`
* `analysis_settlement.py:75-81`

The audit can mark each one with:

* overlap candidate = the other `_validation_context`
* abstraction candidate note = candidate for shared helper extraction if semantics remain identical

That is exactly the kind of advisory semantic output the SPU should produce: useful, bounded, and non-authoritative.

### Coverage accounting on the pilot slice

The prototype run over this real slice produced:

* expected symbols: 62
* audited symbols: 62
* missing: 0
* duplicates: 0
* unexpected: 0
* unresolved: 0
* low-confidence: 21
* completion status: `closed_with_low_confidence`

That is the correct v0 outcome shape: complete accounting, imperfect semantics.

## 9. Acceptance criteria and failure modes

### Acceptance criteria for v0

* Running the census twice over identical file bytes yields identical `census_hash`, identical symbol order, and identical `symbol_id`s.
* The pilot slice emits the same closed symbol inventory each run.
* Every census symbol has exactly one audit entry.
* No audit entry refers to a non-census symbol.
* No audit entry silently disappears without tripping the coverage gate.
* Audit artifacts validate against schema.
* Low-confidence and unresolved cases are explicit, never hidden behind confident prose.
* The CLI exits nonzero on incomplete coverage.
* The module never writes back into production source files.

### Important failure modes

* **Parser blind spots**: dynamic symbol creation, metaclass injection, decorator-generated members.
* **Identity drift**: if fq-name construction changes, historical symbol ids become unstable.
* **Nested symbol handling errors**: local functions or nested classes can be dropped or mis-parented.
* **Span errors**: incorrect `start_line` / `end_line` will pollute evidence refs and review.
* **SPU hallucination**: lexical cues can overclaim role or architectural purpose.
* **Indirect side-effect undercounting**: a symbol may look pure locally while delegating writes to a helper.
* **False overlap signals**: same-name helpers are not always real abstraction candidates.
* **Overclaiming truth from structure**: `BaseModel` + `model_validator` is strong evidence for “contract carrier / validator,” but not proof of intended architecture.
* **Coupling drift with `repo_symbol_catalog@1`**: if the repo-wide symbol id law changes and this module diverges, cross-artifact joins become brittle.

The design should be deliberately conservative: better to mark `audited_low_confidence` than to emit false certainty.

## 10. Forward path after v0

V1 should add three things:

1. a compatibility adapter to ingest or compare against `repo_symbol_catalog@1` and `repo_dependency_graph@1`
2. a stronger SPU that can use bounded cross-symbol evidence, not just local lexical/structural cues
3. diff mode across commits, so the audit can say exactly which symbols changed, which disappeared, and which newly require audit

What remains intentionally unsolved after v0:

* semantic truth
* dynamic/runtime-generated symbols
* non-Python languages
* automated refactoring or writeback
* repo-wide rollout

The right Codex-in-ADEU-harness follow-on is methodical:

* verify the three schemas and emitted sample artifacts
* adversarially test closure by deleting and duplicating audit rows
* verify local-function inclusion on the pilot slice
* inspect overlap candidates for false positives
* only then widen scope to `root_family.py` or a second package

The prototype bundle above is the smallest principled shape I would actually start from.
