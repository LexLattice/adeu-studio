# Draft Stop-Gate Decision vNext+121

Status: proposed gate for `V50-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS121.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail (Frozen)

- This draft records pre-start acceptance criteria only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS121.md`.
- This note captures bounded `V50-A` census / coverage acceptance only; it does not
  authorize the later semantic-audit ledger, the `V49` primitive reuse-vs-independence
  decision, CLI/API/web consumers, repo-wide scope widening, or imported-bundle
  precedent by itself.

## Accept When

- the repo-owned `adeu_symbol_audit` package scaffold lands as the only live owner of
  the shipped `V50-A` code;
- the first release emits exactly:
  - one `adeu_symbol_audit_scope_manifest@1`
  - one `adeu_symbol_census@1`
  - one `adeu_symbol_audit_coverage_report@1`
- deterministic replay is proven over exactly these committed pilot-scope files:
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`
  and the emitted scope manifest binds each file to one explicit `sha256`;
- the census stays bounded to the frozen symbol-kind set:
  - `class`
  - `function`
  - `method`
  - `local_function`
- shared symbol kinds reuse the released textual
  `symbol:{module_path}:{qualname}:{symbol_kind}` identity law;
- `local_function` remains one explicit family-local extension and is never claimed as
  parity or supersession over released `repo_symbol_catalog@1`, even if it reuses the
  same textual symbol-id shape;
- the coverage report remains manifest-to-census closure only and fails closed on:
  - missing manifest source files;
  - out-of-manifest source drift;
  - disallowed symbol-kind drift; or
  - duplicate symbol identity drift;
- Python tests cover:
  - model validation;
  - deterministic census replay;
  - local-function capture;
  - fail-closed coverage mismatch;
  - fixture parity;
- no semantic audit ledger, semantic evidence vocabulary, CLI surface, repo-wide scope,
  or prototype-tree import ships in this slice.

## Do Not Accept If

- the slice silently changes shared symbol identity law;
- the slice silently changes the meaning of shared symbol kinds;
- the slice widens coverage semantics into semantic-audit coverage;
- the slice claims symbol-kind parity or supersession over released
  `repo_symbol_catalog@1`;
- the emitted scope manifest names the right files but does not bind them to explicit
  content hashes;
- the slice decides the later `V49` primitive reuse-vs-independence question early;
- the slice imports prototype code wholesale into live package paths.

## Local Gate

- run `make check`
