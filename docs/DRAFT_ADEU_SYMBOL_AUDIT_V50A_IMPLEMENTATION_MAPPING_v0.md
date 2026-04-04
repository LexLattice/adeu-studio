# Draft ADEU Symbol Audit V50A Implementation Mapping v0

Status: support note for the `V50-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the imported GPT
Pro `adeu_symbol_audit` prototype should be used as shaping evidence while the live
repo-owned `V50-A` implementation is re-authored in `packages/adeu_symbol_audit`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v33.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS121.md`
- `examples/external_prototypes/adeu-symbol-audit-v0-bundle/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the bounded pilot scope over:
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`
- the starter symbol-kind set:
  - `class`
  - `function`
  - `method`
  - `local_function`
- AST-first deterministic extraction posture over explicit parseable Python defs
- the released-style textual symbol-id shape:
  - `symbol:{module_path}:{qualname}:{symbol_kind}`
- useful per-entry descriptive fields such as:
  - `symbol_name`
  - `start_line`
  - `end_line`
  - `parent_symbol_id`
  - `signature_text`
  - `decorators_or_modifiers`
  - `class_bases`
  - `docstring_excerpt`
  - `census_index`

## Re-Author With Repo Alignment

- create the repo-owned package scaffold under:
  - `packages/adeu_symbol_audit/src/adeu_symbol_audit/`
  - `packages/adeu_symbol_audit/tests/`
- re-author models with repo-native fail-closed validation rather than copying the
  prototype module tree
- introduce an explicit scope-manifest artifact instead of leaving scope law implicit
  inside the census builder, and bind each admitted pilot file to one explicit
  `sha256`
- make the overlap law against released `repo_symbol_catalog@1` explicit
- keep `local_function` as one explicit family-local extension rather than an implicit
  descriptive-baseline claim
- narrow `coverage.py` to manifest-to-census closure only for `V50-A`, including one
  explicit `missing_source_files` carrier rather than only unexpected-source drift
- add repo-native deterministic fixtures and targeted tests

## Defer To Later Slice

- `spu.py` semantic audit ledger work to `V50-B`
- the decision whether semantic/evidence vocabulary reuses released `V49` primitives or
  stays intentionally independent to `V50-B`
- audit-ledger coverage semantics to later family work after `V50-A` census/closure is
  accepted
- `cli.py` or runner surfaces to `V50-C`
- repo-wide scope widening beyond the bounded pilot files

## Do Not Import

- the prototype source tree wholesale into live package paths
- the prototype `spu.py` semantic-audit logic into `V50-A`
- the prototype audit-coupled `coverage.py` semantics as the live `V50-A` contract
- the prototype CLI surface
- the sample semantic-audit artifact as if it were a released repo fixture for
  `V50-A`
