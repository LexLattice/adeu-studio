# Locked Continuation vNext+121

Status: `V50-A` implementation contract.

## V121 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v50a_symbol_census_coverage_contract@1",
  "target_arc": "vNext+121",
  "target_path": "V50-A",
  "target_scope": "bounded_repo_owned_symbol_census_and_manifest_to_census_coverage_for_architecture_ir_pilot_scope",
  "implementation_packages": [
    "adeu_symbol_audit"
  ],
  "governing_released_stack": "V45_repo_description_plus_V49_semantic_forms_on_main",
  "governing_stack_consumption_mode": "anchor_and_comparison_context_only_not_reopened_description_semantics_not_reopened_semantic_substrate_semantics",
  "source_intake_bundle": "examples/external_prototypes/adeu-symbol-audit-v0-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "symbol_audit_package_scaffold_required": true,
  "selected_schema_ids": [
    "adeu_symbol_audit_scope_manifest@1",
    "adeu_symbol_census_entry@1",
    "adeu_symbol_census@1",
    "adeu_symbol_audit_coverage_report@1"
  ],
  "pilot_scope_language_singleton": "python",
  "pilot_scope_source_files": [
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py",
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py",
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py"
  ],
  "deterministic_replay_over_exact_pilot_scope_bytes_required": true,
  "scope_manifest_source_file_sha256_required": true,
  "starter_symbol_kind_vocabulary_frozen": [
    "class",
    "function",
    "method",
    "local_function"
  ],
  "repo_symbol_catalog_shared_symbol_kinds": [
    "class",
    "function",
    "method"
  ],
  "repo_symbol_catalog_out_of_scope_symbol_kinds": [
    "module",
    "attribute"
  ],
  "explicit_family_local_extension_symbol_kinds": [
    "local_function"
  ],
  "repo_symbol_catalog_symbol_kind_parity_not_claimed": true,
  "local_function_textual_symbol_id_shape_compatibility_only_not_symbolkind_parity": true,
  "lawful_divergence_from_repo_symbol_catalog_frozen": [
    "narrower_pilot_scope",
    "stricter_manifest_to_census_closure_ordering",
    "explicit_local_function_extension"
  ],
  "unlawful_divergence_from_repo_symbol_catalog_forbidden": [
    "silent_identity_law_change",
    "silent_shared_symbol_kind_meaning_change",
    "parity_or_supersession_claim",
    "implicit_local_function_descriptive_baseline_claim"
  ],
  "symbol_identity_law_compatibility_declaration_required": true,
  "shared_symbol_id_textual_law_reuse_required": true,
  "coverage_report_scope_frozen": "manifest_to_census_closure_only_not_semantic_audit_coverage",
  "manifest_to_census_closure_law_required": true,
  "coverage_report_missing_manifest_source_files_required": true,
  "coverage_mismatch_fails_closed": true,
  "semantic_audit_ledger_not_selected_here": true,
  "semantic_vocab_reuse_vs_independence_decision_not_selected_here": true,
  "v49_primitive_consumption_not_required_in_v50a": true,
  "cli_orchestration_consumers_not_selected_here": true,
  "repo_wide_scope_not_selected_here": true,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v33.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md",
    "docs/DRAFT_ADEU_SYMBOL_AUDIT_V50A_IMPLEMENTATION_MAPPING_v0.md",
    "examples/external_prototypes/adeu-symbol-audit-v0-bundle/ALIGNMENT.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v33.md"
}
```

## Slice

- Arc label: `vNext+121`
- Family label: `V50-A`
- Scope label: bounded repo-owned symbol census and manifest-to-census coverage for
  the `packages/adeu_architecture_ir` pilot scope

## Objective

Release the bounded `V50-A` census/coverage lane by creating the first repo-owned
`adeu_symbol_audit` package and freezing one read-only contract set rich enough to:

- declare one exact pilot-scope manifest over three committed Python files;
- replay one deterministic symbol census over exactly those file bytes;
- make the family’s overlap law against released `repo_symbol_catalog@1` explicit;
- freeze one symbol identity law that stays compatible with the released textual
  `symbol:{module_path}:{qualname}:{symbol_kind}` posture where declared;
- make `local_function` an explicit family-local extension rather than a silent fork
  of the released descriptive baseline;
- emit one manifest-to-census coverage / closure report that fails closed on mismatch.

This slice is read-only, census-first, and pre-semantic. It does not authorize the
semantic audit ledger, the `V49` primitive reuse-vs-independence decision, CLI/API/web
consumers, repo-wide scope widening, runtime mutation surfaces, or direct import of the
prototype tree into live package paths.

## Frozen Implementation Decisions

1. Package-ownership strategy:
   - `packages/adeu_symbol_audit` is the sole implementation owner in this slice;
   - the imported intake bundle remains shaping evidence only and may not be treated as
     the live package surface.
2. Pilot-scope strategy:
   - the first released pilot scope is exactly:
     - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py`
     - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py`
   - `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`
   - deterministic replay must be grounded in exactly those committed bytes, not in a
     looser conceptual “architecture_ir pilot” label.
   - the scope manifest must therefore bind each admitted file path to one explicit
     `sha256` value rather than naming file paths alone.
3. Overlap-and-delta strategy:
   - released `repo_symbol_catalog@1` remains overlap/anchor context only;
   - `V50-A` does not claim symbol-kind parity with released `repo_symbol_catalog@1`;
   - lawful divergence is bounded to:
     - narrower pilot scope;
     - stricter manifest-to-census closure ordering;
     - one explicit family-local `local_function` kind;
   - unlawful divergence is:
     - silent change to shared identity law;
     - silent change to shared symbol-kind meaning;
     - parity or supersession claim against `repo_symbol_catalog@1`;
     - implicit claim that `local_function` already belongs to the released
       descriptive baseline.
4. Symbol-identity strategy:
   - for shared kinds (`class`, `function`, `method`), the family must reuse the
     released textual symbol-id law:
     - `symbol:{module_path}:{qualname}:{symbol_kind}`
   - the `local_function` extension may reuse that same textual shape while remaining
     explicitly family-local;
   - that textual compatibility does not claim parity with the released
     `repo_symbol_catalog@1` `SymbolKind` universe, which still excludes
     `local_function`;
   - any further identity-law delta is forbidden in this slice.
5. Emitted-artifact strategy:
   - `V50-A` emits:
     - one scope manifest;
     - one deterministic symbol census;
     - one manifest-to-census coverage report;
   - `V50-A` does not emit semantic audit entries, semantic confidence claims, or
     audit-ledger coverage.
6. Coverage-law strategy:
   - the first shipped coverage report is manifest-to-census closure only;
   - it checks that:
     - all observed source files belong to the admitted manifest;
     - all manifest files are represented in the census source set;
     - all observed symbol kinds are admitted;
     - duplicate symbol IDs are rejected;
   - it must fail closed on mismatch.
7. Semantic-minimality strategy:
   - `V50-A` artifacts must remain semantically minimal enough that `V50-B` can later
     either:
     - reuse released `V49` primitives; or
     - explicitly remain independent;
   - `V50-A` may not quietly decide that question in field design, status vocabulary,
     or coverage semantics.

## Bounded Starter Vocabularies

The first `V50-A` release should freeze bounded starter vocabularies rather than leave
the family open-ended.

The intended bounded starter vocabularies are:

- `language`:
  - `python`
- `symbol_kind`:
  - `class`
  - `function`
  - `method`
  - `local_function`
- `shared_kind_overlap_with_repo_symbol_catalog`:
  - `class`
  - `function`
  - `method`
- `out_of_scope_released_repo_symbol_catalog_kinds`:
  - `module`
  - `attribute`
- `extractor_confidence_posture`:
  - `authoritative_for_explicit_parseable_defs`
- `parse_status`:
  - `parsed`
- `coverage_status`:
  - `closed_clean`
  - `fail_closed_mismatch`

Out-of-scope constructs in this slice are:

- semantic audit statuses;
- semantic evidence vocabularies;
- confidence-band semantics over audit claims;
- repo-wide symbol census;
- non-Python language handling;
- runtime or mutation surfaces;
- CLI, API, or web orchestration.

## Selected Schema Anchors

The first `V50-A` release should freeze the following contract anchors.

1. `adeu_symbol_audit_scope_manifest@1`
   - `scope_manifest_id`
   - `language`
   - `source_files` with:
     - `file_path`
     - `sha256`
   - `symbol_kinds_included`
   - `scope_hash`
2. `adeu_symbol_census_entry@1`
   - `symbol_id`
   - `module_path`
   - `qualname`
   - `symbol_name`
   - `symbol_kind`
   - `start_line`
   - `end_line`
   - `parent_symbol_id`
   - `signature_text`
   - `decorators_or_modifiers`
   - `class_bases`
   - `docstring_excerpt`
   - `census_index`
   - `extractor_confidence_posture`
   - `parse_status`
3. `adeu_symbol_census@1`
   - `schema`
   - `scope_manifest_ref`
   - `language`
   - `source_files`
   - `symbol_kinds_included`
   - `symbol_count`
   - `census_hash`
   - `symbols`
4. `adeu_symbol_audit_coverage_report@1`
   - `schema`
   - `scope_manifest_ref`
   - `census_hash`
   - `expected_source_files`
   - `observed_source_files`
   - `missing_source_files`
   - `unexpected_source_files`
   - `disallowed_symbol_kinds`
   - `duplicate_symbol_ids`
   - `coverage_status`
   - `coverage_gate_reason`

## Accepted And Reject Fixtures

The first `V50-A` release should include a bounded deterministic fixture set:

- one accepted scope manifest fixture over the exact pilot scope;
- one accepted symbol census fixture over the exact pilot scope bytes;
- one accepted manifest-to-census coverage fixture;
- one reject fixture for coverage mismatch caused by:
  - missing manifest source files;
  - out-of-manifest source drift;
  - disallowed symbol kind drift; or
  - duplicate symbol identity drift.

## Required Deliverables

The first `V50-A` release should add:

- `packages/adeu_symbol_audit/pyproject.toml`
- `packages/adeu_symbol_audit/src/adeu_symbol_audit/models.py`
- `packages/adeu_symbol_audit/src/adeu_symbol_audit/census.py`
- `packages/adeu_symbol_audit/src/adeu_symbol_audit/coverage.py`
- `packages/adeu_symbol_audit/src/adeu_symbol_audit/__init__.py`
- `packages/adeu_symbol_audit/tests/test_symbol_audit_models.py`
- `packages/adeu_symbol_audit/tests/test_symbol_audit_census.py`
- `packages/adeu_symbol_audit/tests/test_symbol_audit_coverage.py`
- committed `v50a` fixtures under `packages/adeu_symbol_audit/tests/fixtures/v50a/`

It should not add:

- `spu.py`
- `cli.py`
- API or web consumers
- repo-wide scope fixtures

## Acceptance

Accept this slice when:

- the repo-owned `adeu_symbol_audit` package is the only live owner of the shipped
  `V50-A` code;
- the exact three-file pilot manifest replays deterministically over committed bytes;
- the emitted scope manifest binds each admitted pilot file to one explicit `sha256`;
- census replay is deterministic and byte-identical on repeated runs;
- shared kinds reuse the released textual symbol-id law exactly;
- `local_function` remains explicit as one family-local extension and is never claimed
  as parity with released `repo_symbol_catalog@1`, even if it reuses the same textual
  symbol-id shape;
- manifest-to-census coverage fails closed on mismatch and replays deterministically;
- committed coverage artifacts type `missing_source_files` explicitly rather than only
  describing that drift in prose;
- committed fixtures prove local-function capture and coverage mismatch reject posture;
- the slice remains semantically minimal enough that the later `V50-B` semantic
  primitive decision stays open;
- no semantic audit ledger, CLI surface, repo-wide scope, or prototype-tree import
  ships in the same slice.

Do not accept this slice if:

- it silently changes shared symbol identity law;
- it silently changes the meaning of shared symbol kinds;
- it widens coverage semantics into audit-ledger semantics;
- it claims parity or supersession over released `repo_symbol_catalog@1`;
- it names the right pilot files but does not bind them to explicit content hashes;
- it imports prototype code wholesale into live package paths.

## Local Gate

- run `make check`
