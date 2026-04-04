# Locked Continuation vNext+122

Status: `V50-B` implementation contract.

## V122 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v50b_symbol_semantic_audit_contract@1",
  "target_arc": "vNext+122",
  "target_path": "V50-B",
  "target_scope": "bounded_repo_owned_one_audit_per_symbol_semantic_ledger_over_released_v50a_census_for_architecture_ir_pilot_scope",
  "implementation_packages": [
    "adeu_symbol_audit"
  ],
  "governing_released_stack": "V45_repo_description_plus_V49_semantic_forms_plus_V50A_symbol_census_and_coverage_on_main",
  "governing_stack_consumption_mode": "anchor_and_consumed_census_context_only_not_reopened_description_semantics_not_reopened_v49_semantic_substrate_semantics_not_reopened_v50a_scope_identity_or_coverage_semantics",
  "source_intake_bundle": "examples/external_prototypes/adeu-symbol-audit-v0-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "released_v50a_census_required": true,
  "released_v50a_closed_clean_coverage_required": true,
  "semantic_audit_spu_py_required": true,
  "single_census_input_initially_required": true,
  "single_closed_clean_coverage_input_initially_required": true,
  "single_audit_artifact_output_initially_required": true,
  "selected_schema_ids": [
    "adeu_symbol_semantic_evidence_ref@1",
    "adeu_symbol_semantic_audit_entry@1",
    "adeu_symbol_semantic_audit@1"
  ],
  "starter_symbol_kind_vocabulary_frozen": [
    "class",
    "function",
    "method",
    "local_function"
  ],
  "audit_status_vocabulary_frozen": [
    "audited_hypothesis",
    "audited_low_confidence",
    "unresolved"
  ],
  "confidence_band_vocabulary_frozen": [
    "low",
    "medium"
  ],
  "evidence_kind_vocabulary_frozen": [
    "source_span",
    "call_summary",
    "decorator",
    "baseclass"
  ],
  "semantic_vocabulary_posture_selected_in_v50b": "explicitly_independent_from_released_v49_primitives",
  "emitted_audit_top_level_posture_fields_required": [
    "semantic_vocabulary_posture",
    "spu_name",
    "spu_version"
  ],
  "one_audit_per_census_symbol_required": true,
  "evidence_ref_minimum_required": true,
  "source_span_evidence_ref_required": true,
  "source_span_detail_format_frozen": "{module_path}#L{start_line}-L{end_line}",
  "likely_canonical_family_is_family_local_heuristic_only": true,
  "closure_truth_remains_in_released_v50a": true,
  "semantic_uncertainty_cannot_redefine_closure_truth": true,
  "completion_status_surface_not_selected_here": true,
  "cli_orchestration_consumers_not_selected_here": true,
  "repo_wide_scope_not_selected_here": true,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v33.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS121.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md",
    "docs/DRAFT_ADEU_SYMBOL_AUDIT_V50A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_SYMBOL_AUDIT_V50B_IMPLEMENTATION_MAPPING_v0.md",
    "examples/external_prototypes/adeu-symbol-audit-v0-bundle/ALIGNMENT.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v33.md"
}
```

## Slice

- Arc label: `vNext+122`
- Family label: `V50-B`
- Scope label: bounded repo-owned one-audit-per-symbol semantic ledger over one
  released `V50-A` census for the `adeu_architecture_ir` pilot scope

## Objective

Release the bounded `V50-B` semantic-audit ledger lane by adding the first repo-owned
helper that consumes one released `adeu_symbol_census@1` plus one released
`adeu_symbol_audit_coverage_report@1` with `coverage_status = closed_clean`, and emits
one deterministic `adeu_symbol_semantic_audit@1` artifact with exactly one audit entry
per census symbol, explicit evidence minimums, and explicit semantic uncertainty
posture, while keeping released `V50-A` closure truth fixed and while explicitly
declining reuse of released `V49` primitives in this slice.

This slice must make explicit:

- one released census input posture only;
- one released closed-clean coverage context posture only;
- one emitted semantic-audit artifact posture only;
- one audit-entry schema over one released symbol identity law;
- one starter `audit_status` vocabulary;
- one starter `confidence_band` vocabulary;
- one starter evidence-kind vocabulary;
- one explicit independence posture from released `V49` primitives;
- one fail-closed posture for:
  - missing audit entry;
  - duplicate audit entry;
  - missing evidence refs;
  - missing `source_span` evidence;
  - unsupported `audit_status`;
  - unsupported `confidence_band`;
  - unsupported evidence kinds;
  - census/artifact mismatch.

This slice is ledger-first and still bounded. It does not authorize CLI/API/web
surfaces, repo-wide scope widening, runtime mutation behavior, a second semantic
substrate hidden behind `V49` names, or direct import of the prototype tree into live
package paths.

## Frozen Implementation Decisions

1. Package-ownership strategy:
   - `packages/adeu_symbol_audit` remains the sole implementation owner in this
     slice;
   - the imported intake bundle remains shaping evidence only and may not be treated as
     the live semantic-audit surface.
2. Input/output cardinality strategy:
   - one released `adeu_symbol_census@1` only;
   - one released `adeu_symbol_audit_coverage_report@1` with
     `coverage_status = closed_clean` only;
   - one emitted `adeu_symbol_semantic_audit@1` only;
   - exactly one audit entry per census symbol only;
   - no batching and no repo-wide scope in this slice.
3. Semantic-vocabulary strategy:
   - `V50-B` selects explicit independence from released `V49` primitives in this
     slice;
   - the audit artifact may not claim to be a `V49` normal form, parse result, or
     transform product;
   - the audit artifact may not smuggle a second hidden semantic substrate behind
     borrowed `V49` terminology.
4. Closure-truth strategy:
   - released `V50-A` coverage remains the authoritative closure/completion baseline;
   - the consumed coverage report must remain `closed_clean` and must match the
     consumed census by `scope_manifest_ref` and `census_hash`;
   - `V50-B` may add semantic uncertainty rows and diagnostics;
   - `V50-B` may not redefine or supersede released `V50-A` closure truth.
5. Audit-entry strategy:
   - every audit entry must carry:
     - `symbol_id`
     - `audit_status`
     - `confidence_band`
     - `role_summary`
     - `architectural_purpose`
     - `local_behavior_summary`
     - `inputs_outputs_summary`
     - `side_effect_profile`
     - `dependency_position`
     - `likely_canonical_family`
     - `evidence_refs`
   - optional support/projection fields may include:
     - `overlap_candidate_symbol_ids`
     - `abstraction_candidate_notes`
     - `uncertainty_notes`
   - `likely_canonical_family` remains a family-local heuristic label only and may not
     claim released `V49` canonical or normal-form authority;
   - no entry may omit `symbol_id` or reuse another entry’s `symbol_id`.
6. Evidence strategy:
   - every audit entry must carry at least one `evidence_ref`;
   - every audit entry must carry at least one `source_span` evidence ref;
   - starter admitted evidence kinds are:
     - `source_span`
     - `call_summary`
     - `decorator`
     - `baseclass`
   - `source_span.detail` must use the released census anchor format:
     - `{module_path}#L{start_line}-L{end_line}`
   - evidence refs must remain descriptive support for the emitted audit row and may
     not silently re-open closure truth.
7. Determinism strategy:
   - repeated audit emission over the same released census and the same deterministic
     auditing logic must produce byte-identical output;
   - audit-entry ordering must be deterministic and keyed to released census
     `symbols` order via `census_index`.
8. Widening strategy:
   - no completion-status surface here;
   - no CLI / runner surface here;
   - no repo-wide scope here;
   - no direct import of the prototype sample artifact as a live released fixture here.

## Bounded Starter Vocabularies

The first `V50-B` release should freeze bounded starter vocabularies rather than leave
the ledger open-ended.

The intended bounded starter vocabularies are:

- `audit_status`:
  - `audited_hypothesis`
  - `audited_low_confidence`
  - `unresolved`
- `confidence_band`:
  - `low`
  - `medium`
- `evidence_kind`:
  - `source_span`
  - `call_summary`
  - `decorator`
  - `baseclass`
- `semantic_vocabulary_posture`:
  - `explicit_independence_from_v49`

Out-of-scope constructs in this slice are:

- `V49` normal-form or parse-result refs inside the emitted audit artifact;
- completion-status or closure-gate artifacts;
- CLI, API, or web surfaces;
- repo-wide semantic audit;
- runtime mutation or worker-execution surfaces.

## Selected Schema Anchors

The first `V50-B` release should freeze the following contract anchors.

1. Consumed `adeu_symbol_census@1`
   - `schema`
   - `scope_manifest_ref`
   - `language`
   - `source_files`
     - `file_path`
     - `sha256`
   - `symbol_kinds_included`
   - `symbol_count`
   - `census_hash`
   - `symbols`
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
2. Consumed `adeu_symbol_audit_coverage_report@1`
   - `schema`
   - `scope_manifest_ref`
   - `census_scope_manifest_ref`
   - `census_hash`
   - `coverage_status`
   - `coverage_gate_reason`
   - expected value in this slice:
     - `coverage_status = closed_clean`
3. Emitted `adeu_symbol_semantic_evidence_ref@1`
   - `evidence_kind`
   - `detail`
4. Emitted `adeu_symbol_semantic_audit_entry@1`
   - `symbol_id`
   - `audit_status`
   - `confidence_band`
   - `role_summary`
   - `architectural_purpose`
   - `local_behavior_summary`
   - `inputs_outputs_summary`
   - `side_effect_profile`
   - `dependency_position`
   - `likely_canonical_family`
   - `overlap_candidate_symbol_ids`
   - `abstraction_candidate_notes`
   - `evidence_refs`
   - `uncertainty_notes`
5. Emitted `adeu_symbol_semantic_audit@1`
   - `schema`
   - `scope_manifest_ref`
   - `census_hash`
   - `semantic_vocabulary_posture`
   - `spu_name`
   - `spu_version`
   - `audit_entries`
   - `audit_hash`

## Audit Law

The first `V50-B` release should make semantic-audit behavior explicit.

- One released census plus one released `closed_clean` coverage report in implies one
  audit artifact out.
- The consumed coverage report must match the consumed census by `scope_manifest_ref`
  and `census_hash`, or the slice fails closed.
- Every released census symbol must receive exactly one audit entry.
- Audit entries must be keyed by the released `symbol_id` law from `V50-A`; they may
  not mint a new symbol identity basis.
- Duplicate or missing `symbol_id` coverage fails closed.
- `audited_hypothesis` and `audited_low_confidence` are evidence-backed hypotheses.
- `unresolved` is a typed uncertainty posture, not an excuse to omit the row.
- `low` and `medium` remain bounded semantic-uncertainty carriers only; they do not
  redefine released `V50-A` closure truth.
- `source_span.detail` must be reproducible directly from the released census row as
  `{module_path}#L{start_line}-L{end_line}`.
- `V50-B` explicitly remains independent from released `V49` primitives in this slice;
  if later family work wants a `V49` bridge, that is a later explicit seam.

## Accepted Starter Fixtures

The first `V50-B` release should include deterministic fixtures rich enough to prove:

- accepted one-audit-per-symbol replay over one released reference census;
- accepted low-confidence handling;
- accepted unresolved handling;
- fail-closed rejection on duplicate `symbol_id`;
- fail-closed rejection on missing `evidence_ref`;
- fail-closed rejection on missing `source_span`;
- fail-closed rejection on unsupported vocabulary values.

## Acceptance Gate

`vNext+122` is acceptable only if:

- repeated replay over the same released census is byte-identical;
- the consumed released coverage report is `closed_clean` and matches the consumed
  census by `scope_manifest_ref` and `census_hash`;
- every census symbol receives exactly one audit row;
- duplicate or missing audit rows fail closed;
- missing evidence minimums fail closed;
- unsupported starter vocabularies fail closed;
- emitted audit artifacts carry `semantic_vocabulary_posture`, `spu_name`, and
  `spu_version`;
- emitted audit rows remain explicitly independent from released `V49` primitives;
- no completion-status, CLI, or repo-wide scope widening ships in the slice.

## PR Shape

The implementation PR should stay bounded to:

- `packages/adeu_symbol_audit/src/adeu_symbol_audit/models.py`
- `packages/adeu_symbol_audit/src/adeu_symbol_audit/spu.py`
- `packages/adeu_symbol_audit/src/adeu_symbol_audit/__init__.py`
- `packages/adeu_symbol_audit/tests/`
- committed deterministic `v50b` fixtures

It should not widen into:

- `cli.py`
- repo-wide source enumeration
- live runtime surfaces
- `V49` package changes
- `V45` package changes
- unrelated workflow edits
