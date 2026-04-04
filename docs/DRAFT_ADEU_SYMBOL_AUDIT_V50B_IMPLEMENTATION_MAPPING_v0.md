# Draft ADEU Symbol Audit V50B Implementation Mapping v0

Status: support-layer implementation mapping for `V50-B`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the imported
`adeu_symbol_audit` prototype material to the repo-owned `V50-B` semantic-audit
ledger slice so the implementation can stay grounded without importing prototype audit
semantics as live authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v33.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS122.md`
- `examples/external_prototypes/adeu-symbol-audit-v0-bundle/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- one-audit-per-symbol posture over one released census
- released census-order basis from `V50-A`:
  - top-level `symbols`
  - per-row `census_index`
  - typed `source_files` with `file_path` plus `sha256`
- released `V50-A` closed-clean coverage as fixed upstream context, not as something
  `V50-B` redefines
- starter `audit_status` vocabulary:
  - `audited_hypothesis`
  - `audited_low_confidence`
  - `unresolved`
- starter `confidence_band` vocabulary:
  - `low`
  - `medium`
- starter evidence kinds already grounded in the prototype sample:
  - `source_span`
  - `call_summary`
  - `decorator`
  - `baseclass`
- descriptive/support fields such as:
  - `role_summary`
  - `architectural_purpose`
  - `local_behavior_summary`
  - `inputs_outputs_summary`
  - `side_effect_profile`
  - `dependency_position`
  - `likely_canonical_family`
  - `overlap_candidate_symbol_ids`
  - `abstraction_candidate_notes`
  - `uncertainty_notes`

## Re-Author With Repo Alignment

- live owner:
  - `packages/adeu_symbol_audit/src/adeu_symbol_audit/spu.py`
- repo-owned models and validation:
  - fail-closed one-audit-per-symbol law
  - fail-closed `closed_clean` coverage-to-census match law
  - fail-closed evidence minimums
  - deterministic ordering keyed to released census `symbols` order via `census_index`
- explicit evidence encoding:
  - `source_span.detail = {module_path}#L{start_line}-L{end_line}`
- explicit independence posture:
  - do not reuse released `V49` primitives in this slice
  - do not borrow `V49` schema names as if they apply to the audit ledger
  - keep `likely_canonical_family` as a family-local heuristic label only, not a
    released `V49` canonical claim
- repo-native fixtures and targeted tests:
  - accepted replay
  - low-confidence and unresolved rows
  - duplicate / missing / evidence-thin failure cases

## Defer To Later Slice

- CLI or runner surfaces to `V50-C`
- repo-wide scope widening beyond the released `V50-A` pilot scope
- any later explicit bridge from the audit ledger into released `V49` primitives
- any completion-status or orchestration summary surface over the audit ledger

## Do Not Import

- the prototype `coverage.py` completion-status semantics as live `V50-B` truth
- the prototype CLI surface
- the prototype sample JSON wholesale as if it were already a released repo fixture
- any prototype-local semantic idiom as if it were released `V49`
