# Assessment vNext+142 Edges

Status: planning-edge assessment for `V54-A`.

Authority layer: planning assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS142_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Source Authority Semantics Stay Ambiguous

- Risk:
  the family could keep talking as if raw history were authoritative while actually
  hashing a normalized text variant, leaving authority posture soft and misleading.
- Response:
  freeze `V54-A` to normalized source text authoritative after line-ending
  normalization only, and keep raw-byte authority `not_selected_yet`.

### Edge 2: Imported Prototype Becomes Silent Family Authority

- Risk:
  the normalized intake bundle could be treated as if it already were the repo-owned
  `V54` family instead of support-only evidence.
- Response:
  keep the external bundle explicitly `non_precedent`, support-only, and re-author the
  first live contract under `packages/adeu_history_semantics` plus repo-native schema
  exports.

### Edge 3: Starter Scope Widens Across Multiple Source Domains

- Risk:
  `V54-A` could quietly try to cover both conversation-history and abstract-like
  sources before the authority root is stable.
- Response:
  keep the starter source domain bounded to explicit-role-header
  `conversation_history` only and classify `abstract_like` as `not_selected_yet`.

### Edge 4: Preclassification Hints Turn Into Slice Or Theme Authority

- Risk:
  `local_group_id` and `suggested_slice_boundary_before` could look structured enough
  that later readers treat them as already-released slice or theme contracts.
- Response:
  keep source, text-shape, preclassification, and ledger artifacts as the only
  `instantiated_here` surfaces in `V54-A`; defer slice and theme artifacts explicitly
  to later family work.

### Edge 5: Advisory Reconstruction Reappears Too Early

- Risk:
  the starter package could smuggle in O/E/D/U packets, evidence refs, workspace
  questions, or end-to-end bundles before source authority and export posture are
  stable.
- Response:
  keep O/E/D/U and workspace seams explicitly `deferred_to_later_family`, with no
  released advisory reconstruction artifacts in `V54-A`.

### Edge 6: Export Posture Remains Soft

- Risk:
  the family could ship Pydantic models and tests while still omitting package schema
  exports, root `spec/` mirrors, and an export helper, repeating the imported
  bundle’s contract gap.
- Response:
  make repo-native schema export posture part of the starter slice itself rather than a
  cleanup note for later.

### Edge 7: Starter Parser Coverage Overclaims Corpus Adequacy

- Risk:
  a small deterministic starter parser could be mistaken for evidence that shorthand
  aliases, same-speaker grouping, quote/paste detection, and broader corpus ingestion
  are already adequate.
- Response:
  keep the starter domain narrow and classify shorthand alias support, grouping
  hardening, and broader parser adequacy as `deferred_to_later_family`.

### Edge 8: Projection-Only Metadata Quietly Mints Identity

- Risk:
  source labels, wave posture tags, or notes could drift into implicit identity law
  even though the family claims to be rooted in authoritative source text.
- Response:
  freeze starter identity basis to `input_kind` plus `source_text_hash` only and keep
  other source metadata explicitly projection-only.

## Current Judgment

- `V54-A` is worth implementing now because the repo already has:
  - a planning family selection in `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md`
  - a decomposition note in
    `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54_IMPLEMENTATION_MAPPING_v0.md`
  - a normalized imported bundle that is strong shaping evidence but not live
    authority
- the right starter boundary is narrow:
  - one repo-owned package
  - one explicit normalized-text authority root
  - one explicit-role-header `conversation_history` domain
  - one deterministic text-shape / preclassification / ledger overlay only
  - explicit deferral of slice, theme, O/E/D/U, and workspace seams
  - explicit repo-native schema/export posture
- the next meaningful work after this starter contract should remain sequenced:
  - `V54-B` for released slice/theme substrate plus parser/grouping hardening
  - `V54-C` for advisory O/E/D/U packet release only
  - `V54-D` for bounded workspace synthesis only
