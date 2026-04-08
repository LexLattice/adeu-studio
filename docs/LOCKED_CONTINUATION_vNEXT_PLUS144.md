# Locked Continuation vNext+144

Status: `V54-B` implementation contract.

Authority layer: lock.

## Controlling Authority Map

- planning:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md`
- upstream released lock:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS142.md`
- support:
  - `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54B_IMPLEMENTATION_MAPPING_v0.md`
  - `examples/external_prototypes/adeu-history-semantics-bundle/ALIGNMENT.md`
  - `examples/external_prototypes/adeu-history-semantics-bundle/CLAIMED_SCOPE.md`
  - `docs/DRAFT_PARALLEL_ARC_META_LOOP_PROTOCOL_v0.md`
  - `docs/PARALLEL_ARC_META_LOOP_BATON_v0.json`

## V144 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v54b_history_ledger_slice_theme_contract@1",
  "target_arc": "vNext+144",
  "target_path": "V54-B",
  "target_scope": "bounded_repo_owned_history_ledger_slice_and_theme_release_over_released_v54a_source_and_preclassification_surfaces_with_deterministic_same_role_slice_grouping_and_no_advisory_reconstruction_or_workspace_widening",
  "implementation_packages": [
    "adeu_history_semantics"
  ],
  "selected_owner_surface": "packages/adeu_history_semantics",
  "upstream_released_schema_ids": [
    "adeu_history_source_artifact@1",
    "adeu_history_text_shape_signals@1",
    "adeu_history_preclassification@1"
  ],
  "selected_schema_ids": [
    "adeu_history_ledger_entry@1",
    "adeu_history_ledger@1",
    "adeu_history_slice@1",
    "adeu_history_theme_anchor@1"
  ],
  "upstream_source_authority_semantics_inherited_from_v54a": "normalized_source_text_authoritative_after_line_ending_normalization",
  "upstream_source_domain_inherited_from_v54a": "conversation_history_with_explicit_full_role_headers_only",
  "same_speaker_entry_merge_status": "forbidden_in_v54b_starter",
  "starter_slice_grouping_rule": "maximal_contiguous_same_role_run_over_released_preclassification_order",
  "starter_theme_anchor_grouping_rule": "group_slices_by_identical_deterministic_theme_key_only",
  "starter_theme_term_derivation_law_frozen": true,
  "starter_theme_key_derivation_law_frozen": true,
  "starter_theme_anchor_supporting_term_law_frozen": true,
  "starter_theme_derivation_fail_closed_when_no_candidate_terms_remain": true,
  "zero_entry_ledger_forbidden": true,
  "zero_slice_bundle_forbidden": true,
  "zero_theme_anchor_bundle_forbidden": true,
  "quoted_or_multiline_content_may_not_mint_new_entries_or_roles": true,
  "shorthand_alias_source_status": "deferred_to_later_v54_slice",
  "abstract_like_source_status": "not_selected_yet",
  "evidence_ref_release_status": "deferred_to_v54c",
  "odeu_packet_release_status": "deferred_to_v54c",
  "workspace_release_status": "deferred_to_v54d",
  "lane_scoring_status": "not_selected_yet",
  "package_schema_export_required": true,
  "root_spec_mirror_required": true,
  "export_helper_update_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v144_closeout.json",
    "artifacts/stop_gate/metrics_v144_closeout.json",
    "artifacts/stop_gate/report_v144_closeout.md"
  ]
}
```

## Objective

Release the bounded `V54-B` ledger / slice / theme starter seam by extending the
repo-owned `adeu_history_semantics` package over the already-released `V54-A` source
artifact and preclassification substrate only.

This slice exists to make four things explicit before any later advisory
reconstruction or workspace widening:

- one owner package only:
  - `packages/adeu_history_semantics`
- one inherited source-authority posture only:
  - normalized source text after line-ending normalization
- one new deterministic derived-overlay layer only:
  - ledger entry
  - ledger
  - slice
  - theme anchor
- one bounded grouping hardening lane only:
  - no same-speaker entry collapse
  - no quoted-content role laundering
  - no zero-entry / zero-slice / zero-theme apparent success

The imported `adeu-history-semantics-bundle` remains support-only shaping evidence in
this slice. It does not become precedent-bearing authority or a live package import by
default.

## Required Deliverables

The first `V54-B` release should add or extend exactly these live implementation
surfaces:

- `packages/adeu_history_semantics/src/adeu_history_semantics/models.py`
- `packages/adeu_history_semantics/src/adeu_history_semantics/preclassify.py`
- `packages/adeu_history_semantics/src/adeu_history_semantics/ledger.py`
- `packages/adeu_history_semantics/src/adeu_history_semantics/export_schema.py`
- `packages/adeu_history_semantics/src/adeu_history_semantics/__init__.py`
- package schema exports under:
  - `packages/adeu_history_semantics/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_history_semantics/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_history_semantics/tests/fixtures/v54b/`

This slice should not add:

- released `adeu_history_evidence_ref@1`,
  `adeu_history_odeu_lane_reconstruction@1`, or
  `adeu_history_odeu_reconstruction_packet@1` contracts;
- released `adeu_history_workspace_question@1`,
  `adeu_history_workspace_theme_frame@1`,
  `adeu_history_workspace_snapshot@1`, or
  `adeu_history_semantic_bundle@1` contracts;
- shorthand `U:` / `A:` / `S:` starter-domain widening;
- `abstract_like` starter-domain widening;
- lane scoring, advisory warrants, or theme-ranking semantics;
- API, UI, runtime-worker, retrieval, or corpus-ingestion widening.

## Frozen Implementation Decisions

### 1. Ownership And Upstream Inheritance

- `packages/adeu_history_semantics` remains the only active implementation package for
  `V54-B`.
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS142.md` remains authoritative for:
  - source-authority semantics
  - source identity law
  - starter timestamp law
  - explicit full role-header source-domain law
  - released text-shape / preclassification schema meaning
- `V54-B` may consume and extend the released `V54-A` substrate, but it may not reopen:
  - raw-byte authority
  - dual-authority posture
  - shorthand alias acceptance
  - `abstract_like` starter input
  - projection-only metadata identity law
- the imported bundle alignment and claimed-scope notes remain support-only:
  - imported external `X2` bundle
  - `non_precedent`
  - intake evidence only

### 2. Released `V54-B` Contract Set

- admit exactly four newly released contracts:
  - `adeu_history_ledger_entry@1`
  - `adeu_history_ledger@1`
  - `adeu_history_slice@1`
  - `adeu_history_theme_anchor@1`
- each newly released contract must remain downstream of the released `V54-A`
  `source_id` and `preclassification_id` surfaces.
- no alternate authority root is authorized in `V54-B`.
- ledger, slice, and theme anchors remain derived overlays:
  - deterministic
  - provenance-linked
  - bounded
  - not advisory winner claims

### 3. Ledger Entry And Ledger Law

- each ledger entry must reference exactly one released `HistoryPreclassification`.
- each ledger entry must carry at least:
  - `schema`
  - `entry_id`
  - `source_id`
  - `preclassification_id`
  - `order_index`
  - `entry_text`
  - `entry_text_hash`
  - `role`
  - `origin_type`
  - `source_line_start`
  - `source_line_end`
  - ordered `structural_markers`
- `entry_text` in the starter slice must remain identical to the released
  `preclassification.message_text`.
- `role`, `origin_type`, `source_line_start`, and `source_line_end` in the starter
  slice must remain inherited from the released preclassification rather than
  reinterpreted heuristically.
- adjacent same-speaker preclassifications may not be collapsed into one ledger entry:
  - one preclassification
  - one ledger entry
- each ledger must carry at least:
  - `schema`
  - `ledger_id`
  - `source_id`
  - ordered `entries`
  - `entry_count`
- zero-entry ledgers are forbidden.

### 4. Slice Law

- each slice must be a contiguous chronology-local run of ordered ledger entries.
- the starter grouping rule is frozen exactly as:
  - maximal contiguous same-role run over released `order_index`
- each slice must carry at least:
  - `schema`
  - `slice_id`
  - `source_id`
  - `slice_index`
  - ordered `entry_ids`
  - `chronology_start_order_index`
  - `chronology_end_order_index`
  - ordered `boundary_tags`
  - ordered `theme_terms`
  - `theme_label`
- starter `theme_terms` are frozen as deterministic slice-local lexical terms derived
  only from the ordered `entry_text` values of the slice's released ledger entries:
  - lowercase the entry text
  - split on non-alphanumeric boundaries
  - discard empty tokens
  - discard pure-digit tokens
  - discard tokens shorter than 4 characters
  - discard role tokens:
    - `user`
    - `assistant`
    - `system`
- `theme_terms` must be the ordered unique remaining candidate terms in first
  occurrence order across the slice's ordered entries;
- `theme_label` must be the single-space join of the first up to three
  slice-local `theme_terms`;
- if no lawful `theme_terms` remain for a slice after the frozen derivation above,
  `V54-B` must fail closed rather than minting an empty or helper-invented slice/theme
  surface;
- each ledger entry may belong to exactly one slice in the starter slice.
- zero-slice outputs are forbidden.
- quoted lines, code fences, blank lines, or other multi-line content inside one entry
  may influence boundary tags only through deterministic released markers:
  - they may not mint new roles
  - they may not split one ledger entry into multiple ledger entries

### 5. Theme Anchor Law

- theme anchors remain bounded interpretive overlays, not authority roots.
- each theme anchor must carry at least:
  - `schema`
  - `theme_anchor_id`
  - `source_id`
  - `theme_key`
  - `display_label`
  - ordered `slice_ids`
  - ordered `anchor_entry_ids`
  - ordered `supporting_terms`
- the starter theme-anchor grouping rule is frozen exactly as:
  - group slices by identical deterministic `theme_key` only
- `theme_key` for a slice must be the double-colon join of the first up to five
  `theme_terms` already derived by the frozen slice law above;
- every slice grouped into one theme anchor must already have the same derived
  `theme_key`;
- the emitted theme anchor `theme_key` must be that shared slice-local `theme_key`
  carried through unchanged;
- theme-anchor `supporting_terms` must be the ordered unique union of grouped slices'
  `theme_terms`, preserving slice order and then in-slice term order;
- theme-anchor `display_label` must be the `theme_label` from the first slice in the
  grouped `slice_ids` order;
- if no lawful slice-local `theme_key` can be derived, `V54-B` must fail closed
  rather than emitting a helper-invented theme anchor.
- zero-theme-anchor outputs are forbidden.
- `V54-B` may describe repeated themes; it may not emit:
  - winner language
  - role-fit language
  - O/E/D/U lane cues
  - inferential maturity scores

### 6. Parser / Grouping Hardening Boundary

- hardening in `V54-B` remains bounded to the already released explicit full
  role-header source domain only.
- `V54-B` must directly exercise regressions for:
  - consecutive same-speaker turns
  - quoted or pasted content staying inside the authored entry
  - multi-line entry stability
  - empty or degenerate upstream compilation failing closed
- `V54-B` does not authorize:
  - shorthand alias source acceptance
  - source-header reinterpretation
  - substring lane scoring
  - advisory O/E/D/U inference
  - workspace synthesis

### 7. Broader Family Narrowing Classification

The broader `V54` family surface narrows in `V54-B` as follows:

- `adeu_history_source_artifact@1`:
  - `already_released_upstream`
- `adeu_history_text_shape_signals@1`:
  - `already_released_upstream`
- `adeu_history_preclassification@1`:
  - `already_released_upstream`
- `adeu_history_ledger_entry@1`:
  - `instantiated_here`
- `adeu_history_ledger@1`:
  - `instantiated_here`
- `adeu_history_slice@1`:
  - `instantiated_here`
- `adeu_history_theme_anchor@1`:
  - `instantiated_here`
- `adeu_history_evidence_ref@1`:
  - `deferred_to_v54c`
- `adeu_history_odeu_lane_reconstruction@1`:
  - `deferred_to_v54c`
- `adeu_history_odeu_reconstruction_packet@1`:
  - `deferred_to_v54c`
- `adeu_history_workspace_question@1`:
  - `deferred_to_v54d`
- `adeu_history_workspace_theme_frame@1`:
  - `deferred_to_v54d`
- `adeu_history_workspace_snapshot@1`:
  - `deferred_to_v54d`

### 8. Starter Fixture Posture

The first `V54-B` release should include at least:

- one clean alternating-role reference source producing:
  - one lawful ledger
  - multiple lawful slices
  - one or more lawful theme anchors
- one positive consecutive same-speaker reference source proving:
  - same-speaker turns remain separate ledger entries
  - the same contiguous role run becomes one lawful slice
- one positive quoted or multi-line reference source proving:
  - quoted or fenced text stays inside entry identity
  - no accidental role laundering occurs
- one reject fixture for:
  - empty or degenerate upstream compilation
- one reject fixture for:
  - attempted shorthand alias or other out-of-domain source widening

## Validation Posture

- starter validation for this docs-only bundle remains:
  - `make arc-start-check ARC=144`
- full Python/package validation remains deferred until implementation work begins.
