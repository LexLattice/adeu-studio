# Locked Continuation vNext+142

Status: `V54-A` implementation contract.

Authority layer: lock.

## Controlling Authority Map

- planning:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md`
- support:
  - `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54A_IMPLEMENTATION_MAPPING_v0.md`
  - `examples/external_prototypes/adeu-history-semantics-bundle/ALIGNMENT.md`
  - `examples/external_prototypes/adeu-history-semantics-bundle/CLAIMED_SCOPE.md`
  - `docs/DRAFT_PARALLEL_ARC_META_LOOP_PROTOCOL_v0.md`
  - `docs/PARALLEL_ARC_META_LOOP_BATON_v0.json`

## V142 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v54a_history_source_authority_contract@1",
  "target_arc": "vNext+142",
  "target_path": "V54-A",
  "target_scope": "bounded_repo_owned_history_source_authority_and_preclassification_starter_over_one_explicit_role_header_conversation_history_domain_with_normalized_text_authority_root_prior_to_ledger_slice_theme_odeu_or_workspace_release",
  "implementation_packages": [
    "adeu_history_semantics"
  ],
  "selected_owner_surface": "packages/adeu_history_semantics",
  "selected_schema_ids": [
    "adeu_history_source_artifact@1",
    "adeu_history_text_shape_signals@1",
    "adeu_history_preclassification@1"
  ],
  "starter_source_domain": "conversation_history_with_explicit_role_headers",
  "starter_input_kind": "conversation_history",
  "selected_source_authority_semantics": "normalized_source_text_authoritative_after_line_ending_normalization",
  "starter_timestamp_prefix_format": "optional_bracketed_yyyy_mm_dd_hh_mm_immediately_before_full_role_header_only",
  "normalized_text_identity_basis": [
    "input_kind",
    "source_text_hash"
  ],
  "projection_only_source_metadata": [
    "source_label",
    "corpus_wave_posture",
    "source_notes"
  ],
  "deterministic_derived_overlay_schema_ids": [
    "adeu_history_text_shape_signals@1",
    "adeu_history_preclassification@1"
  ],
  "ledger_release_status": "deferred_to_later_family",
  "slice_and_theme_release_status": "deferred_to_later_family",
  "odeu_packet_release_status": "deferred_to_later_family",
  "workspace_release_status": "deferred_to_later_family",
  "abstract_like_source_status": "not_selected_yet",
  "shorthand_alias_and_grouping_hardening_status": "deferred_to_later_family",
  "whole_source_fail_closed_required": true,
  "package_schema_export_required": true,
  "root_spec_mirror_required": true,
  "export_helper_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v142_closeout.json",
    "artifacts/stop_gate/metrics_v142_closeout.json",
    "artifacts/stop_gate/report_v142_closeout.md"
  ]
}
```

## Objective

Release the bounded `V54-A` source-authority and preclassification starter seam by
defining one repo-owned `adeu_history_semantics` package under repo authority,
selecting normalized source text as the only starter authority root, and shipping the
repo-native schema/export posture for source, text-shape signal, and deterministic
preclassification artifacts only.

This slice exists to make three things explicit before any later ledger / slice / theme
or advisory reconstruction widening:

- one owner package only:
  - `packages/adeu_history_semantics`
- one bounded starter source domain only:
  - `conversation_history` with explicit `User:` / `Assistant:` / `System:` headers
- one starter authority ladder only:
  - source artifact:
    authority root
  - text-shape / preclassification:
    deterministic derived overlay
  - ledger / slice / theme:
    deferred_to_later_family
  - O/E/D/U packets:
    deferred_to_later_family
  - workspace synthesis:
    deferred_to_later_family

The imported `adeu-history-semantics-bundle` remains support-only shaping evidence in
this slice. It does not become precedent-bearing authority or a live package import by
default.

## Required Deliverables

The first `V54-A` release should add exactly these live implementation surfaces:

- `packages/adeu_history_semantics/src/adeu_history_semantics/models.py`
- `packages/adeu_history_semantics/src/adeu_history_semantics/preclassify.py`
- `packages/adeu_history_semantics/src/adeu_history_semantics/export_schema.py`
- `packages/adeu_history_semantics/src/adeu_history_semantics/__init__.py`
- package schema exports under:
  - `packages/adeu_history_semantics/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_history_semantics/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_history_semantics/tests/fixtures/v54a/`

This slice should not add:

- released `adeu_history_ledger_entry@1`,
  `adeu_history_ledger@1`,
  `adeu_history_slice@1`, or
  `adeu_history_theme_anchor@1` contracts;
- released `adeu_history_evidence_ref@1`,
  `adeu_history_odeu_lane_reconstruction@1`, or
  `adeu_history_odeu_reconstruction_packet@1` contracts;
- released `adeu_history_workspace_question@1`,
  `adeu_history_workspace_theme_frame@1`,
  `adeu_history_workspace_snapshot@1`, or
  `adeu_history_semantic_bundle@1` contracts;
- API, UI, runtime-worker, retrieval, or corpus-ingestion widening;
- raw-byte authority claims or dual raw-plus-normalized authority surfaces;
- `abstract_like` starter-domain widening.

## Frozen Implementation Decisions

### 1. Ownership And Authority Boundary

- `packages/adeu_history_semantics` remains the only active implementation package for
  `V54-A`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md` remains the planning authority for family/path
  selection only; implementation authority is carried by this lock.
- the broader family-to-slice narrowing decisions for `V54-A` are frozen in this
  lock.
- `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54_IMPLEMENTATION_MAPPING_v0.md` remains the
  support mapping reference for broader family shaping context only; it does not
  outrank or override this lock.
- `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54A_IMPLEMENTATION_MAPPING_v0.md` remains the
  support mapping for this starter slice only.
- the imported bundle alignment and claimed-scope notes remain support-only:
  - imported external `X2` bundle
  - `non_precedent`
  - intake evidence only
- `V54-A` may constrain later `V54` paths, but it may not mint:
  - ambient continuation inside `V49` or `V52`
  - implicit raw-byte authority
  - implicit acceptance of prototype parser heuristics for broader corpora

### 2. Source Authority Posture

- admit exactly one released authority-root contract:
  - `adeu_history_source_artifact@1`
- each starter source artifact must carry:
  - `schema`
  - `source_id`
  - `input_kind`
  - `source_label`
  - `source_text`
  - `source_text_hash`
  - `corpus_wave_posture`
  - `source_authority_posture`
  - ordered `source_notes`
- `input_kind` in the starter slice must remain exactly:
  - `conversation_history`
- the positively accepted starter source domain must remain exactly:
  - explicit role-header conversation histories using
    `User:` / `Assistant:` / `System:` message headers
- optional timestamp prefixes may appear only in this exact form:
  - `[` four-digit year `-` two-digit month `-` two-digit day space two-digit hour
    `:` two-digit minute `]`
  - the timestamp prefix must appear immediately before the full role header on the
    same line
  - when present, `timestamp_text` preserves the bracket contents only, for example
    `2026-02-02 10:00`
- shorthand `U:` / `A:` / `S:` aliases remain deferred to later family hardening.
- `source_authority_posture` in the starter slice must remain exactly:
  - `normalized_source_text_authoritative`
- normalized starter authority means:
  - line-ending normalization from `CRLF` / `CR` to `LF` is applied before hashing and
    stored in `source_text`
  - no broader whitespace rewriting, paraphrase, repair, or canonical prose cleanup is
    authorized
- `source_id` identity basis in the starter slice must remain exactly:
  - `input_kind`
  - `source_text_hash`
- `source_label`, `corpus_wave_posture`, and `source_notes` remain projection-only
  metadata:
  - they may constrain interpretation
  - they may vary without changing `source_id` when authoritative normalized text is
    unchanged
  - they may not mint a second source identity root
- raw bytes are not preserved as the starter authority surface:
  - raw-byte authority is `not_selected_yet`
  - dual raw-plus-normalized authority is `not_selected_yet`
- if any line in a candidate source falls outside the bounded starter source domain,
  `V54-A` must reject the whole source rather than silently dropping, repairing, or
  partially laundering malformed content into the released source contract.

### 3. Preclassification Posture

- admit exactly two released deterministic derived-overlay contracts:
  - `adeu_history_text_shape_signals@1`
  - `adeu_history_preclassification@1`
- each starter preclassification artifact must carry:
  - `schema`
  - `preclassification_id`
  - `source_id`
  - `order_index`
  - `message_text`
  - `source_line_start`
  - `source_line_end`
  - `role`
  - `origin_type`
  - ordered `source_declaration_hints`
  - optional `timestamp_text`
  - ordered `structural_markers`
  - `text_shape_signals`
- `preclassification_id` in the starter slice must remain source-grounded only:
  - it derives from `source_id` plus `order_index`
  - no alternate grouping identity surface is authorized in the starter slice
- `role` in the positively accepted starter slice must remain exactly:
  - `user`
  - `assistant`
  - `system`
- `origin_type` in the positively accepted starter slice must remain exactly:
  - `user_native`
  - `assistant_reply`
  - `system_instruction`
- starter `source_declaration_hints` remain deterministic reflections of source text
  only:
  - full role header presence
  - timestamp prefix present or absent
  - no interpretive or heuristic recovery hints
- starter `HistoryTextShapeSignals` remain count-based, deterministic, and
  provenance-linked only:
  - no heuristic confidence scores
  - no O/E/D/U lane scores
  - no interpretive warrants
- starter `structural_markers` remain source-local only:
  - they may describe directly observed line or block structure
  - they may not mint released ledger, slice, or theme authority in `V54-A`

### 4. Broader Family Narrowing Classification

The broader `V54` family surface narrows in `V54-A` as follows:

- `adeu_history_source_artifact@1`:
  - `instantiated_here`
- `adeu_history_text_shape_signals@1`:
  - `instantiated_here`
- `adeu_history_preclassification@1`:
  - `instantiated_here`
- `adeu_history_ledger_entry@1`:
  - `deferred_to_later_family`
- `adeu_history_ledger@1`:
  - `deferred_to_later_family`
- `adeu_history_slice@1`:
  - `deferred_to_later_family`
- `adeu_history_theme_anchor@1`:
  - `deferred_to_later_family`
- `adeu_history_evidence_ref@1`:
  - `deferred_to_later_family`
- `adeu_history_odeu_lane_reconstruction@1`:
  - `deferred_to_later_family`
- `adeu_history_odeu_reconstruction_packet@1`:
  - `deferred_to_later_family`
- `adeu_history_workspace_question@1`:
  - `deferred_to_later_family`
- `adeu_history_workspace_theme_frame@1`:
  - `deferred_to_later_family`
- `adeu_history_workspace_snapshot@1`:
  - `deferred_to_later_family`
- `adeu_history_semantic_bundle@1`:
  - `deferred_to_later_family`
- `abstract_like` input domain:
  - `not_selected_yet`
- raw-byte authority root:
  - `not_selected_yet`

## Bounded Starter Vocabularies

The first `V54-A` release should freeze:

- `input_kind`:
  - `conversation_history`
- `source_authority_posture`:
  - `normalized_source_text_authoritative`
- `role`:
  - `user`
  - `assistant`
  - `system`
- `origin_type`:
  - `user_native`
  - `assistant_reply`
  - `system_instruction`
- `corpus_wave_posture`:
  - `unassigned`
  - `wave_0_bootstrap_candidate`
  - `later_wave_candidate`

## Fixture And Test Expectations

The committed `v54a` fixture/test set should include at minimum:

- one positive starter source fixture:
  - explicit `User:` / `Assistant:` / `System:` role headers
  - optional exact `[YYYY-MM-DD HH:MM]` timestamp prefixes
  - projection-only source metadata present
- one positive normalization-equivalence fixture pair:
  - same bounded source content in `LF` and `CRLF`
  - same emitted `source_text_hash`
  - same emitted `source_id`
- one positive projection-only metadata fixture:
  - `source_label`, `corpus_wave_posture`, or `source_notes` may vary
  - source identity must remain unchanged when authoritative normalized text is
    unchanged
- reject fixtures for:
  - `abstract_like` starter input
  - unheadered conversation-history input
  - shorthand `U:` / `A:` / `S:` aliases
  - non-conforming timestamp prefixes
  - mixed in-domain and malformed blocks inside one source
  - attempted raw-byte authority claim
  - attempted release of ledger / slice / theme / O/E/D/U / workspace surfaces from
    the starter lane

## Acceptance

Accept `V54-A` when:

- the three new source / preclassification contracts validate and export cleanly;
- authoritative package schemas and root `spec/` mirrors agree deterministically;
- the starter source domain remains bounded to explicit full role-header
  `conversation_history` only;
- normalized-text authority is explicit and replayable, with no raw-byte overclaim;
- optional timestamp handling is explicit, mechanized, and fail-closed to one exact
  bracketed `YYYY-MM-DD HH:MM` prefix form only;
- source identity remains bound only to `input_kind` plus authoritative
  `source_text_hash`;
- projection-only source metadata does not mint alternate identity;
- text-shape and preclassification artifacts remain deterministic derived overlays
  only;
- no ledger, slice, theme, O/E/D/U, workspace, or end-to-end semantic-bundle contract
  ships in the starter slice;
- targeted tests cover positive replay plus reject fixtures for unsupported domain and
  widened-surface attempts.

Do not accept `V54-A` if:

- raw bytes are claimed as the authority root without byte-preserving contract
  surfaces;
- `abstract_like` or shorthand-alias conversation logs are silently admitted into the
  same starter contract;
- non-conforming or ambiguously placed timestamp prefixes are silently normalized into
  accepted starter sources;
- prototype reconstruction helpers or bundle-level artifacts are shipped as if already
  inside `V54-A`;
- the imported bundle is cited as live implementation authority rather than support-only
  shaping evidence.

## Local Gate

- keep this lock aligned with the checks actually run for the starter bundle:
  - `make arc-start-check ARC=142` if the canonical helper completes in this worktree
  - otherwise, record the exact worktree repo-root quirk plus the truthful substitute
    docs-only checks that were actually run
