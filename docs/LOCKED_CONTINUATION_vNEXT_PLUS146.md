# Locked Continuation vNext+146

Status: `V54-C` implementation contract.

Authority layer: lock.

## Controlling Authority Map

- planning:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md`
- upstream released lock:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS142.md`
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS144.md`
- architecture / decomposition:
  - `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54_IMPLEMENTATION_MAPPING_v0.md`
- support:
  - `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54C_IMPLEMENTATION_MAPPING_v0.md`
  - `examples/external_prototypes/adeu-history-semantics-bundle/ALIGNMENT.md`
  - `examples/external_prototypes/adeu-history-semantics-bundle/CLAIMED_SCOPE.md`
  - `docs/DRAFT_PARALLEL_ARC_META_LOOP_PROTOCOL_v0.md`
  - `docs/PARALLEL_ARC_META_LOOP_BATON_v0.json`

## V146 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v54c_history_odeu_reconstruction_contract@1",
  "target_arc": "vNext+146",
  "target_path": "V54-C",
  "target_scope": "bounded_repo_owned_history_advisory_evidence_ref_and_odeu_reconstruction_release_over_released_v54a_source_and_v54b_ledger_slice_theme_surfaces_with_explicit_advisory_posture_and_no_workspace_synthesis_widening",
  "implementation_packages": [
    "adeu_history_semantics"
  ],
  "selected_owner_surface": "packages/adeu_history_semantics",
  "upstream_released_schema_ids": [
    "adeu_history_source_artifact@1",
    "adeu_history_text_shape_signals@1",
    "adeu_history_preclassification@1",
    "adeu_history_ledger_entry@1",
    "adeu_history_ledger@1",
    "adeu_history_slice@1",
    "adeu_history_theme_anchor@1"
  ],
  "selected_schema_ids": [
    "adeu_history_evidence_ref@1",
    "adeu_history_odeu_lane_reconstruction@1",
    "adeu_history_odeu_reconstruction_packet@1"
  ],
  "upstream_source_authority_semantics_inherited_from_v54a": "normalized_source_text_authoritative_after_line_ending_normalization",
  "upstream_source_domain_inherited_from_v54a": "conversation_history_with_explicit_full_role_headers_only",
  "upstream_grouping_and_theme_law_inherited_from_v54b": true,
  "selected_lane_order": [
    "O",
    "E",
    "D",
    "U"
  ],
  "selected_lane_presence_statuses": [
    "present",
    "weakly_present",
    "underdetermined",
    "not_salient"
  ],
  "selected_lane_explicitation_statuses": [
    "locally_explicit",
    "dialogically_explicitated",
    "contextually_reconstructed",
    "underdetermined"
  ],
  "selected_dominant_role_postures": [
    "user_primary",
    "assistant_explication",
    "mixed",
    "source_primary",
    "none"
  ],
  "evidence_refs_must_resolve_to_released_ledger_entries": true,
  "present_or_weak_lanes_require_non_empty_text_and_evidence_refs": true,
  "absent_lanes_may_not_carry_evidence_refs": true,
  "absent_lanes_must_omit_reconstruction_text": true,
  "absent_lanes_require_underdetermined_explicitation_and_none_dominant_role": true,
  "exactly_one_packet_per_released_slice_required": true,
  "packet_authority_posture": "advisory_overlay_only",
  "packet_semantic_identity_mode_literal": "v54c_history_packet_hash_law",
  "packet_semantic_hash_basis": "sha256_canonical_json_over_schema_source_slice_theme_canonical_lanes_and_semantic_identity_mode_only",
  "packet_id_derivation": "history_packet_prefix_plus_first_16_hex_of_semantic_hash",
  "packet_reintegrated_summary_status": "omitted_in_v54c",
  "workspace_release_status": "deferred_to_v54d",
  "semantic_bundle_release_status": "deferred_to_later_family",
  "package_schema_export_required": true,
  "root_spec_mirror_required": true,
  "export_helper_update_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v146_closeout.json",
    "artifacts/stop_gate/metrics_v146_closeout.json",
    "artifacts/stop_gate/report_v146_closeout.md"
  ]
}
```

## Objective

Release the bounded `V54-C` advisory reconstruction seam by extending the already
released `V54-A` source authority and `V54-B` ledger / slice / theme substrate with
repo-owned evidence-ref and O/E/D/U packet artifacts only.

This slice exists to make four things explicit before any later workspace synthesis:

- one owner package only:
  - `packages/adeu_history_semantics`
- one inherited authority ladder only:
  - `V54-A` source authority remains the root
  - `V54-B` ledger / slice / theme remains the bounded upstream interpretive substrate
- one advisory reconstruction layer only:
  - evidence ref
  - O/E/D/U lane reconstruction
  - O/E/D/U reconstruction packet
- one explicit defer boundary only:
  - workspace question / theme frame / snapshot remain deferred to `V54-D`

The imported `adeu-history-semantics-bundle` remains support-only shaping evidence in
this slice. It does not become precedent-bearing authority or a live package import by
default.

## Required Deliverables

The first `V54-C` release should add or extend exactly these live implementation
surfaces:

- `packages/adeu_history_semantics/src/adeu_history_semantics/models.py`
- `packages/adeu_history_semantics/src/adeu_history_semantics/reconstruct.py`
- `packages/adeu_history_semantics/src/adeu_history_semantics/export_schema.py`
- `packages/adeu_history_semantics/src/adeu_history_semantics/__init__.py`
- package schema exports under:
  - `packages/adeu_history_semantics/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_history_semantics/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_history_semantics/tests/fixtures/v54c/`

This slice should not add:

- released `adeu_history_workspace_question@1`,
  `adeu_history_workspace_theme_frame@1`, or
  `adeu_history_workspace_snapshot@1` contracts;
- released `adeu_history_semantic_bundle@1`;
- shorthand `U:` / `A:` / `S:` source-domain widening;
- `abstract_like` source-domain widening;
- lane scoring, warrant ranking, workspace question generation, or cross-packet
  synthesis;
- API, UI, runtime-worker, retrieval, or broader corpus-ingestion widening.

## Frozen Implementation Decisions

### 1. Ownership And Upstream Inheritance

- `packages/adeu_history_semantics` remains the only active implementation package for
  `V54-C`.
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS142.md` remains authoritative for:
  - source-authority semantics
  - source identity law
  - starter source-domain law
  - released text-shape / preclassification schema meaning
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS144.md` remains authoritative for:
  - one-preclassification-to-one-ledger-entry law
  - maximal contiguous same-role slice grouping law
  - deterministic theme-term / theme-label / theme-key / theme-anchor law
- `V54-C` may consume and extend the released `V54-A` and `V54-B` substrate, but it
  may not reopen:
  - raw-byte or dual-authority posture
  - shorthand alias acceptance
  - `abstract_like` starter input
  - same-speaker entry collapse
  - alternate theme grouping or ranking law
- the imported bundle alignment and claimed-scope notes remain support-only:
  - imported external `X2` bundle
  - `non_precedent`
  - intake evidence only

### 2. Released `V54-C` Contract Set

- admit exactly three newly released contracts:
  - `adeu_history_evidence_ref@1`
  - `adeu_history_odeu_lane_reconstruction@1`
  - `adeu_history_odeu_reconstruction_packet@1`
- each newly released contract must remain downstream of the released:
  - `source_id`
  - `entry_id`
  - `slice_id`
  - `theme_anchor_id`
- no alternate authority root is authorized in `V54-C`.
- O/E/D/U packets remain advisory reconstruction overlays:
  - provenance-linked
  - bounded
  - explicit about weakness or underdetermination
  - not workspace synthesis
  - not authority-root conclusions

### 3. Evidence-Ref Law

- each evidence ref must reference exactly one released `HistoryLedgerEntry`.
- each evidence ref must carry at least:
  - `schema`
  - `entry_id`
  - `role`
  - `excerpt`
- `role` in the starter slice must remain inherited from the referenced released
  ledger entry / preclassification rather than reclassified heuristically.
- `excerpt` in the starter slice must stay source-grounded:
  - non-empty
  - text already present inside the referenced released `entry_text`
  - not a synthetic paraphrase presented as direct evidence
- evidence refs remain descriptive provenance hooks only:
  - they do not mint a separate authority root
  - they do not replace the released source / ledger surfaces

### 4. Lane-Reconstruction Law

- each lane reconstruction must carry at least:
  - `schema`
  - `lane_id`
  - `presence_status`
  - `explicitation_status`
  - `dominant_role_posture`
  - optional `reconstruction_text`
  - ordered `evidence_refs`
- `lane_id` in the starter slice must remain exactly one of:
  - `O`
  - `E`
  - `D`
  - `U`
- `presence_status` in the starter slice must remain bounded to:
  - `present`
  - `weakly_present`
  - `underdetermined`
  - `not_salient`
- `explicitation_status` in the starter slice must remain bounded to:
  - `locally_explicit`
  - `dialogically_explicitated`
  - `contextually_reconstructed`
  - `underdetermined`
- `dominant_role_posture` in the starter slice must remain bounded to:
  - `user_primary`
  - `assistant_explication`
  - `mixed`
  - `source_primary`
  - `none`
- `present` or `weakly_present` lanes must carry:
  - non-empty `reconstruction_text`
  - one or more lawful `evidence_refs`
- `underdetermined` or `not_salient` lanes must:
  - stay explicit as absent or weak rather than silently backfilled
  - omit `reconstruction_text` entirely
  - carry no `evidence_refs`
  - use `explicitation_status = underdetermined`
  - use `dominant_role_posture = none`
- lane posture remains descriptive and advisory only:
  - no lane scoring
  - no winner language
  - no workspace question generation

### 5. Packet Law

- each packet must be downstream of exactly one released slice and one released theme
  anchor.
- the starter slice must release exactly one packet per released slice.
- each packet must carry at least:
  - `schema`
  - `packet_id`
  - `source_id`
  - `slice_id`
  - `theme_anchor_id`
  - ordered `lane_reconstructions`
  - `interpretation_authority_posture`
  - `semantic_identity_mode`
  - `semantic_hash`
- `lane_reconstructions` in the starter slice must contain exactly one lawful lane for
  each of:
  - `O`
  - `E`
  - `D`
  - `U`
- packet lane order must remain deterministic:
  - `O`
  - `E`
  - `D`
  - `U`
- `interpretation_authority_posture` in the starter slice must remain exactly:
  - `advisory_overlay_only`
- `semantic_identity_mode` in the starter slice must remain exactly:
  - `v54c_history_packet_hash_law`
- `semantic_hash` in the starter slice must equal the lowercase hex SHA-256 of the
  canonical JSON packet identity basis containing exactly:
  - `schema`
  - `source_id`
  - `slice_id`
  - `theme_anchor_id`
  - ordered `lane_reconstructions`, with each lane reduced to:
    - `lane_id`
    - `presence_status`
    - `explicitation_status`
    - `dominant_role_posture`
    - `reconstruction_text`
    - ordered `evidence_refs`, with each evidence ref reduced to:
      - `entry_id`
      - `role`
      - `excerpt`
  - `semantic_identity_mode`
- `packet_id` in the starter slice must remain exactly:
  - `history_packet:{semantic_hash[:16]}`
- `reintegrated_summary` is omitted in `V54-C`:
  - it is not part of the starter packet contract
  - it may not appear as a support field or alternate identity carrier in this slice
- packets in `V54-C` do not authorize:
  - cross-slice workspace ordering
  - theme-frame synthesis
  - question generation
  - end-to-end semantic-bundle release

### 6. Broader Family Narrowing Classification

The broader `V54` family surface narrows in `V54-C` as follows:

- `adeu_history_source_artifact@1`:
  - `already_released_upstream`
- `adeu_history_text_shape_signals@1`:
  - `already_released_upstream`
- `adeu_history_preclassification@1`:
  - `already_released_upstream`
- `adeu_history_ledger_entry@1`:
  - `already_released_upstream`
- `adeu_history_ledger@1`:
  - `already_released_upstream`
- `adeu_history_slice@1`:
  - `already_released_upstream`
- `adeu_history_theme_anchor@1`:
  - `already_released_upstream`
- `adeu_history_evidence_ref@1`:
  - `instantiated_here`
- `adeu_history_odeu_lane_reconstruction@1`:
  - `instantiated_here`
- `adeu_history_odeu_reconstruction_packet@1`:
  - `instantiated_here`
- `adeu_history_workspace_question@1`:
  - `deferred_to_v54d`
- `adeu_history_workspace_theme_frame@1`:
  - `deferred_to_v54d`
- `adeu_history_workspace_snapshot@1`:
  - `deferred_to_v54d`
- `adeu_history_semantic_bundle@1`:
  - `deferred_to_later_family`

### 7. Starter Fixture Posture

The first `V54-C` release should include at least:

- one positive reference source producing:
  - one lawful packet per released slice
  - one explicit four-lane `O/E/D/U` packet
  - user-grounded theme provenance with retained assistant explication when present
- one positive mixed-role fixture proving:
  - dialogical explication remains advisory
  - packet evidence stays grounded in concrete released entry excerpts
- one positive weak-lane or underdetermined fixture proving:
  - absence is recorded explicitly
  - the implementation does not silently manufacture full four-lane symmetry
- one reject fixture for:
  - absent-lane synthesized `reconstruction_text`
- one reject fixture for:
  - synthetic or ungrounded evidence refs
- one reject fixture for:
  - missing, duplicate, or non-canonical lane sets
- one reject fixture for:
  - non-canonical packet identity replay across `semantic_identity_mode`,
    `semantic_hash`, and `packet_id`
- one reject fixture for:
  - unexpected `reintegrated_summary` presence in `V54-C`
- one reject fixture for:
  - attempted workspace-field or semantic-bundle widening inside `V54-C`

## Validation Posture

- starter validation for this docs-only bundle remains:
  - `make arc-start-check ARC=146`
- full Python/package validation remains deferred until implementation work begins.
