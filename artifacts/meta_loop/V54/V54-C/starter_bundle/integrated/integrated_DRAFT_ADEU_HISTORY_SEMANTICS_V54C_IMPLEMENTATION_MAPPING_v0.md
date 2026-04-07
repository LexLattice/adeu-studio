# Draft ADEU History Semantics V54C Implementation Mapping v0

Status: support note for the `V54-C` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the broader
`V54` family should narrow into the third live `V54-C` slice while keeping the
imported `adeu-history-semantics-bundle` as shaping evidence rather than live
authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md`
- `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS142.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS144.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS146.md`
- `examples/external_prototypes/adeu-history-semantics-bundle/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- one adjacent package home:
  - `packages/adeu_history_semantics`
- one bounded advisory artifact layer over the released `V54-A` and `V54-B` substrate:
  - history evidence ref
  - history O/E/D/U lane reconstruction
  - history O/E/D/U reconstruction packet
- one explicit four-lane O/E/D/U posture rather than a generic summary surface
- one explicit advisory-only interpretation posture with no workspace synthesis in this
  slice

## Re-Author With Repo Alignment

- consume the already released `V54-A` contracts unchanged:
  - `adeu_history_source_artifact@1`
  - `adeu_history_text_shape_signals@1`
  - `adeu_history_preclassification@1`
- consume the already released `V54-B` contracts unchanged:
  - `adeu_history_ledger_entry@1`
  - `adeu_history_ledger@1`
  - `adeu_history_slice@1`
  - `adeu_history_theme_anchor@1`
- release exactly three new repo-owned contracts:
  - `adeu_history_evidence_ref@1`
  - `adeu_history_odeu_lane_reconstruction@1`
  - `adeu_history_odeu_reconstruction_packet@1`
- keep evidence refs grounded to released ledger entries:
  - one `entry_id`
  - one inherited `role`
  - one non-empty `excerpt` already present in the referenced released `entry_text`
  - no synthetic paraphrase-only evidence objects
- keep exactly one packet per released slice:
  - downstream of one released `slice_id`
  - downstream of one released `theme_anchor_id`
  - downstream of one released `source_id`
- keep exactly one canonical `O/E/D/U` lane set per packet in this order:
  - `O`
  - `E`
  - `D`
  - `U`
- keep released lane presence semantics bounded to:
  - `present`
  - `weakly_present`
  - `underdetermined`
  - `not_salient`
- keep released lane explicitation semantics bounded to:
  - `locally_explicit`
  - `dialogically_explicitated`
  - `contextually_reconstructed`
  - `underdetermined`
- keep released dominant-role posture semantics bounded to:
  - `user_primary`
  - `assistant_explication`
  - `mixed`
  - `source_primary`
  - `none`
- keep `present` or `weakly_present` lanes fail-closed:
  - require non-empty `reconstruction_text`
  - require one or more lawful `evidence_refs`
- keep `underdetermined` or `not_salient` lanes explicit rather than repaired:
  - omit `reconstruction_text` entirely
  - no `evidence_refs`
  - `explicitation_status = underdetermined`
  - `dominant_role_posture = none`
- freeze packet identity law in `V54-C`:
  - `semantic_identity_mode = v54c_history_packet_hash_law`
  - `semantic_hash = lowercase_hex_sha256(canonical_json(packet_identity_basis))`,
    where the basis contains only:
    - `schema`
    - `source_id`
    - `slice_id`
    - `theme_anchor_id`
    - ordered `lane_reconstructions` reduced to:
      - `lane_id`
      - `presence_status`
      - `explicitation_status`
      - `dominant_role_posture`
      - `reconstruction_text`
      - ordered lawful evidence refs reduced to:
        - `entry_id`
        - `role`
        - `excerpt`
    - `semantic_identity_mode`
  - `packet_id = history_packet:{semantic_hash[:16]}`
  - `reintegrated_summary` is omitted in `V54-C`
- keep packets advisory and provenance-linked:
  - downstream of released source / slice / theme surfaces
  - no lane scoring
  - no warrant ranking
  - no workspace question generation
  - no workspace ordering or synthesis
- require regressions for:
  - locally explicit assistant-marked lane replay
  - dialogically explicitated mixed-role replay over a user-grounded theme anchor
  - weak or underdetermined lane replay
  - absent-lane synthesized-text rejection
  - evidence-ref grounding rejection
  - missing or duplicate lane rejection
  - non-canonical packet-id or semantic-hash replay rejection
  - unexpected `reintegrated_summary` rejection in `V54-C`
  - no workspace widening inside `V54-C`

## Instantiated Here

- `adeu_history_evidence_ref@1`
- `adeu_history_odeu_lane_reconstruction@1`
- `adeu_history_odeu_reconstruction_packet@1`

## Defer To Later Slice

- `adeu_history_workspace_question@1`
- `adeu_history_workspace_theme_frame@1`
- `adeu_history_workspace_snapshot@1`
- `adeu_history_semantic_bundle@1`
- shorthand `U:` / `A:` / `S:` source-domain widening
- `abstract_like` source-domain widening
- lane scoring, ranking, or warrant language
- workspace synthesis and cross-packet question generation
- API/UI/runtime, retrieval, or broader corpus-ingestion surfaces

## Do Not Import

- any implication that evidence refs or packets are new authority roots
- any packet construction that skips released slice/theme provenance
- any `underdetermined` or `not_salient` lane carrying synthesized
  `reconstruction_text`
- any evidence ref excerpt not actually present in the referenced released `entry_text`
- any packet-local `reintegrated_summary` inside `V54-C`
- any forced complete O/E/D/U symmetry when the local material is weak or
  underdetermined
- any workspace snapshot or end-to-end semantic-bundle claim inside `V54-C`
