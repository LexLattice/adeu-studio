# Draft ADEU History Semantics V54B Implementation Mapping v0

Status: support note for the `V54-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the broader
`V54` family should narrow into the second live `V54-B` slice while keeping the
imported `adeu-history-semantics-bundle` as shaping evidence rather than live
authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md`
- `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS142.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS144.md`
- `examples/external_prototypes/adeu-history-semantics-bundle/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- one adjacent package home:
  - `packages/adeu_history_semantics`
- one bounded downstream artifact layer over released `V54-A` source/preclassification:
  - history ledger entry
  - history ledger
  - history slice
  - history theme anchor
- one deterministic package-first scope with no API/UI/runtime widening
- one descriptive theme-anchor posture rather than winner or recommendation language

## Re-Author With Repo Alignment

- consume the already released `V54-A` contracts unchanged:
  - `adeu_history_source_artifact@1`
  - `adeu_history_text_shape_signals@1`
  - `adeu_history_preclassification@1`
- release exactly four new repo-owned contracts:
  - `adeu_history_ledger_entry@1`
  - `adeu_history_ledger@1`
  - `adeu_history_slice@1`
  - `adeu_history_theme_anchor@1`
- keep one ledger entry per released preclassification:
  - no same-speaker entry collapse
  - no role laundering from quoted or pasted text
- keep the source-domain boundary inherited from `V54-A`:
  - explicit full role-header `conversation_history` only
  - shorthand alias support remains deferred
  - `abstract_like` remains `not_selected_yet`
- freeze one bounded slice law:
  - maximal contiguous same-role run over released `order_index`
- freeze one bounded theme-anchor law:
  - group slices by identical deterministic `theme_key` only
  - no ranking
  - no O/E/D/U lane scoring
  - no workspace interpretation
- require regressions for:
  - consecutive same-speaker chronology
  - quoted or fenced multi-line stability
  - degenerate-input fail-close
  - out-of-domain shorthand rejection

## Instantiated Here

- `adeu_history_ledger_entry@1`
- `adeu_history_ledger@1`
- `adeu_history_slice@1`
- `adeu_history_theme_anchor@1`

## Defer To Later Slice

- `adeu_history_evidence_ref@1`
- `adeu_history_odeu_lane_reconstruction@1`
- `adeu_history_odeu_reconstruction_packet@1`
- `adeu_history_workspace_question@1`
- `adeu_history_workspace_theme_frame@1`
- `adeu_history_workspace_snapshot@1`
- shorthand `U:` / `A:` / `S:` source-domain widening
- `abstract_like` source-domain widening
- advisory lane scoring or warrant language
- workspace synthesis and end-to-end semantic bundle release
- API/UI/runtime, retrieval, or broader corpus-ingestion surfaces

## Do Not Import

- any implication that `V54-B` reopens `V54-A` source authority or source identity law
- any prototype-style lane scoring or inferential maturity posture
- any claim that quoted or pasted text can author a new role or new entry by itself
- any zero-entry / zero-slice / zero-theme output that appears lawful
- any implication that the imported overlay is already a repo continuation
