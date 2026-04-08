# Draft ADEU History Semantics V54A Implementation Mapping v0

Status: support note for the `V54-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the broader
`V54` family should narrow into the first live `V54-A` starter slice while keeping the
imported `adeu-history-semantics-bundle` as shaping evidence rather than live
authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md`
- `docs/DRAFT_ADEU_HISTORY_SEMANTICS_V54_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS142.md`
- `examples/external_prototypes/adeu-history-semantics-bundle/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- one adjacent package home:
  - `packages/adeu_history_semantics`
- one bounded starter source-artifact posture rather than vague memory/runtime language:
  - history source artifact
  - text-shape signals
  - preclassification
- one deterministic compilation pipeline with bounded fixtures
- one package-first scope with no API/UI/runtime widening in starter posture
- one explicit-role-header conversation-history starter domain

## Re-Author With Repo Alignment

- create the repo-owned package scaffold under:
  - `packages/adeu_history_semantics/src/adeu_history_semantics/`
  - `packages/adeu_history_semantics/tests/`
- choose normalized source text after line-ending normalization as the only starter
  authority root
- keep source identity bound only to:
  - `input_kind`
  - `source_text_hash`
- keep `source_label`, `corpus_wave_posture`, and `source_notes` projection-only:
  - they may vary without changing source identity when authoritative normalized text
    is unchanged
- bound the starter source domain to explicit full role-header `conversation_history`
  only:
  - `User:`
  - `Assistant:`
  - `System:`
- if timestamps are present, accept only this exact prefix form:
  - bracketed `YYYY-MM-DD HH:MM`
  - immediately before the full role header on the same line
- reject the whole starter source if any line falls outside the accepted domain:
  - no partial salvage
  - no silent repair
  - no malformed-line dropping
- re-author repo-native schema exports, root `spec/` mirrors, and an export helper as
  part of `V54-A` itself

## Instantiated Here

- `adeu_history_source_artifact@1`
- `adeu_history_text_shape_signals@1`
- `adeu_history_preclassification@1`

## Defer To Later Slice

- `adeu_history_ledger_entry@1`
- `adeu_history_ledger@1`
- `adeu_history_slice@1`
- `adeu_history_theme_anchor@1`
- shorthand `U:` / `A:` / `S:` alias support
- grouping hardening and broader parser adequacy
- `abstract_like` starter-domain widening
- advisory O/E/D/U packet release
- advisory workspace synthesis
- end-to-end semantic bundle release
- API/UI/runtime, retrieval, or broader corpus-ingestion surfaces

## Do Not Import

- any implication that the imported overlay is already a repo continuation
- any claim that current prototype tests justify broader corpus ingestion by themselves
- raw-byte authority or dual-authority posture in the starter slice
- flexible or free-form timestamp parsing
- absence of package-local schema exports as if it were already a released contract
  lane
- ledger, slice, theme, O/E/D/U, or workspace artifacts as if they were already
  `instantiated_here`
