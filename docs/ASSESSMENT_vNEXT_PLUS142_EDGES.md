# Assessment vNext+142 Edges

Status: post-closeout edge assessment for `V54-A` (April 7, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS142_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Authority Rhetoric Could Drift Back Toward Raw-Source Claims

- Risk:
  the released starter could still be spoken about as if it preserved literal raw
  bytes when it actually normalizes line endings before storing and hashing
  authoritative source text.
- Response:
  keep the released posture explicit:
  `normalized_source_text_authoritative_after_line_ending_normalization`, and defer
  raw-byte or dual-authority surfaces to a later family decision if ever selected.
- Closeout Evidence:
  the shipped source artifact and tests bind starter identity to `input_kind` plus
  normalized `source_text_hash` only, with line-ending normalization replay covered by
  deterministic fixtures.

### Edge 2: Starter Domain Could Quietly Widen Beyond Explicit Role Headers

- Risk:
  shorthand aliases, abstract-like sources, or mixed-domain material could be treated
  as if the starter release already covered them.
- Response:
  keep the released input domain bounded to explicit full role-header
  `conversation_history` only and keep shorthand alias support plus `abstract_like`
  widening deferred.
- Closeout Evidence:
  shipped reject fixtures cover shorthand `U:` / `A:` / `S:` input, unheadered
  conversation history, mixed malformed blocks, and widened-surface attempts.

### Edge 3: Timestamp Parsing Could Become Helper Taste Again

- Risk:
  optional timestamp handling could drift from one exact released form into a broader
  parser that silently interprets timestamp-like prefixes by discretion.
- Response:
  keep the starter law at one optional bracketed `YYYY-MM-DD HH:MM` prefix immediately
  before the full role header only.
- Closeout Evidence:
  shipped parsing logic plus review hardening `00c44494d3fcdb17543a1115f7ad92554ef9b2e2`
  admit bracket-led valid content without widening the accepted timestamp surface.

### Edge 4: Whole-Source Fail-Closed Posture Could Erode

- Risk:
  malformed blocks inside an otherwise valid source could be silently dropped or
  normalized into apparent success.
- Response:
  keep the released starter posture at whole-source reject on any out-of-domain line.
- Closeout Evidence:
  shipped fixtures reject mixed-domain malformed blocks, malformed timestamp
  placement, shorthand aliases, and unheadered sources rather than partially salvaging
  them.

### Edge 5: Projection-Only Metadata Could Start Minting Identity

- Risk:
  `source_label`, `corpus_wave_posture`, or `source_notes` could drift into hidden
  identity law even though the family claims to be rooted in authoritative normalized
  source text.
- Response:
  keep starter identity bound only to `input_kind` plus normalized `source_text_hash`
  and keep the other source metadata explicitly projection-only.
- Closeout Evidence:
  shipped tests prove label / wave / notes variation does not mint alternate identity
  when authoritative normalized text is unchanged.

### Edge 6: Export Posture Could Soften Back Into Model-Only Ownership

- Risk:
  the family could start relying on Python model classes alone and let schema exports,
  root mirrors, or export helper discipline drift.
- Response:
  keep package-local schema exports, root `spec/` mirrors, and export-helper parity as
  part of the released starter contract itself.
- Closeout Evidence:
  `v142` ships package schema JSON, root `spec/` mirrors, export helper wiring, and
  deterministic export tests for all three starter schema ids.

### Edge 7: Advisory Reconstruction Could Reappear Too Early

- Risk:
  the family could start talking as if ledger, slice, theme, O/E/D/U, or workspace
  artifacts were already part of the released starter.
- Response:
  keep all advisory reconstruction and workspace seams deferred to later family paths.
- Closeout Evidence:
  the shipped `V54-A` package exports only source artifact, text-shape signals, and
  preclassification; no ledger, slice, theme, O/E/D/U, or workspace contracts were
  released in `v142`.

### Edge 8: Starter Parser Coverage Could Overclaim Corpus Adequacy

- Risk:
  deterministic starter-domain replay could be misread as evidence that the broader
  heuristic parser and grouping layer are already adequate for real corpus ingestion.
- Response:
  treat `V54-A` as a bounded source-authority and export substrate only, and move
  parser/grouping hardening into `V54-B`.
- Closeout Evidence:
  the shipped slice stays narrow, the planning branch now selects `V54-B` next, and
  no broad corpus-ingestion claim is made in the released closeout evidence.

## Current Judgment

- `V54-A` was the right first slice because the family needed:
  - one explicit source-authority choice
  - one repo-native schema/export posture
  - one deterministic source-grounded text-shape / preclassification substrate
  - one bounded input domain before any advisory reconstruction widening
- the shipped result remained properly bounded:
  - one repo-owned package
  - three released source contracts
  - one normalized-text authority root
  - one explicit-role-header `conversation_history` starter domain
  - one exact optional bracketed timestamp prefix form
  - one whole-source fail-closed posture
  - one deterministic text-shape / preclassification overlay
  - projection-only source metadata outside identity law
  - no ledger
  - no slice
  - no theme
  - no O/E/D/U
  - no workspace
  - no API/UI/runtime widening
  - no broader corpus-ingestion claim
- `V54-A` is now closed on `arc/v54-r3` in the branch-local sense:
  - `adeu_history_source_artifact@1`
  - `adeu_history_text_shape_signals@1`
  - `adeu_history_preclassification@1`
- the next meaningful family work remains sequenced:
  - `V54-B` for released ledger / slice / theme substrate plus parser/grouping
    hardening
  - `V54-C` for advisory O/E/D/U packet release only
  - `V54-D` for bounded workspace synthesis only
