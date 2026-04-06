# Draft Stop-Gate Decision vNext+142

Status: proposed gate for `V54-A`.

Authority layer: planning scaffold for a later closeout-required decision artifact.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS142.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Guardrail

- This note records the pre-start acceptance gate for `vNext+142` only.
- It does not redefine the implementation contract in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS142.md`.
- If `V54-A` later closes successfully, this scaffold is superseded by post-closeout
  evidence and final decision values.

## Accept When

- the starter source-authority contract exports and mirrors exactly these schema ids:
  - `adeu_history_source_artifact@1`
  - `adeu_history_text_shape_signals@1`
  - `adeu_history_preclassification@1`
  - `adeu_history_ledger_entry@1`
  - `adeu_history_ledger@1`
- the authoritative source posture remains exactly:
  - `normalized_source_text_authoritative`
- line-ending normalization is explicit, deterministic, and replayable:
  - `LF` and `CRLF` variants of the same starter source produce the same authoritative
    normalized `source_text`, `source_text_hash`, and `source_id`
- the starter input domain remains exactly:
  - `conversation_history` with explicit `User:` / `Assistant:` / `System:` headers
- source identity remains bound only to:
  - `input_kind`
  - `source_text_hash`
- `source_label`, `corpus_wave_posture`, and `source_notes` remain projection-only and
  do not mint alternate identity
- ledger entries and preclassification stay deterministic, source-grounded, and
  fail-closed outside the bounded starter domain
- `local_group_id` and `suggested_slice_boundary_before` remain preclassification hints
  only and do not become released slice/theme authority in `V54-A`
- package-local schema exports, root `spec/` mirrors, and the schema export helper stay
  in sync
- targeted tests cover canonical replay, normalization equivalence, and reject cases
  for unsupported domain or widened-surface attempts

## Do Not Accept If

- the slice claims raw-byte authority without byte-preserving contract fields and
  replay tests
- `abstract_like` or shorthand `U:` / `A:` / `S:` inputs are silently accepted as the
  same starter-domain release
- the implementation ships slice, theme, O/E/D/U, workspace, or end-to-end semantic
  bundle contracts in `V54-A`
- prototype heuristic grouping or reconstruction logic is treated as broad
  corpus-ingestion adequacy by default
- imported external bundle artifacts are treated as precedent-bearing live authority
  instead of support-only intake evidence

## Local Gate

- run `make arc-start-check ARC=142`
