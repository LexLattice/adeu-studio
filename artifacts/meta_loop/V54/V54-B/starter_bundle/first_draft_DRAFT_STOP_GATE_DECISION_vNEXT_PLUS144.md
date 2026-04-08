# Draft Stop-Gate Decision vNext+144

Status: proposed gate for `V54-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS144.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the released `V54-A` source-authority and preclassification substrate remains
  inherited unchanged:
  - normalized source text after line-ending normalization only
  - explicit full role-header `conversation_history` only
  - source identity rooted only in `input_kind` plus `source_text_hash`
- four new repo-owned contracts export and mirror deterministically:
  - `adeu_history_ledger_entry@1`
  - `adeu_history_ledger@1`
  - `adeu_history_slice@1`
  - `adeu_history_theme_anchor@1`
- each ledger entry is provably downstream of exactly one released preclassification
  with no same-speaker entry collapse;
- slice grouping is deterministic, chronology-local, and frozen to maximal contiguous
  same-role runs over released `order_index`;
- theme anchors remain descriptive groupings only:
  - deterministic `theme_key`
  - no ranking
  - no lane scoring
  - no O/E/D/U advice
- tests cover at least:
  - clean alternating-role reference replay
  - consecutive same-speaker grouping
  - quoted or fenced multi-line stability
  - empty or degenerate fail-closed posture
  - reject posture for shorthand or other out-of-domain source widening.

## Do Not Accept If

- the implementation reopens raw-byte authority, dual-authority posture, or projection
  metadata identity law from `V54-A`;
- shorthand `U:` / `A:` / `S:` source acceptance appears without an explicit later lock;
- adjacent same-speaker turns are silently merged into one ledger entry;
- quoted or pasted text inside one entry is allowed to mint a new role or ledger entry;
- theme anchors drift into advisory winner language, role-fit language, or O/E/D/U
  lane semantics;
- zero-entry ledgers, zero-slice outputs, or zero-theme-anchor outputs compile as
  apparent success;
- the slice starts exporting evidence refs, O/E/D/U packets, workspace artifacts, or
  broader runtime/API/corpus surfaces.

## Local Gate

- run `make arc-start-check ARC=144`
- full `make check` is intentionally not part of this docs-only starter step.
