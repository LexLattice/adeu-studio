# Draft Stop-Gate Decision vNext+146

Status: proposed gate for `V54-C`.

Authority layer: planning scaffold for a later closeout-required decision artifact.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS146.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Guardrail

- This note records the pre-start acceptance gate for `vNext+146` only.
- It does not redefine the implementation contract in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS146.md`.
- If `V54-C` later closes successfully, this scaffold is superseded by post-closeout
  evidence and final decision values.

## Accept When

- the released `V54-A` source-authority and `V54-B` ledger / slice / theme substrate
  remains inherited unchanged:
  - normalized source text after line-ending normalization only
  - explicit full role-header `conversation_history` only
  - one preclassification to one ledger-entry law only
  - maximal contiguous same-role slice grouping only
  - deterministic descriptive theme-anchor law only
- three new repo-owned contracts export and mirror deterministically:
  - `adeu_history_evidence_ref@1`
  - `adeu_history_odeu_lane_reconstruction@1`
  - `adeu_history_odeu_reconstruction_packet@1`
- evidence refs remain grounded to released ledger entries and released entry text:
  - concrete `entry_id`
  - inherited `role`
  - excerpt text already present inside the referenced released `entry_text`
- each packet remains downstream of exactly one released slice and one released theme
  anchor, with exactly one lawful `O/E/D/U` lane set in canonical order;
- `present` or `weakly_present` lanes require:
  - non-empty `reconstruction_text`
  - one or more lawful `evidence_refs`
- `underdetermined` or `not_salient` lanes remain explicit rather than silently
  repaired:
  - no `evidence_refs`
  - `explicitation_status = underdetermined`
  - `dominant_role_posture = none`
- `interpretation_authority_posture` remains exactly:
  - `advisory_overlay_only`
- package-local schema exports, root `spec/` mirrors, and the schema export helper
  stay in sync
- targeted tests cover at least:
  - locally explicit lane replay
  - dialogically explicitated mixed-role replay
  - contextually reconstructed weak or underdetermined replay
  - evidence-ref grounding rejection
  - missing or duplicate lane rejection
  - no workspace widening inside the `V54-C` slice

## Do Not Accept If

- the implementation reopens raw-byte authority, shorthand alias acceptance, or any
  other released `V54-A` source-domain law;
- the implementation reopens same-speaker entry collapse, alternate slice grouping, or
  alternate theme-key derivation law from `V54-B`;
- evidence refs point at missing entry ids, use mismatched roles, or present synthetic
  paraphrase as direct evidence;
- packets silently fill absent lanes into fully explicit four-lane symmetry;
- packets drift into lane scoring, winner language, warrant language, or workspace
  synthesis;
- the slice exports workspace question, workspace theme frame, workspace snapshot, or
  semantic-bundle contracts;
- the slice widens into API, UI, runtime, retrieval, or broader corpus-ingestion
  surfaces.

## Local Gate

- attempted docs-only gate:
  - `make arc-start-check ARC=146`
- current worktree result:
  - `pass`
- full `make check` is intentionally not part of this docs-only starter step.
