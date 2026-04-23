# Draft Stop-Gate Decision vNext+185

Status: proposed starter gate for `V67-A`.

Authority layer: planning / starter gate.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS185.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- all seven `V67-A` starter schemas are defined with repo-native `schema` fields
  and export cleanly to both authoritative and mirror paths;
- all seven models and schema constants export from `adeu_core_ir.__init__`;
- the starter ergonomic class vocabulary is frozen exactly to the selected
  artifact-inspector family class set;
- the starter candidate profile table is frozen exactly to the selected finite
  candidate ids;
- reference fixtures validate locally and bind to the released UX-governance
  basis with exact source refs and hashes;
- reject fixtures fail with stable reason categories for:
  - unknown class drift
  - unknown projection refs
  - same-context glossary drift
  - user preference lowering a hard floor
  - inadmissible physical / visual chain claims
  - scalar exported preference scores;
- visibility-contract validation covers all required evidence / trust / status /
  commit-bearing parts of the released projection;
- same-context reveal terms validate against the released
  `v36a_same_context_reachability_glossary@1`;
- platform presets cannot become hard law unless explicitly repo-adopted;
- `V67-A` result fixtures remain schema / validator fixtures only and do not
  claim computed ergonomic feasibility;
- no bounded adjudication engine, runtime measurement artifact, or runtime bridge
  artifact lands in this slice.

## Do Not Accept If

- any `V67-A` artifact still relies on draft-only `schema_id` instead of the
  repo-native `schema` field;
- the starter registry leaves ergonomic class ids or candidate ids implicit;
- candidate rows can mint new semantic lanes, regions, action clusters, or
  same-context vocabulary;
- source-artifact refs / hashes are omitted, non-replayable, or non-deterministic
  in starter reference fixtures;
- diagnostics / conformance artifacts are silently promoted from optional
  downstream evidence into required `V67-A` basis;
- any result artifact exports scalar ergonomic scores or treats utility ranking
  as constitutional law;
- `V67-A` smuggles in bounded adjudication computation under the label of
  reference result fixtures;
- the slice widens into layout solving, screenshot-first authority, runtime
  personalization, or typed runtime bridge output.

## Local Gate

- run `git diff --check`
- run `make arc-start-check ARC=185`

Full Python lane may remain skipped here because this is a docs-only starter
bundle.
