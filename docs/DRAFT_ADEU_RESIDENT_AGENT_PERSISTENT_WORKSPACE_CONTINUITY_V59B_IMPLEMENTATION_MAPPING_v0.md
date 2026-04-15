# Draft ADEU Resident-Agent Persistent Workspace Continuity V59B Implementation Mapping v0

Status: support note for the `V59-B` implementation pass after `V59-A` closed on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a later `V59-B`
slice should integrate continuity-safe restoration over the same exact continuity-bound
lineage rather than silently reusing fresh-sandbox restoration semantics.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v42.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_PERSISTENT_WORKSPACE_CONTINUITY_V59_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_PERSISTENT_WORKSPACE_CONTINUITY_V59A_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V57-B` restoration law as the bounded restore baseline
- shipped `V58-B` explicit live restoration handoff / reintegration posture
- the shipped `V59-A` continuity region / admission / occupancy / reintegration
  surfaces
- the rule that prior workspace state remains context at most, never sufficient
  authority

## Re-Author With Repo Alignment

`V59-B` should add bounded continuity-safe restoration only.

Candidate new surfaces:

- `agentic_de_workspace_continuity_restoration_handoff_record@1`
- `agentic_de_workspace_continuity_restoration_reintegration_report@1`

`V59-B` should keep explicit:

- continuity-safe restoration is a new live act, not standing continuity authority
- shipped `V57-B` / `V58-B` restoration semantics are not automatically
  continuity-safe
- continuity-safe restoration remains lineage-bound to the same prior observation /
  ticket / checkpoint chain
- continuity-safe restoration requires one explicit prior governed-state baseline inside
  the declared continuity region
- continuity-safe restoration remains same-session and same-turn only in the starter
  slice
- restoration-time capability / approval posture must be re-snapshotted and compared
  against the admitted continuation posture
- restoration-time continuation verdict must remain typed, witness-bearing, and
  replayable:
  - same selected evidence chain
  - same frozen policy
  - same restoration-time continuation verdict
- missing or mismatched restoration-time resnapshot fails closed
- `action_ticket_ref`, prior reintegration refs, and prior occupancy refs remain
  historical lineage inputs only until bounded compensating-scope derivation and
  current-turn restoration witness basis independently pass
- continuity-safe restoration remains explicit state, not hidden cleanup
- prior governed-state baseline match should be first-class:
  - explicit baseline-match verdict
  - explicit restoration-time target or region state summary
- replay means bounded recomputation / re-evaluation of that exact continuity-safe
  restoration event, not arbitrary prior live-action re-execution
- positive continuity-safe restoration reintegration requires declared current-turn
  witness basis or equivalent certificate ref
- the replay-law proof surface should live inside the continuity restoration
  reintegration report rather than a separate artifact
- handoff / reintegration fields remain origin-tagged and dependence-tagged
- exact continuity root, target, and `create_new` compensating-restore exemplar remain
  frozen

## Defer To Later Slice

- append-only continuity restoration
- overwrite or destructive continuity restoration
- broader repo cleanup semantics
- standing resume or replay authority
- continuity hardening / migration decisions

## Do Not Import

- hidden compensators
- hidden cleanup success criteria
- semantic widening from one continuity-safe restore exemplar to restoration-family law
- any claim that prior continuity success makes future restoration ambiently admissible
