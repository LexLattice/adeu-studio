# Draft ADEU Resident-Agent Live Harness Integration V58B Implementation Mapping v0

Status: support note for the `V58-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a later `V58-B`
slice should integrate restoration as an explicit harness state over the same exact
starter lineage rather than as hidden cleanup.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v41.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58A_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V57-B` restoration law
- the `V58-A` live-turn admission / handoff / reintegration surfaces
- the exact `local_write/create_new` exemplar and designated sandbox root
- the rule that outer harness capability remains necessary at most, never sufficient
- the rule that transcript and event stream remain observability surfaces, not native
  current-turn witness

## Re-Author With Repo Alignment

`V58-B` should add bounded restore-state integration only.

Candidate new surfaces:

- `agentic_de_live_restoration_handoff_record@1`
- `agentic_de_live_restoration_reintegration_report@1`

`V58-B` should keep explicit:

- restoration is a new live act, not ambient continuing authority
- restoration remains lineage-bound to the same prior observation / ticket /
  checkpoint chain
- restoration remains same-session and same-turn only in this slice
- restoration-time capability / approval posture must be re-snapshotted and compared
  against the admitted continuation posture
- missing or mismatched restoration-time resnapshot fails closed
- `action_ticket_ref` and prior reintegration refs are historical lineage inputs only
  until bounded compensating-scope derivation and current-turn restoration witness
  basis independently pass
- the live restoration handoff should carry at least:
  - restoration-time session capability snapshot
  - restoration-time approval posture snapshot
  - restoration-time continuation verdict
  - bounded compensating-scope derivation summary
- restoration remains explicit harness state, not hidden cleanup
- replay means bounded recomputation / re-evaluation of that exact restoration event,
  not arbitrary prior live-action re-execution
- replay-law proof should live inside the live restoration reintegration report rather
  than imply a separate replay-authority artifact in this slice
- positive restoration reintegration requires declared current-turn restoration witness
  basis or equivalent certificate ref
- handoff / reintegration fields remain origin-tagged and dependence-tagged
- echoed observability or prior-artifact lineage remains root-deduplicated so it
  cannot look like independent current-turn restoration support
- exact sandbox root, target, and `create_new` compensating-restore exemplar remain
  frozen

## Defer To Later Slice

- restoration-family widening
- append-only restoration integration
- broader repo cleanup semantics
- harness hardening / migration decisions

## Do Not Import

- auto-restore
- hidden compensators
- hidden cleanup success criteria
- semantic widening from one restore exemplar to restoration-family law
