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

## Re-Author With Repo Alignment

`V58-B` should add bounded restore-state integration only.

Candidate new surfaces:

- `agentic_de_live_restoration_handoff_record@1`
- `agentic_de_live_restoration_reintegration_report@1`

`V58-B` should keep explicit:

- restoration is a new live act, not ambient continuing authority
- restoration remains lineage-bound to the same prior observation / ticket /
  checkpoint chain
- restoration remains explicit harness state, not hidden cleanup
- replay means bounded recomputation / re-evaluation of that exact restoration event,
  not arbitrary prior live-action re-execution

## Defer To Later Slice

- restoration-family widening
- append-only restoration integration
- broader repo cleanup semantics
- harness hardening / migration decisions

## Do Not Import

- auto-restore
- hidden compensators
- semantic widening from one restore exemplar to restoration-family law
