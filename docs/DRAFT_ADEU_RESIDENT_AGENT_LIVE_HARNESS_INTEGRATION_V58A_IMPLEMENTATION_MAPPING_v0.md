# Draft ADEU Resident-Agent Live Harness Integration V58A Implementation Mapping v0

Status: support note for the `V58-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the first `V58`
slice should bind one real live URM copilot turn to the shipped `V56-B` ticket lineage
and the shipped `V57-A` observed local effect without widening authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v41.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_V57_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V56-B` action-class, runtime-state, and ticket semantics
- shipped `V57-A` observation and local-effect conformance semantics
- shipped designated local-effect sandbox semantics
- shipped fresh-sandbox reset semantics

## Re-Author With Repo Alignment

`V58-A` should add exactly:

- `agentic_de_live_turn_admission_record@1`
- `agentic_de_live_turn_handoff_record@1`
- `agentic_de_live_turn_reintegration_report@1`

`V58-A` should consume:

- one current URM copilot session path
- one explicit `agentic_de_lane_drift_record@1`
- shipped `V56-A` / `V56-B` packet / proposal / checkpoint / ticket surfaces
- shipped `V57-A` observation / local-effect conformance surfaces
- committed closeout evidence from shipped `V56` / `V57` lanes as drift guard only

Those prior committed artifacts should outrank narrative interpretation for drift
checking, but they should not count as current-turn witness.

## Starter Live-Turn Law

The starter turn should make these laws explicit:

- outer URM session mode and approval posture are operability preconditions at most
- inner entitlement remains the exact current-turn `V56-B` ticket lineage
- transcript and event stream remain observability surfaces only
- current-turn witness must come from current-turn admission + packet/proposal /
  checkpoint / ticket + observed pre/post state
- positive reintegration must name its witness basis or certificate ref
- no hidden bridge state may decide eligibility or closeout
- repeated transcript fragments, event-stream emissions, or repeated references to the
  same observed effect must not count as independent current-turn witness

The selected live path in this slice should remain exactly:

- live session path:
  - URM copilot session path
- action class:
  - `local_write`
- write kind:
  - `create_new`
- designated sandbox root:
  - `artifacts/agentic_de/v57/local_effect/`
- exact starter target centered on:
  - `runtime/reference_patch_candidate.diff`

`V58-A` should also keep:

- restoration not selected in the starter slice
- no auto-cleanup
- no second exemplar
- no `local_reversible_execute`
- no dispatch

## Required Axes

`agentic_de_live_turn_admission_record@1` should at minimum externalize:

- live session id
- current session capability snapshot
- current approval posture snapshot
- admission verdict
- admission reason codes
- repo root / cwd
- designated sandbox root
- selected live path identity

Admission verdicts should remain typed rather than boolean. At minimum the starter slice
should distinguish:

- admitted
- absent_not_owed
- rejected_inadmissible
- stale_or_expired
- withheld
- unknown
- partial

`agentic_de_live_turn_handoff_record@1` should at minimum externalize:

- live-turn admission ref
- domain packet ref
- action proposal ref
- checkpoint ref
- ticket ref
- exact target relative path
- exact selected effect scope
- source-origin tags for each authority-bearing field
- dependence tags when any field is derived rather than native current-turn support
- root-origin identifiers needed for dedup / non-independence checks

`agentic_de_live_turn_reintegration_report@1` should at minimum externalize:

- live-turn admission ref
- handoff ref
- observation ref
- local-effect conformance ref
- observed effect summary
- reintegration status
- reintegration reason codes
- reintegration witness basis summary
- reintegration certificate ref or equivalent witness ref when positive reintegration is
  asserted
- source-origin tags for `observed_effect_summary` and `six_lane_closeout_posture`
- dependence tags for any non-native or derived component
- root-origin dedup summary for repeated observability or prior-artifact inputs
- explicit six-lane closeout posture

Origin tags should keep at least these distinctions explicit:

- `current_turn_native`
- `current_turn_derived`
- `observability_only`
- `prior_artifact`
- `shaping_only`

## Defer To Later Slice

- explicit restoration-state harness integration
- persistent workspace continuity
- replay/drift hardening
- broader action-class coverage

## Do Not Import

- outer write-mode collapse into inner entitlement
- event-stream-as-witness
- prior-closeout-as-current-witness
- boolean-only admission semantics
- positive reintegration with no declared witness basis
- echo-amplified transcript or event-stream support
- hidden retry or cleanup behavior
- class widening from one create-new exemplar
