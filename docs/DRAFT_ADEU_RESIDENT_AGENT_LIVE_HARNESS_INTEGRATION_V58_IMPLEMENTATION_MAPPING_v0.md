# Draft ADEU Resident-Agent Live Harness Integration V58 Implementation Mapping v0

Status: support-layer implementation mapping for `V58`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the `V58` family into a
repo-native implementation shape so one real live resident turn can be governed by the
shipped `V56` / `V57` artifact stack rather than by ambient harness capability alone.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v41.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_V56_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_V57_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- the shipped `V56-A`, `V56-B`, and `V56-C` packet / proposal / checkpoint / ticket /
  conformance / harvest surfaces
- the shipped `V57-A`, `V57-B`, and `V57-C` observation / restoration / hardening
  surfaces
- the rule that `agentic_de_*` naming remains the lineage carrier while `V58` is the
  live harness-integration family role
- the rule that hidden cognition is not the governance surface
- the rule that transcript and event stream are observability surfaces, not native
  witness

## Re-Author With Repo Alignment

- primary family package:
  - `packages/adeu_agentic_de`
- live harness package:
  - `packages/urm_runtime`
- likely API/backend surfaces:
  - `apps/api/src/adeu_api/`
  - `apps/api/scripts/`
- tests:
  - `packages/adeu_agentic_de/tests/`
  - `packages/urm_runtime/tests/`
  - `apps/api/tests/`
- likely starter artifact output root:
  - `artifacts/agentic_de/v58/`

The family should remain backend-first in `V58-A`:

- no new product/UI authority surface
- no dispatch widening
- no execute widening
- no repo-authority write-mode reuse

## Path Ladder Mapping

- `V58-A`
  - instantiate one live-turn admission record
  - instantiate one explicit ticket-to-effect handoff record
  - instantiate one reintegration report
  - bind one real URM copilot turn to the shipped `V56-B -> V57-A` `local_write` /
    `create_new` exemplar
  - keep outer harness capability necessary at most, never sufficient
  - keep admission typed:
    - not just present / absent
    - explicit verdict plus reason posture
  - keep positive reintegration witness-bearing:
    - explicit witness basis or certificate ref
    - not status-only closure
  - keep handoff / reintegration fields origin-tagged and dependence-tagged
  - keep repeated observability or prior-artifact lineage root-deduplicated so echo
    cannot look like independent current-turn support
  - keep restoration not selected in the same starter turn
- `V58-B`
  - add one explicit restoration-state harness integration path over the same exact
    lineage using shipped `V57-B`
  - keep restoration as explicit state, not hidden cleanup
  - keep replay bounded to recomputation / re-evaluation of that same restore path
- `V58-C`
  - add one advisory harness drift / hardening surface over the same exact bound path
  - keep outputs advisory-only
  - keep any later widening or migration decision separate from live behavior by
    default

## Pre-Lane Drift Check Rule

Because all lane bundles are drafted before first implementation, each later lane should
start with one short drift check against the previous lane's actual landing.

That drift check should emit one bounded handoff artifact:

- `agentic_de_lane_drift_record@1`

Each controlling assumption should be classified at least as:

- `holds`
- `amended`
- `superseded`
- `not_selected_anymore`

## Interface Ordering Rule

- `V55` remains the constitutional coherence checker over family surfaces
- `V56` remains the resident proposal / checkpoint / ticket family
- `V57` remains the bounded observed / restored local-effect evidence family
- `V58` owns only live harness admission / handoff / reintegration over that already
  selected path
- `V48` remains the owner of delegated worker execution after lawful dispatch

## Do Not Import

- outer `writes_allowed` or approval posture as ticket equivalent
- transcript or `urm_events.ndjson` as current-turn native witness
- prior fixtures or closeout evidence as current-turn entitlement
- boolean-only admission that hides rejected / stale / withheld / unknown differences
- positive reintegration with no declared witness basis or certificate ref
- recirculated transcript, event-stream, or prior-artifact echoes counted as new support
- hidden bridge state between ticket issuance and observed effect
- auto-restoration or auto-retry in the starter live turn
- semantic widening from one create-new exemplar to class-level `local_write`
- any assumption that later `V58` lanes are authorized merely because they are drafted
