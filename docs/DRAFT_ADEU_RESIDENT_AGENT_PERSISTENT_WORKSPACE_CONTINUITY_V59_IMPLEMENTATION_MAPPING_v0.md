# Draft ADEU Resident-Agent Persistent Workspace Continuity V59 Implementation Mapping v0

Status: support-layer implementation mapping for `V59`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the `V59` family into a
repo-native implementation shape so bounded persistent workspace continuity can land
over the already shipped `V56` / `V57` / `V58` governed live path without turning
carried-forward state into ambient authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v42.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_PERSISTENT_WORKSPACE_CONTINUITY_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_V57_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- the shipped `V56-A`, `V56-B`, and `V56-C` packet / proposal / checkpoint / ticket /
  conformance / harvest surfaces
- the shipped `V57-A`, `V57-B`, and `V57-C` observation / restoration / hardening
  surfaces
- the shipped `V58-A`, `V58-B`, and `V58-C` live admission / handoff /
  reintegration / advisory surfaces
- the shipped `V59-A` continuity region / admission / occupancy / reintegration
  surfaces
- the rule that `agentic_de_*` naming remains the lineage carrier while `V59` is the
  persistent workspace-continuity family role
- the rule that hidden cognition is not the governance surface
- the rule that prior workspace state is context at most, never standing authority
- the rule that transcript and event stream are observability surfaces, not native
  current-turn witness

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
- likely family module split:
  - `workspace_continuity.py`
  - `workspace_continuity_reintegration.py`
- likely family artifact output root:
  - `artifacts/agentic_de/v59/`
- declared continuity root for the starter lane:
  - `artifacts/agentic_de/v59/workspace_continuity/`

The family should remain backend-first in `V59-A`:

- no product API/UI authority widening
- no dispatch widening
- no execute widening
- no repo-source continuity in the first slice

## Path Ladder Mapping

- `V59-A`
  - instantiate one declared continuity-region surface
  - instantiate one continuity admission record
  - instantiate one occupancy report
  - instantiate one continuity reintegration report
  - bind the exact shipped `V58` live path to one declared persistent continuity region
  - keep current-turn live admission required
  - keep continuity admission typed and replayable:
    - same selected continuity evidence chain plus same frozen policy
    - same continuity admission verdict
    - any verdict other than `admitted` remains non-entitling and fail-closed in the
      starter slice
  - keep carried-forward state context-only unless freshly re-witnessed in the current
    turn
  - keep `create_new` semantically exact through typed occupancy law
  - keep occupancy verdict witness-bearing and replayable:
    - declared region snapshot identity
    - target-level presence or absence
    - prior governed artifact refs when matched
    - explicit out-of-band detection grounds when asserted
  - keep starter admissibility narrow:
    - `unoccupied` target only
    - occupied, drifted, out-of-band, or unknown target states fail closed
  - keep non-target occupants inside the declared continuity root contextual only:
    - region-scope context or out-of-scope drift
    - not silent target entitlement or ambient admissibility
  - keep prior ticket, prior reintegration, or prior successful turn non-equivalent to
    ambient admissibility
  - keep positive continuity reintegration witness-bearing:
    - explicit witness basis or certificate ref
  - keep restoration not selected in the starter continuity slice
  - keep replay / resume widening not selected in the starter continuity slice
- `V59-B`
  - add one explicit continuity-safe restoration path over the same exact continuity
    lineage
  - reuse the shipped `V59-A` continuity region / admission / occupancy /
    reintegration surfaces by default
  - instantiate explicit restoration handoff / reintegration under continuity
  - keep restoration a new live act, not standing continuity authority
  - keep same-session and same-turn continuation only in the starter restore slice
  - keep restoration-time capability / approval posture re-snapshotted against the
    admitted continuity continuation posture
  - keep restoration-time continuation verdict typed, witness-bearing, and replayable:
    - same selected evidence chain
    - same frozen policy
    - same continuation verdict
  - keep mismatch or missing restoration-time resnapshot fail-closed
  - keep `action_ticket_ref`, prior continuity reintegration refs, and prior occupancy
    refs historical lineage inputs only until bounded compensating-scope derivation
    and current-turn restoration witness basis independently pass
  - keep continuity-safe restoration dependent on explicit prior governed-state
    baseline comparison
  - keep explicit prior governed-state baseline-match verdict
  - keep explicit restoration-time target or region state summary
  - keep explicit bounded compensating-scope match or fail closed
  - keep replay bounded to recomputation / re-evaluation of that same continuity-safe
    restoration event only
  - keep append-only, overwrite, destructive, or repo-source restoration not selected
- `V59-C`
  - add one advisory continuity hardening / drift surface over the same exact
    continuity-bound path
  - reuse the shipped `V59-A` continuity lineage by default
  - reuse the shipped `V59-B` continuity-safe restoration lineage by default if that
    slice lands
  - keep outputs advisory-only and path-level only
  - keep continuity evidence non-generalizing by default:
    - not class-level `local_write` law
    - not replay-family law
    - not continuity-family law
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
- `V58` remains the live harness admission / handoff / reintegration family
- `V59` owns only declared persistent continuity-region identity, occupancy, and
  continuity reintegration over that already integrated path, plus later selected
  continuity-safe restoration over the same exact path
- `V48` remains the owner of delegated worker execution after lawful dispatch

## Do Not Import

- stopping runtime reset as implicit continuity authority
- carried-forward state as current-turn native witness by default
- prior ticket or prior reintegration as standing authority
- occupied target state silently normalized into `create_new` admissibility
- shipped `V57-B` / `V58-B` fresh-sandbox restoration semantics treated as
  automatically continuity-safe
- restoration or replay widening by continuity implication alone
- out-of-band drift treated as if it were governed carried-forward lineage
- any assumption that later `V59` lanes are authorized merely because they are drafted
