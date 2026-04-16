# Draft ADEU Resident-Agent Connector Admission And External Assistant Bridge V62 Implementation Mapping v0

Status: support-layer implementation mapping for `V62` after `V61` closed on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the `V62` family into
a repo-native implementation shape so one external connector path can be admitted
into the shipped `V61` governed communication membrane without letting connector
transport or upstream assistant output become ambient authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v45.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V59_v0.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_FAMILY_v0.md`
- `docs/support/v60+ plan gptpro.md`
- `docs/formal/asir/ASIRKernelConnector.md`

## Carry Forward Nearly As-Is

- the shipped `V61-A`, `V61-B`, and `V61-C` communication / bridge / advisory
  surfaces
- the shipped `V60-A`, `V60-B`, and `V60-C` continuation outputs
- the shipped `V58-A`, `V58-B`, and `V58-C` origin and reintegration discipline
- the shipped `V59-A`, `V59-B`, and `V59-C` continuity posture
- the rule that transcript, event stream, and connector payload are not native
  witness by default
- the rule that communication law remains owned by `V61`
- the rule that remote operator UX stays in `V63`
- the rule that hidden cognition is not the governance surface

## Re-Author With Repo Alignment

- primary family package:
  - `packages/adeu_agentic_de`
- runtime / connector package:
  - `packages/urm_runtime`
- likely API/backend surfaces:
  - `apps/api/src/adeu_api/`
  - `apps/api/scripts/`
- current connector-capable runtime surfaces to retrofit first:
  - connector snapshot / exposure mapping in `packages/urm_runtime`
  - existing resident session and send/message bridge seams
- tests:
  - `packages/adeu_agentic_de/tests/`
  - `packages/urm_runtime/tests/`
  - `apps/api/tests/`

The family should remain backend-first in `V62-A`:

- no remote operator UX law yet
- no broader connector fleet yet
- no human-via-connector selection yet
- no repo-bound writable-surface widening
- no execute widening
- no dispatch widening

## Path Ladder Mapping

- `V62-A`
  - instantiate:
    - `agentic_de_connector_admission_record@1`
    - `agentic_de_external_assistant_ingress_bridge_packet@1`
  - require explicit starter typing for:
    - connector class
    - connector identity or instance
    - connector-carried principal class
    - snapshot / exposure / route basis
    - freshness basis
    - surface/session identity where relevant
  - bind those outputs to one already-real connector path only
  - keep principal selection explicit:
    - principal-typed connector path
    - external-assistant principal selected in `V62-A`
    - human-via-connector not selected in `V62-A`
  - prefer retrofitting existing connector snapshot / exposure seams before adding
    new product routes or UI semantics
  - keep connector admission typed and replayable:
    - same connector facts
    - same snapshot / exposure facts
    - same freshness basis
    - same frozen policy
    - same admission verdict
  - keep admission basis repo-native and fail-closed:
    - exact connector snapshot ref or equivalent
    - exact exposure mapping ref or equivalent
    - explicit freshness basis summary
    - missing or stale admission basis fails closed
  - keep raw connector traffic non-authorizing:
    - not raw transcript truth
    - not generic chat memory
    - not native witness by default
    - not charter compilation
    - not continuation mutation
    - not act authority
  - keep the bridge dependent on shipped `V61` packet law:
    - same admitted connector
    - same consumed `V61` communication basis
    - same frozen policy
    - same bridge packet
    - connector bridge does not interpret message meaning independently of `V61`
    - where office or rewitness posture matters, the bridge consumes shipped
      `V61-B` office / rewitness surfaces explicitly
  - keep `V62-A` narrower than the later bridge follow-on:
    - admitted connector path plus ingress bridge only
    - no full bidirectional bridge yet
    - no richer provenance carry-through claims yet
    - no human-via-connector semantics yet
  - keep the starter bounded to one admitted connector path:
    - no broader connector fleet
    - no remote-operator UX
    - no repo-write authority
    - no execute authority
    - no dispatch widening
  - keep seam evidence non-generalizing by default:
    - not human-via-connector law
    - not remote-operator law
    - not broader connector-fleet trust law
    - not repo-authority law
    - not execution-authority law
- `V62-B`
  - treat shipped `V62-A` as closed starter basis:
    - consume the shipped admitted connector record
    - consume the shipped external assistant ingress bridge packet
    - do not reopen `V62-A` principal selection or admission law
  - add:
    - `agentic_de_external_assistant_egress_bridge_packet@1`
    - one explicit egress-side external assistant bridge follow-on over the same
      admitted connector path so the shipped `V62-A` ingress plus the new `V62-B`
      egress surface define the bounded bidirectional bridge
  - keep provenance carry-through explicit and replayable:
    - same admitted connector record
    - same shipped ingress bridge basis
    - same consumed `V61` communication lineage
    - same selected connector principal
    - same frozen policy
    - same bridge basis
    - missing or inconsistent connector basis fails closed
  - keep bridge basis more explicit than `V62-A`:
    - explicit ingress and egress basis carry-through
    - explicit snapshot / exposure provenance carry-through
    - explicit office / rewitness consumption where relevant
    - direct consumed rewitness basis summary when positive
    - explicit continuation-basis selection summary
    - optional office / rewitness refs set to `none` mean not selected and not
      consumed in that packet
    - missing optional office / rewitness refs may not be inferred from prior
      capability or connector availability
  - keep external assistant output bounded:
    - not native witness by itself
    - not task-law ingress by itself
    - not bridge-office by itself
    - not repo-write authority
    - not human-via-connector semantics by itself
  - keep connector and remote-operator trust still separated
- `V62-C`
  - add one advisory connector hardening / provenance-drift surface over the same
    admitted connector lineage
  - candidate surface:
    - `agentic_de_connector_bridge_hardening_register@1`
  - keep outputs advisory-only and non-entitling
  - keep evidence basis distinct from recommendation
  - keep the advisory result extensional and replayable:
    - same admitted connector lineage
    - same consumed `V61` communication basis
    - same explicit provenance / exposure basis
    - same frozen policy
    - same recommendation
  - keep connector exemplar evidence non-generalizing by default:
    - not remote-operator law
    - not broader connector fleet law
    - not repo-authority conclusions
    - not execution-authority conclusions
  - keep later connector migration scope unspecified until a later lock selects it

## Pre-Lane Drift Check Rule

Because all lane bundles are drafted before first implementation, each later lane
should start with one short drift check against the previous lane's actual landing.

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
- `V58` remains the live harness admission / origin / reintegration family
- `V59` remains the persistent continuity family over the selected path
- `V60` remains the continuation / residual-intent kernel
- `V61` remains the owner of governed communication packet, interpretation,
  surface typing, bridge-office binding, and rewitness law
- `V62` owns only connector admission and external assistant bridge posture over that
  already governed communication stack
- `V63` should later own remote operator UX over `V61`
- `V64` and `V65` remain later execution-widening branches

## Likely Repo-Native Surfaces

Likely implementation surfaces for `V62-A`:

- `packages/adeu_agentic_de/src/adeu_agentic_de/models.py`
  - new connector admission and external assistant bridge models
- `packages/adeu_agentic_de/src/adeu_agentic_de/checker.py`
  - loader / renderer / validator / runner support for `V62-A`
- `packages/adeu_agentic_de/src/adeu_agentic_de/export_schema.py`
  - authoritative and mirrored schema export
- `packages/adeu_agentic_de/src/adeu_agentic_de/__init__.py`
  - public export wiring
- `packages/urm_runtime/src/urm_runtime/`
  - likely connector identity / exposure consumption points only if the slice needs
    runtime-backed admission facts
- `apps/api/scripts/`
  - one thin starter script for `V62-A`
- `packages/adeu_agentic_de/tests/`
  - package and schema tests
- `apps/api/tests/`
  - thin CLI and backend seam tests

The starter slice should prefer retrofitting existing connector exposure seams over
adding new product surfaces.
