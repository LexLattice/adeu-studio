# Draft ADEU Remote Operator UX And Phone Control Plane V63 Implementation Mapping v0

Status: support-layer implementation mapping for `V63` after `V62` closed on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the `V63` family into
a repo-native implementation shape so one bounded remote operator surface can
inspect shipped loop and communication lineage and emit one tiny bounded response
set without letting phone/control reachability become ambient authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v46.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V59_v0.md`
- `docs/ARCHITECTURE_ADEU_REMOTE_OPERATOR_UX_AND_PHONE_CONTROL_PLANE_FAMILY_v0.md`
- `docs/support/v60+ plan gptpro.md`
- `docs/OPERATOR_REFERENCE_v0.md`

## Carry Forward Nearly As-Is

- the shipped `V60-A`, `V60-B`, and `V60-C` continuation / refresh / advisory
  surfaces
- the shipped `V61-A`, `V61-B`, and `V61-C` communication / bridge / advisory
  surfaces
- the shipped `V58-A`, `V58-B`, and `V58-C` origin and reintegration discipline
- the shipped `V59-A`, `V59-B`, and `V59-C` continuity posture
- the shipped `V62-A`, `V62-B`, and `V62-C` connector posture as separate sibling
  family law only
- the rule that communication law remains owned by `V61`
- the rule that connector law remains owned by `V62`
- the rule that remote visibility or acknowledgement is not witness by default
- the rule that hidden cognition is not the governance surface

## Re-Author With Repo Alignment

- primary family package:
  - `packages/adeu_agentic_de`
- runtime/session package:
  - `packages/urm_runtime`
- likely API/backend surfaces:
  - `apps/api/src/adeu_api/`
  - `apps/api/scripts/`
- likely remote UI surfaces:
  - `apps/web/`
- current remote-capable practical references to consume first:
  - URM approval/session state
  - current workbench doctrine
  - existing copilot/event surfaces
- tests:
  - `packages/adeu_agentic_de/tests/`
  - `packages/urm_runtime/tests/`
  - `apps/api/tests/`
  - `apps/web/` tests where view-model shaping needs frontend coverage

The family should remain backend-first plus one bounded view projection in `V63-A`:

- no connector admission or connector trust mutation
- no broader remote-admin family claim yet
- no repo-bound writable-surface widening
- no execute widening
- no dispatch widening

## Path Ladder Mapping

- `V63-A`
  - instantiate:
    - `agentic_de_remote_operator_session_record@1`
    - `agentic_de_remote_operator_view_packet@1`
    - `agentic_de_remote_operator_response_record@1`
  - require explicit starter typing for:
    - remote-operator principal class
    - remote session / surface identity
    - remote session admission verdict family
    - consumed loop-state basis
    - consumed governed communication basis
    - approval/session basis where relevant
    - selected response kind where relevant
    - frozen-policy anchor
  - bind those outputs to one bounded remote operator surface only
  - keep principal selection explicit:
    - `remote_operator` selected in `V63-A`
    - `external_assistant` not selected in `V63-A`
    - `human_via_connector` not selected in `V63-A`
  - prefer retrofitting existing status/approval/session seams before adding new
    product or shell semantics
  - keep remote session and view typed and replayable:
    - same admitted remote session basis
    - same consumed `V60` / `V61` basis
    - same frozen policy
    - same session/view outputs
  - keep bounded response basis repo-native and fail-closed:
    - exact admitted remote session ref
    - exact selected response kind
    - explicit control basis ref or equivalent matched to that response kind
    - explicit approval/session state ref where relevant
    - explicit continuation or communication posture summary where relevant
    - missing or inconsistent session/response basis fails closed
  - keep remote transport non-authorizing:
    - not witness
    - not bridge office
    - not connector law
    - not repo-write authority
    - not execute authority
    - not dispatch authority
  - keep `V63-A` narrower than the later control bridge:
    - read-mostly status / ask / evidence view only
    - bounded acknowledgement / approval / continue / pause / escalate only
    - acknowledgement remains notification/session posture only and may not mutate
      continuation, communication, or authority state by itself
    - no structured answers or clarifications
    - no inspect-rich controls
    - no richer typed command/control bridge yet
  - keep the starter bounded to one remote operator surface:
    - no broader remote-admin family
    - no connector mutation
    - no repo-write authority
    - no execute authority
    - no dispatch widening
  - keep seam evidence non-generalizing by default:
    - not connector law
    - not broader remote-admin law
    - not repo-authority law
    - not execution-authority law
    - not all devices or all operator surfaces by default
- `V63-B`
  - treat shipped `V63-A` as closed starter basis:
    - consume the shipped admitted remote session record
    - consume the shipped remote operator view packet
    - do not reopen `V63-A` principal selection or session admission law
  - add:
    - `agentic_de_remote_operator_control_bridge_packet@1`
    - one explicit governed remote command/control bridge over the same admitted
      remote operator session so richer typed intervention remains separate from
      starter responses
  - let richer remote intervention land there:
    - structured answers or clarifications
    - inspect-rich controls
    - broader typed command/control bridge
  - keep command/control semantics typed and fail-closed:
    - same admitted remote session record
    - same consumed shipped `V60` / `V61` basis
    - same frozen policy
    - same control bridge output
  - keep connector and repo trust still separated
- `V63-C`
  - add one advisory remote-operator hardening surface over the same admitted
    remote operator lineage
  - candidate surface:
    - `agentic_de_remote_operator_hardening_register@1`
  - keep outputs advisory-only and non-entitling
  - keep evidence basis distinct from recommendation
  - committed lane artifacts outrank narrative interpretation when the advisory
    register is derived
  - keep the advisory result extensional and replayable:
    - same admitted remote session lineage
    - same view and response or control lineage
    - same consumed `V60` / `V61` basis
    - same frozen policy
    - same recommendation
  - keep remote exemplar evidence non-generalizing by default:
    - not connector law
    - not broader remote-admin law
    - not repo-authority conclusions
    - not execution-authority conclusions

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
- `V62` remains the owner of connector admission and external assistant bridge
  posture over that already governed communication stack
- `V63` owns only remote operator session/view/response posture over that already
  governed communication stack
- `V64` and `V65` remain later execution-widening branches

## Likely Repo-Native Surfaces

Likely implementation surfaces for `V63-A`:

- `packages/adeu_agentic_de/src/adeu_agentic_de/models.py`
  - new remote operator session / view / response models
- `packages/adeu_agentic_de/src/adeu_agentic_de/checker.py`
  - loader / renderer / validator / runner support for `V63-A`
- `packages/adeu_agentic_de/src/adeu_agentic_de/export_schema.py`
  - authoritative and mirrored schema export
- `packages/adeu_agentic_de/src/adeu_agentic_de/__init__.py`
  - public export wiring
- `packages/urm_runtime/src/urm_runtime/`
  - likely session/control and approval-state consumption points only if the slice
    needs runtime-backed admission facts
- `apps/api/scripts/`
  - one thin starter script for `V63-A`
- `apps/web/`
  - one bounded read-mostly remote dashboard projection only if the slice needs
    explicit UI projection in the starter pass
- `packages/adeu_agentic_de/tests/`
  - package and schema tests
- `apps/api/tests/`
  - thin CLI and backend seam tests

The starter slice should prefer retrofitting existing status/approval/session seams
over adding new free-form control surfaces.
