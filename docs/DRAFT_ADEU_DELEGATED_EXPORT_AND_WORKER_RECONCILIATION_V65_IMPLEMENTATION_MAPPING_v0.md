# Draft ADEU Delegated Export And Worker Reconciliation V65 Implementation Mapping v0

Status: support-layer implementation mapping for `V65` after `V64` closed on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the `V65` family into
a repo-native implementation shape so one bounded delegated export / worker
reconciliation family can land over the already shipped local writable-surface
stack and the already released `V48` worker substrate without turning local repo
authority, worker-carrier identity, or prior successful delegation into ambient
export, shell, execute, or all-repo authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v50.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V59_v0.md`
- `docs/ARCHITECTURE_ADEU_DELEGATED_EXPORT_AND_WORKER_RECONCILIATION_FAMILY_v0.md`
- `docs/support/v60+ plan gptpro.md`

## Carry Forward Nearly As-Is

- the shipped `V59-A`, `V59-B`, and `V59-C` continuity region / occupancy /
  restoration / hardening posture
- the shipped `V60-A`, `V60-B`, and `V60-C` continuation / refresh / advisory
  hardening posture
- the shipped `V61-A`, `V61-B`, and `V61-C` governed communication / bridge /
  advisory hardening posture
- the shipped `V62-A`, `V62-B`, and `V62-C` connector posture as separate sibling
  trust law only
- the shipped `V63-A`, `V63-B`, and `V63-C` remote operator posture as separate
  sibling transport/control law only
- the shipped `V64-A`, `V64-B`, and `V64-C` local writable-surface authority as
  the only local export basis
- the released `V48-A` through `V48-E` worker binding / compiled-boundary /
  envelope / conformance / topology posture as the only worker-law basis
- the rule that local writable-surface authority is local entitlement law, not
  delegated export law
- the rule that released worker carrier identity is worker-law carrier posture,
  not export entitlement law
- the rule that hidden cognition is not the governance surface

## Re-Author With Repo Alignment

- primary family package:
  - `packages/adeu_agentic_de`
- consumed worker substrate package:
  - `packages/adeu_agent_harness`
- runtime/session package:
  - `packages/urm_runtime`
- likely API/backend surfaces:
  - `apps/api/src/adeu_api/`
  - `apps/api/scripts/`
- tests:
  - `packages/adeu_agentic_de/tests/`
  - `packages/adeu_agent_harness/tests/`
  - `packages/urm_runtime/tests/`
  - `apps/api/tests/`

The family should remain backend-first in `V65-A`:

- no connector-law mutation
- no remote-operator-law mutation
- no fresh local writable-surface widening
- no fresh `V48` worker-law redefinition
- no broader dispatch semantics initiated by the starter
- no execute widening
- no dispatch widening
- no recursive or multi-worker orchestration

## Path Ladder Mapping

- `V65-A`
  - instantiate:
    - `agentic_de_delegated_worker_export_packet@1`
  - require explicit starter typing for:
    - shipped local writable-surface lineage identity
    - exported work summary
    - exported-work membership basis
    - exact local target or artifact carry-through where relevant
    - released worker carrier basis ref or equivalent
    - selected worker topology basis ref or equivalent
    - released worker carrier identity summary
    - selected worker topology lineage summary
    - consumed continuation basis
    - consumed communication basis where relevant
    - frozen policy anchor
    - explicit export verdict family
  - bind those outputs to one bounded export path only
  - keep export scope explicit:
    - one shipped local writable surface only
    - one released worker carrier lineage only
    - one selected worker topology lineage only
    - no all-repo delegated export
    - no worker-topology widening in the starter slice
    - no implicit fan-out or later worker-set expansion by implication
  - keep delegated export authority replayable:
    - same shipped `V64` basis
    - same released `V48` basis
    - same exported work summary
    - same exported-work membership basis
    - same consumed `V60` basis
    - same consumed `V61` basis where relevant
    - same frozen policy
    - same export output
  - keep authority-seam boundaries explicit:
    - local writable authority is not delegated export authority
    - released `V48` worker carrier identity is not delegated export authority
    - shipped `V64-C` advisory hardening evidence is shaping/drift-guard context only, not export entitlement
    - delegated export starter does not initiate broader dispatch semantics
    - delegated export starter does not redefine worker execution
    - delegated export starter is not reconciliation by itself
    - delegated export starter does not carry worker-result semantics yet
    - delegated export is not dispatch authority
    - delegated export is not shell / execute authority
    - delegated export is not connector or remote-operator law
  - keep export entitlement typed and fail-closed:
    - missing or inconsistent local basis fails closed
    - missing or inconsistent released worker basis fails closed
    - missing or inconsistent exported-work membership basis fails closed
    - ambiguous exported-work widening fails closed
    - out-of-scope local paths may not be laundered through worker carrier identity
    - shipped `V64` narrow mutation semantics must remain preserved in exported form
    - no backdoor append / overwrite / rename / delete widening
    - no richer worker-side action-family widening
- later `V65-B`
  - treat shipped `V65-A` export starter as closed bridge basis
  - add `agentic_de_delegated_worker_reconciliation_report@1` over that same exported lineage
- later `V65-C`
  - add `agentic_de_delegated_worker_hardening_register@1` over the same export / reconciliation lineage
  - keep outputs advisory-only and non-entitling

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

- `V48` remains the owner of delegated worker binding / compiled-boundary /
  envelope / conformance / topology law
- `V59` remains the owner of continuity-region identity and occupancy posture
- `V60` remains the owner of continuation / residual-intent identity
- `V61` remains the owner of governed communication packet and office law
- `V64` remains the owner of bounded local repo-bound writable-surface authority
- `V65` owns only bounded delegated export / worker reconciliation bridge law over
  that already governed local-and-worker stack

## Likely Repo-Native Surfaces

Likely implementation surfaces for `V65-A`:

- `packages/adeu_agentic_de/src/adeu_agentic_de/models.py`
  - new delegated export starter model
- `packages/adeu_agentic_de/src/adeu_agentic_de/checker.py`
  - loader / renderer / validator / runner support for `V65-A`
- `packages/adeu_agentic_de/src/adeu_agentic_de/export_schema.py`
  - authoritative and mirrored schema export
- `packages/adeu_agentic_de/src/adeu_agentic_de/__init__.py`
  - public export wiring
- `packages/adeu_agent_harness/src/adeu_agent_harness/`
  - consumed worker-law carrier reads only where released `V48` surfaces are
    needed as explicit basis
- `packages/urm_runtime/src/urm_runtime/`
  - only if runtime-backed approval/session or communication facts are needed as
    consumed basis
- `apps/api/scripts/`
  - one thin starter script for `V65-A`
- `packages/adeu_agentic_de/tests/`
  - package and schema tests
- `apps/api/tests/`
  - thin CLI and backend seam tests

The starter slice should prefer retrofitting the shipped `V64` local writable
surfaces and consuming the released `V48` worker substrate over inventing broad
dispatch, multi-worker control, or shell-control surfaces.
