# Draft ADEU Repo-Bound Writable-Surface Authority V64 Implementation Mapping v0

Status: support-layer implementation mapping for `V64` after `V63` closed on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the `V64` family into
a repo-native implementation shape so one bounded writable-surface authority family
can land over the already shipped continuity / continuation / communication stack
without turning persistence context, communication lineage, or remote control posture
into ambient repo authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v49.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V59_v0.md`
- `docs/ARCHITECTURE_ADEU_REPO_BOUND_WRITABLE_SURFACE_AUTHORITY_FAMILY_v0.md`
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
- the rule that continuity region is context/persistence law, not entitlement law
- the rule that communication law remains owned by `V61`
- the rule that remote operator law remains owned by `V63`
- the rule that hidden cognition is not the governance surface

## Re-Author With Repo Alignment

- primary family package:
  - `packages/adeu_agentic_de`
- runtime/session package:
  - `packages/urm_runtime`
- likely API/backend surfaces:
  - `apps/api/src/adeu_api/`
  - `apps/api/scripts/`
- tests:
  - `packages/adeu_agentic_de/tests/`
  - `packages/urm_runtime/tests/`
  - `apps/api/tests/`

The family should remain backend-first in `V64-A`:

- no remote-operator law mutation
- no connector-law mutation
- no broader repo-bound writable-surface widening beyond one selected surface
- no execute widening
- no dispatch widening
- no delegated worker export or reconciliation

## Path Ladder Mapping

- `V64-A`
  - instantiate:
    - `agentic_de_repo_writable_surface_descriptor@1`
    - `agentic_de_repo_write_lease_record@1`
    - `agentic_de_repo_write_surface_admission_record@1`
  - require explicit starter typing for:
    - selected subtree or file-set surface identity
    - canonical normalized path-membership basis
    - inclusion / exclusion basis
    - consumed continuity-region basis
    - consumed continuation basis
    - consumed communication basis where relevant
    - preserved narrow write-semantics basis
    - per-target occupancy / admissibility basis
    - frozen policy anchor
    - explicit lease verdict family
    - explicit admission verdict family
  - bind those outputs to one bounded writable surface only
  - keep writable-surface scope explicit:
    - one declared subtree or file-set only
    - no all-repo writable authority
    - no implicit descendant laundering outside the declared surface
  - keep writable-surface authority lease-shaped and replayable:
    - same selected surface basis
    - same consumed `V59` / `V60` / `V61` basis
    - same frozen policy
    - same descriptor / lease / admission outputs
  - keep authority-seam boundaries explicit:
    - continuity region is not writable entitlement
    - communication lineage is not writable entitlement
    - connector posture is not writable entitlement
    - remote control posture is not writable entitlement
    - writable-surface admission is not shell / execute / dispatch authority
    - writable-surface admission is not delegated worker authority
  - keep mutation semantics narrower than later `V64` work:
    - preserve current `local_write` / `create_new` subset only
    - no append / overwrite / rename / delete widening yet
  - keep per-target entitlement typed and fail-closed:
    - lease alone is not enough for every path in the declared surface
    - explicit occupancy/admissibility basis required
    - missing or inconsistent target basis fails closed
  - keep path membership exact and fail-closed:
    - canonical normalized membership only
    - symlink / alias / indirection surprises fail closed
    - explicit inclusion / exclusion basis required
- later `V64-B`
  - treat shipped `V64-A` surface descriptor and lease as closed starter basis
  - add writable-surface restoration / reintegration over that same selected
    writable surface
- later `V64-C`
  - add one advisory hardening surface over the same selected writable-surface
    lineage
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

- `V59` remains the owner of continuity-region identity and occupancy posture
- `V60` remains the owner of continuation / residual-intent identity
- `V61` remains the owner of governed communication packet and office law
- `V63` remains the owner of remote operator session / view / response / control
  posture
- `V64` owns only bounded repo-bound writable-surface authority over that already
  governed stack
- `V65` remains the owner of later delegated export / worker reconciliation

## Likely Repo-Native Surfaces

Likely implementation surfaces for `V64-A`:

- `packages/adeu_agentic_de/src/adeu_agentic_de/models.py`
  - new writable-surface descriptor / lease / admission models
- `packages/adeu_agentic_de/src/adeu_agentic_de/checker.py`
  - loader / renderer / validator / runner support for `V64-A`
- `packages/adeu_agentic_de/src/adeu_agentic_de/export_schema.py`
  - authoritative and mirrored schema export
- `packages/adeu_agentic_de/src/adeu_agentic_de/__init__.py`
  - public export wiring
- `packages/urm_runtime/src/urm_runtime/`
  - only if runtime-backed approval/session facts are needed as consumed basis
- `apps/api/scripts/`
  - one thin starter script for `V64-A`
- `packages/adeu_agentic_de/tests/`
  - package and schema tests
- `apps/api/tests/`
  - thin CLI and backend seam tests

The starter slice should prefer retrofitting existing continuity / continuation /
communication seams over inventing broad repo-admin or shell-control surfaces.
