# Draft ADEU Resident-Agent Local-Effect Hardening V57 Implementation Mapping v0

Status: support-layer implementation mapping for `V57`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the `V57` family into a
repo-native implementation shape so bounded actual local-effect evidence can land
without silently widening the released `V56` runtime-governance family.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v40.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_V56_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- the shipped `V56-A`, `V56-B`, and `V56-C` packet / contract / proposal /
  checkpoint / ticket / conformance / harvest surfaces
- the rule that `agentic_de_*` naming remains the lineage carrier while `V57` is the
  local-effect hardening family role
- the shipped `V56-B` interpretation of:
  - `local_reversible_execute`
  - `local_write`
- the rule that hidden cognition is not the governance surface
- one full lane ladder drafted before first implementation:
  - `V57-A`
  - `V57-B`
  - `V57-C`

## Re-Author With Repo Alignment

- primary family package:
  - `packages/adeu_agentic_de`
- package source home:
  - `packages/adeu_agentic_de/src/adeu_agentic_de/`
- tests:
  - `packages/adeu_agentic_de/tests/`
- one thin script seam under existing repo operations:
  - `apps/api/scripts/`
- likely starter module split:
  - `local_effect.py`
  - `local_effect_conformance.py`
- likely starter artifact output root:
  - `artifacts/agentic_de/v57/`
- designated local-effect sandbox root:
  - `artifacts/agentic_de/v57/local_effect/`

The family should remain package-first in `V57-A`:

- no product API/UI widening;
- no multi-agent topology;
- no CI gating posture.
- no destructive or overwrite `local_write` semantics in the first actual-effect
  subset while restoration remains out of scope.

## Path Ladder Mapping

- `V57-A`
  - instantiate the first actual local-effect observation path
  - instantiate one designated local-effect sandbox root
  - instantiate one first safe `local_write` subset only:
    - `create_new`
    - `append_only`
  - instantiate one local-effect observation record
  - instantiate one local-effect conformance report
  - keep the path bounded to `local_write` only
- `V57-B`
  - add one restoration / compensating-restore record
  - add one bounded replay/restoration path over the same frozen `local_write`
    semantics
- `V57-C`
  - add one hardening register
  - decide whether the observed/restored local-write path deserves stronger local
    hardening later
  - do not assume such hardening is selected in advance

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

Only material drift should force a rewrite of the drafted next-lane note. Minor drift
should be recorded as confirmation or narrow amendment.

## Interface Ordering Rule

- `V55` remains the constitutional coherence checker over family surfaces;
- `V56` remains the resident proposal/checkpoint/ticket family;
- `V57` remains the actual bounded local-effect observation/restoration/hardening
  family over one already selected `V56` live path;
- `V48` remains the owner of delegated worker execution after lawful dispatch.

## Do Not Import

- support-doc self-promotion into live effect authority
- silent widening from sandbox-local effect to general repo write authority
- destructive, overwrite, rename, delete, or metadata-mutating writes in the first
  slice
- automatic hardening from one observed effect
- semantic repartition of `local_write`
- any assumption that later `V57` lanes are authorized merely because they are drafted
