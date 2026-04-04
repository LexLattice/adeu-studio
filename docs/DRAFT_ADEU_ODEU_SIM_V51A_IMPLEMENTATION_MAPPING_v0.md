# Draft ADEU ODEU Sim V51A Implementation Mapping v0

Status: support note for the `V51-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the imported GPT
Pro `odeu-sandbox-app` prototype should be used as shaping evidence while the live
repo-owned `V51-A` implementation is re-authored in `packages/adeu_odeu_sim`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS124.md`
- `examples/external_prototypes/odeu-sandbox-app/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the starter one-region / one-commons / one-institution / one-public-archive domain
- the starter scenarios:
  - `healthy_baseline`
  - `weak_d`
- the explicit O/E/D/U lane split in kernel state
- the starter archetype vocabulary:
  - `cooperator`
  - `opportunist`
  - `auditor`
  - `official`
  - `ai_dependent`
- the starter action vocabulary and lane-delta posture
- the heuristic regime-label vocabulary used by the prototype classifier
- the seeded deterministic replay posture demonstrated by the prototype engine tests
- the named lane-crossing concept set:
  - `O -> E` trace
  - `E -> D` legitimacy
  - `D -> O` allocation
  - `U -> D` pressure
- the key nested kernel objects as real first-class models, including:
  - lane-state models
  - `Agent`
  - `ResourcePool`
  - `Institution`
  - `Norm`
  - `Observation`
  - `EvidenceRecord`
  - `Claim`
  - `PublicReport`
  - `AuditResult`
  - `SanctionEvent`
- the scenario share-allocation fields carried directly in `ScenarioConfig`

## Re-Author With Repo Alignment

- create the repo-owned package scaffold under:
  - `packages/adeu_odeu_sim/src/adeu_odeu_sim/`
  - `packages/adeu_odeu_sim/tests/`
- re-author models with repo-native fail-closed validation rather than copying the
  prototype module tree
- introduce explicit repo-owned schema/model ids for the starter kernel contracts
- keep the key nested kernel objects as first-class validated models rather than
  collapsing them into one broad `WorldState` payload
- re-author the prototype’s loose string `event_log` into a typed event-record
  contract for repo-native replay and diagnostics
- make the lane-crossing contracts live in explicit typed contract surfaces rather than
  only in README prose
- freeze deterministic replay in repo-native fixtures and tests over exact starter
  scenarios, seed, and replay horizon
- freeze deterministic agent iteration order and action tie-break behavior explicitly
- freeze exact archetype-share validation in `ScenarioConfig`
- keep regime outputs explicitly heuristic and diagnostic only in live code
- add repo-native deterministic fixture snapshots and targeted tests

## Defer To Later Slice

- `api.py` and any FastAPI route work to `V51-B`
- `static/` and any browser/UI surface to `V51-C`
- persistent storage to later family work after the kernel contract is accepted
- broader scenario families, including:
  - `weak_e`
  - `weak_e_weak_d`
  - `coercive_truth_poor_order`
  - `ai_mediated_epistemics`
- any FastAPI or browser/UI consumer code to later family slices
- broader product routing or non-persistent API/UI orchestration until later slices

## Do Not Import

- the prototype source tree wholesale into live package or app paths
- the prototype `api.py` into `V51-A`
- the prototype `static/` UI assets into `V51-A`
- the standalone run guidance as if it were repo-native build methodology
- the prototype tests wholesale as released repo fixtures without re-authoring them
- the prototype string-only `event_log` posture as the live replay carrier
