# Draft ADEU Resident-Agent Interaction Governance V56B Implementation Mapping v0

Status: support note for the `V56-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the second slice
should harden the resident-agent loop from dry-run governance into one bounded live gate
without widening into broad runtime control.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v39.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_V56_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_V56A_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- the shipped `V56-A` packet / contract / proposal / diagnostics surfaces
- the same shaping-input set unless explicitly amended by drift record
- the non-laundering and advisory-until-gated posture

## Re-Author With Repo Alignment

`V56-B` should add exactly:

- `agentic_de_runtime_state@1`
- `agentic_de_action_ticket@1`

and one bounded live use path over the shipped checkpoint for selected action classes
only:

- `write`
- `execute`
- `dispatch`

The gate should:

- consume the shipped `V56-A` packet / contract / proposal surfaces unchanged by
  default;
- consume the shipped `V56-A` checkpoint surface unchanged by default;
- require checkpoint `accepted` status before issuing an action ticket;
- preserve unresolved and rejected states explicitly;
- remain local and bounded rather than becoming a repo-wide execution authority.

Likely starter script seam:

- `apps/api/scripts/run_agentic_de_interaction_v56b.py`

## `V56-B` Control Boundary

`V56-B` should govern:

- selected live action boundary crossing;
- ticket issuance;
- checkpoint and consequence logging.

Before `V56-B` lock, the family should freeze one exact starter action-class taxonomy
for:

- pure read / inspect
- effect-bearing or capability-sensitive inspect
- local reversible execute
- stronger execute
- local write
- delegated or external dispatch

`V56-B` should not yet govern:

- all reads and inspections;
- all runtime memory or planning state;
- multi-agent topologies;
- product-user-facing surfaces by default.

## Defer To Later Slice

- harvest and calibration
- profile/variant manifests
- broader runtime rollout
- stronger governance posture changes

## Do Not Import

- checker-global gating
- multi-surface rollout by default
- CI or branch protection logic
