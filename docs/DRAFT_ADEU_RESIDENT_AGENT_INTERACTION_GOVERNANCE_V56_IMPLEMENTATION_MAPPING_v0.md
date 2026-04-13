# Draft ADEU Resident-Agent Interaction Governance V56 Implementation Mapping v0

Status: support-layer implementation mapping for `V56`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the `V56` family into a
repo-native implementation shape so the resident-agent interaction-governance ladder can
land without silently promoting support doctrine into live runtime authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v39.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_FAMILY_v0.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`

## Carry Forward Nearly As-Is

- the repo-native packet / morph IR / interaction-contract ladder already visible in
  `packages/adeu_core_ir/schema/ux_*`
- the rule that `agentic_de_*` naming is the lineage carrier while `V56` is the
  runtime-governance family role particularized through that lineage
- the authority-boundary law from `ADEU_SCHEMA_META_GRAMMAR`
- the membrane-gate doctrine from `ODEU_MEMBRANE_ARCHITECTURE`
- the no-stronger-than-witness / anti-laundering posture from the lawful-morphisms
  note
- the rule that hidden cognition should not be treated as the primary governance
  surface
- one full lane ladder drafted before first implementation:
  - `V56-A`
  - `V56-B`
  - `V56-C`

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
  - `domain_packet.py`
  - `morph_ir.py`
  - `interaction_contract.py`
  - `action_proposal.py`
  - `membrane.py`
  - `diagnostics.py`
  - `conformance.py`
- likely starter artifact output root:
  - `artifacts/agentic_de/v56/`

The family should remain package-first in `V56-A`:

- no product API/UI widening;
- no live multi-agent topology;
- no CI gating posture.

## Path Ladder Mapping

- `V56-A`
  - instantiate the family starter package
  - instantiate packet, morph IR, interaction contract, action proposal,
    dry-run membrane checkpoint, diagnostics, and conformance surfaces
  - instantiate one dry-run membrane gate only
- `V56-B`
  - add runtime state and action ticket surfaces plus one bounded live use path over
    the shipped checkpoint for selected write / execute / dispatch classes
  - keep the gate local and bounded
- `V56-C`
  - add harvest and governance-calibration surfaces
  - decide whether any local enforcement should strengthen later
  - do not assume such strengthening is selected in advance

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

## Defer To Later Slice

- direct hidden-cognition governance
- product-surface rollout
- multi-agent orchestration
- repo-wide gating
- generalized theorem-prover semantics

## Interface Ordering Rule

- `V55` remains the constitutional coherence checker over family surfaces;
- `V56` remains the resident runtime-governance family;
- `V48` remains the owner of delegated worker execution after lawful dispatch;
- `V51` may shape runtime semantics but does not own authority here.

## Do Not Import

- prompt-only runtime governance as if it were sufficient
- free transition from reasoning to effect with no typed proposal
- support-doc self-promotion into live runtime authority
- automatic equivalence between worker-harness authority and resident-agent authority
- any assumption that later `V56` lanes are authorized merely because they are drafted
