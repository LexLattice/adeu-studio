# Draft ADEU Resident-Agent Interaction Governance V56A Implementation Mapping v0

Status: support note for the `V56-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the first
resident-agent interaction-governance slice should land as a bounded starter family
rather than a premature live-control system.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v39.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_V56_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- the existing packet / morph IR / interaction-contract slot structure already visible
  in `packages/adeu_core_ir/schema/ux_*`
- the authority-boundary law:
  - surface artifacts may express but may not mint authority
- the resident-agent law:
  - outputs remain advisory until a governed gate
- the non-laundering law:
  - unresolved or under-evidenced states do not silently collapse into action
- the practical six-lane discipline:
  - packet / settlement / proposal / diagnostics remain explicit

## Re-Author With Repo Alignment

`V56-A` should instantiate exactly:

- `agentic_de_domain_packet@1`
- `agentic_de_morph_ir@1`
- `agentic_de_interaction_contract@1`
- `agentic_de_action_proposal@1`
- `agentic_de_membrane_checkpoint@1`
- `agentic_de_morph_diagnostics@1`
- `agentic_de_conformance_report@1`

The starter package should:

- validate the packet and interaction contract fail-closed;
- compile one action proposal against them;
- keep `agentic_de_action_proposal@1` non-entitling in `V56-A`:
  - candidate action only
  - claimed basis only
  - dry-run checkpointability only
- emit one dry-run membrane checkpoint artifact over that proposal;
- emit diagnostics and one conformance-style typed delta report with:
  - `executed_or_observed_effect = no_live_effect`

Likely starter script seam:

- `apps/api/scripts/lint_agentic_de_interaction_v56a.py`

## Exact `V56-A` Shaping Set

The first shaping-input set should be closed to:

- `docs/support/ADEU_SCHEMA_META_GRAMMAR.md`
- `docs/support/AGENTIC_DE_TYPE_GRAMMAR.md`
- `docs/support/ODEU_MEMBRANE_ARCHITECTURE.md`
- `docs/support/ODEU AS A COUPLED SEMANTIC HYPERSPACE WITH LAWFUL MORPHISMS_v2.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`
- `packages/adeu_core_ir/schema/ux_domain_packet.v1.json`
- `packages/adeu_core_ir/schema/ux_morph_ir.v1.json`
- `packages/adeu_core_ir/schema/ux_interaction_contract.v1.json`

Later support artifacts require explicit admission-amendment and do not enter by
thematic similarity alone.

## `V56-A` Runtime Posture

`V56-A` is:

- dry-run only;
- diagnostics-first;
- no live write / execute / dispatch entitlement;
- no hidden-cognition governance claim.

It should be able to say:

- checkpoint status:
  - `accepted`
  - `residualized`
  - `blocked`
  - `escalated`
  - `rejected_by_form`
- checkpoint reason code:
  - `authority_missing`
  - `insufficient_evidence`
  - `proposal_malformed`
  - `out_of_scope`
  - `noncomparable`
  - `unresolved_dependency`
  - `not_evaluable_yet`

It should not be able to directly execute a gated effect yet.

## Defer To Later Slice

- runtime checkpoint persistence
- live action tickets
- actual tool interception
- harvest and calibration
- multi-profile or multi-variant governance

## Do Not Import

- direct write / execute / dispatch interception into `V56-A`
- speculative internal-state proxy metrics presented as authoritative governance input
- broad resident-agent runtime replacement
- product UI or API rollout
