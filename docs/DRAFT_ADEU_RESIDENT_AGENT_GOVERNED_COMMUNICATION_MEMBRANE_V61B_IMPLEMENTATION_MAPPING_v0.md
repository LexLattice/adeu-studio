# Draft ADEU Resident-Agent Governed Communication Membrane V61B Implementation Mapping v0

Status: support note for the `V61-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the second
`V61` slice should take one already shipped `V61-A` governed communication lineage
over one exact resident seam and make bridge-office posture plus rewitness /
message-promotion explicit, replayable, and fail-closed without reopening `V60`
continuation law, connector transport law, or remote/operator law.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v44.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_V61_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_V61A_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V61-A` ingress / descriptor / interpretation / egress packet law
- shipped `V60-A`, `V60-B`, and `V60-C` continuation / refresh / advisory posture
- shipped `V58-A`, `V58-B`, and `V58-C` live session and reintegration origin
  discipline
- shipped `V59-A`, `V59-B`, and `V59-C` continuity posture over the selected exact
  downstream exemplar
- the rule that transcript and event stream remain observability surfaces, not native
  witness
- the rule that communication access is not bridge office
- the rule that `charter_amendment_candidate` remains communication posture only and
  does not mutate charter/residual/continuation state

## Re-Author With Repo Alignment

`V61-B` should add exactly:

- `agentic_de_bridge_office_binding_record@1`
- `agentic_de_message_rewitness_gate_record@1`

`V61-B` should consume:

- one shipped `agentic_de_communication_ingress_packet@1`
- one shipped `agentic_de_surface_authority_descriptor@1`
- one shipped `agentic_de_ingress_interpretation_record@1`
- one shipped `agentic_de_communication_egress_packet@1`
- one latest shipped `V60` continuation basis only over the exact same selected
  downstream exemplar
- one explicit `agentic_de_lane_drift_record@1`
- committed closeout evidence from shipped `V61-A` as drift guard only

Those prior artifacts should outrank narrative interpretation for drift checking, but
they should not become ambient bridge authority or witness by mere existence.

The selected seam in this slice should remain exactly:

- live session surface:
  - URM copilot send path only
- runtime method:
  - `copilot.user_message`
- downstream action class:
  - `local_write`
- downstream write kind:
  - `create_new`
- declared continuity root:
  - `artifacts/agentic_de/v59/workspace_continuity/`
- exact downstream target centered on:
  - `runtime/reference_patch_candidate.diff`

## Bridge Office And Rewitness Law

The second communication slice should make these laws explicit:

- office binding is downstream of one already shipped `V61-A` communication lineage
- office binding must remain typed and replayable:
  - same selected bridge facts
  - same latest communication lineage
  - same selected `V60` continuation basis
  - same frozen policy
  - same office posture
- office binding remains explicit:
  - UI send access is not office binding
  - prior resident emission capability is not office binding
  - connector presence is not office binding
  - missing or inconsistent bridge facts fail closed:
    - `resident_bridge_escalate_for_review`
    - or `resident_bridge_withheld_by_policy`
- rewitness / message-promotion gate must remain typed and replayable:
  - same selected communication lineage
  - same selected office binding
  - same frozen policy
  - same rewitness outcome
- rewitness remains fail-closed:
  - raw communication is not native witness by default
  - raw transcript is not witness by default
  - generic chat memory is not witness law
  - ambiguity blocks promotion rather than being summarized away
- positive rewitness in `V61-B` remains bounded:
  - explicit witness-candidate posture only
  - positive rewitness requires explicit witness basis ref or certificate ref
  - missing positive rewitness basis fails closed
  - not native witness by itself
  - not reintegration closure by itself
  - not act authority
  - not repo-write authority
  - not charter mutation
  - not residual mutation
  - not loop-state mutation
  - not continuation-decision mutation
- office-bound outbound posture remains bounded:
  - same exact resident seam only
  - same exact shipped communication lineage only
  - no connector transport law here
  - no remote/operator law here
  - no product/UI authority rollout here

## Required Axes

`agentic_de_bridge_office_binding_record@1` should at minimum externalize:

- communication_ingress_ref
- surface_authority_descriptor_ref
- ingress_interpretation_ref
- communication_egress_ref
- task_charter_ref
- latest_continuation_basis_ref
- latest_continuation_basis_selection_summary
- resident_session_ref
- source_principal_class
- speaker_class
- surface_instance_or_session_identity
- selected_bridge_office_posture
- bridge_reason_codes
- frozen_policy_anchor_ref
- bridge_binding_basis_summary
- field_origin_tags
- field_dependence_tags
- root_origin_ids

At minimum the slice should distinguish bridge-office postures such as:

- `resident_bridge_bound`
- `resident_bridge_not_bound`
- `resident_bridge_withheld_by_policy`
- `resident_bridge_escalate_for_review`

`agentic_de_message_rewitness_gate_record@1` should at minimum externalize:

- communication_ingress_ref
- ingress_interpretation_ref
- communication_egress_ref
- bridge_office_binding_ref
- task_charter_ref
- latest_continuation_basis_ref
- rewitness_outcome
- rewitness_reason_codes
- frozen_policy_anchor_ref
- rewitness_basis_summary
- witness_basis_ref_or_none
- certificate_ref_or_none
- field_origin_tags
- field_dependence_tags
- root_origin_ids
- root_origin_dedup_summary

At minimum the slice should distinguish rewitness outcomes such as:

- `remain_communication_only`
- `witness_candidate_promoted`
- `withheld_by_policy`
- `blocked_ambiguous_lineage`
- `escalate_for_review`

Only `witness_candidate_promoted` may mark positive rewitness in `V61-B`.

If `witness_candidate_promoted` is selected, the positive result must remain bounded
to explicit witness-candidate posture only and may not become native witness,
reintegration closure, or act authority by default. It must also carry an explicit
witness basis ref or certificate ref, and missing positive basis must fail closed.

## Defer To Later Slice Or Family

- connector-specific transport trust or admission
- remote-operator UX law
- richer thread arbitration or multi-party office selection
- repo-bound writable-surface widening
- replay / resume widening
- execute widening
- dispatch widening
- advisory communication hardening and migration

## Do Not Import

- communication access as ambient bridge office
- raw transcript as native witness
- generic chat memory as rewitness law
- connector transport trust in `V61-B`
- remote operator or phone UX law in `V61-B`
- repo-write authority in `V61-B`
- act authority from office binding or rewitness alone
