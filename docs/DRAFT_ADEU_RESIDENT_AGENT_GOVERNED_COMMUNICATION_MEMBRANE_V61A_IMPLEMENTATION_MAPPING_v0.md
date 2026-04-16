# Draft ADEU Resident-Agent Governed Communication Membrane V61A Implementation Mapping v0

Status: support note for the `V61-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the first `V61`
slice should retrofit one already-real resident communication seam into a typed
governed communication membrane over the shipped `V60` continuation kernel without
letting transcript, UI send plumbing, or bridge posture become ambient authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v44.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_V61_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V60-A`, `V60-B`, and `V60-C` continuation / refresh / advisory surfaces
- shipped `V58-A`, `V58-B`, and `V58-C` live session and reintegration origin
  discipline
- shipped `V59-A`, `V59-B`, and `V59-C` continuity posture over the selected exact
  downstream exemplar
- the rule that transcript and event stream are observability surfaces, not native
  witness
- the rule that communication access is not permission
- the rule that `emit_governed_communication` in `V60` is posture only, not packet
  law

## Re-Author With Repo Alignment

`V61-A` should add exactly:

- `agentic_de_communication_ingress_packet@1`
- `agentic_de_surface_authority_descriptor@1`
- `agentic_de_ingress_interpretation_record@1`
- `agentic_de_communication_egress_packet@1`

`V61-A` should consume:

- one explicit `agentic_de_lane_drift_record@1`
- one existing URM copilot session send seam only:
  - API route:
    - `apps/api/src/adeu_api/urm_routes.py:/copilot/send`
  - runtime request method:
    - `copilot.user_message`
- one latest shipped `V60` continuation basis only over the exact selected downstream
  exemplar:
  - `agentic_de_task_charter_packet@1`
  - latest applicable `agentic_de_task_residual_packet@1` or
    `agentic_de_task_residual_refresh_packet@1`
  - `agentic_de_loop_state_ledger@1`
  - latest applicable `agentic_de_continuation_decision_record@1` or
    `agentic_de_continuation_refresh_decision_record@1`
- shipped `V60-C` advisory hardening posture as shaping input only
- committed closeout evidence from shipped `V60` lanes as drift guard only

Web copilot and GPT-5.4 desktop workbench should be treated as consumer surfaces of
that same starter backend seam, not as separate starter retrofit seams in `V61-A`.

## Starter Communication Law

The starter communication turn should make these laws explicit:

- communication ingress must remain typed and replayable:
  - same selected ingress payload
  - same selected surface facts
  - same frozen policy
  - same ingress packet
- principal / speaker typing must remain explicit:
  - source principal class
  - speaker class
  - surface instance or session identity
- surface authority classification must remain typed and replayable:
  - same selected surface facts
  - same frozen policy
  - same descriptor
- the surface-authority descriptor records surface affordance / bounded authority
  posture only:
  - not message interpretation by itself
  - not charter or continuation mutation by itself
- ingress interpretation must remain typed and replayable:
  - same ingress packet
  - same descriptor
  - same selected `V60` continuation basis
  - same frozen policy
  - same interpretation posture
- `charter-amendment candidate` remains posture only in this slice:
  - not charter mutation
  - not residual mutation
  - not continuation mutation
  - not starter seed-ingress reopening
- communication egress must remain typed and replayable:
  - same selected interpretation
  - same selected `V60` continuation basis
  - same frozen policy
  - same egress packet
- egress remains communication posture only:
  - not act authority
  - not ticket authority
  - not repo-write authority
  - not native witness by default
- resident runtime emission in `V61-A` is not yet explicit bridge-office behavior
- rewitness / message-promotion remains unselected in this slice
- evidence from this selected seam remains non-generalizing by default:
  - not connector-family law
  - not remote-operator law
  - not bridge-office law
  - not rewitness / message-promotion law
  - not independent law for other communication surfaces beyond the same backend seam

The selected starter path in this slice should remain exactly:

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

## Required Axes

`agentic_de_communication_ingress_packet@1` should at minimum externalize:

- communication ingress id
- resident session ref
- source principal class
- speaker class
- surface class
- surface instance or session identity
- selected API route or equivalent surface ref
- selected runtime message method
- ingress payload summary
- seed / continuation basis summary
- ingress basis summary
- field origin tags
- field dependence tags
- root-origin identifiers needed for dedup / non-independence checks

`agentic_de_surface_authority_descriptor@1` should at minimum externalize:

- descriptor id
- communication ingress ref
- surface class
- surface instance or session identity
- surface affordance classes
- bounded authority posture summary
- frozen policy anchor ref
- descriptor basis summary
- field origin tags
- field dependence tags

`agentic_de_ingress_interpretation_record@1` should at minimum externalize:

- communication ingress ref
- surface authority descriptor ref
- task charter ref
- loop-state ledger ref
- latest continuation basis ref
- latest continuation-basis selection summary
- frozen policy anchor ref
- interpretation posture
- interpretation reason codes
- interpretation basis summary
- field origin tags
- field dependence tags
- root-origin identifiers

At minimum the starter slice should distinguish interpretation postures such as:

- `clarification_response`
- `authority_response`
- `status_request`
- `charter_amendment_candidate`
- `advisory_only_message`

`agentic_de_communication_egress_packet@1` should at minimum externalize:

- communication egress id
- ingress interpretation ref
- task charter ref
- latest continuation basis ref
- selected egress posture
- selected egress surface ref
- egress payload summary
- frozen policy anchor ref
- egress basis summary
- field origin tags
- field dependence tags
- root-origin identifiers

At minimum the starter slice should distinguish outbound communication postures:

- `status_update`
- `clarification_question`
- `authority_request`
- `escalation_notice`
- `completion_report`
- `advisory_only_message`

## Defer To Later Slice

- explicit resident bridge-office binding
- explicit rewitness / message-promotion gate
- connector-specific transport trust or admission
- remote-operator UX law
- repo-bound writable-surface widening
- replay / resume widening
- execute widening
- dispatch widening

## Do Not Import

- raw transcript semantics as ingress law
- generic chat memory as communication authority
- UI send access as bridge office
- `charter_amendment_candidate` as implicit charter mutation
- communication packets as native witness by default
- connector traffic as already-governed communication law
