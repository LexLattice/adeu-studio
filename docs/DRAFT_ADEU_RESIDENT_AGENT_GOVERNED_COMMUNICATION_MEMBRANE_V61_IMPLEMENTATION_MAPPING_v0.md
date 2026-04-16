# Draft ADEU Resident-Agent Governed Communication Membrane V61 Implementation Mapping v0

Status: support-layer implementation mapping for `V61` after `V60` closed on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the `V61` family into a
repo-native implementation shape so governed communication packets, interpretation,
surface typing, and later bridge-office law can land over the already shipped `V60`
continuation kernel without letting transcript, UI plumbing, or transport surfaces
become ambient authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v44.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V59_v0.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_FAMILY_v0.md`
- `docs/support/v60+ plan gptpro.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`
- `docs/DRAFT_WCPGC_CORE_AND_STRICT_V0_v0.md`

## Carry Forward Nearly As-Is

- the shipped `V60-A`, `V60-B`, and `V60-C` starter / refresh / advisory continuation
  surfaces
- the shipped `V58-A`, `V58-B`, and `V58-C` origin and reintegration discipline
- the shipped `V59-A`, `V59-B`, and `V59-C` continuity and restoration posture
- the rule that `agentic_de_*` naming remains the lineage carrier while `V61` is the
  governed communication family role
- the rule that hidden cognition is not the governance surface
- the rule that transcript and event stream are observability surfaces, not native
  witness or act authority
- the rule that communication access is not permission
- the rule that connector or phone transport must consume `V61`, not preempt it

## Re-Author With Repo Alignment

- primary family package:
  - `packages/adeu_agentic_de`
- live harness/runtime package:
  - `packages/urm_runtime`
- likely API/backend surfaces:
  - `apps/api/src/adeu_api/`
  - `apps/api/scripts/`
- current communication-capable UI/runtime surfaces to retrofit first:
  - `apps/web/src/app/copilot/`
  - `apps/gpt54-codex-workbench/`
  - existing URM session send/message seams and API routes
- tests:
  - `packages/adeu_agentic_de/tests/`
  - `packages/urm_runtime/tests/`
  - `apps/api/tests/`

The family should remain backend-first in `V61-A`:

- no connector-specific transport law yet
- no remote operator UX law yet
- no repo-bound writable-surface widening
- no dispatch widening
- no execute widening
- no bridge-office binding yet

## Path Ladder Mapping

- `V61-A`
  - instantiate:
    - `agentic_de_communication_ingress_packet@1`
    - `agentic_de_surface_authority_descriptor@1`
    - `agentic_de_ingress_interpretation_record@1`
    - `agentic_de_communication_egress_packet@1`
  - require explicit starter packet typing for:
    - source principal class
    - speaker class
    - surface instance or session identity
  - bind those outputs to already-real repo communication surfaces only:
    - web copilot
    - GPT-5.4 desktop workbench
    - resident session send/message seams
  - prefer retrofitting existing send / receive seams before adding new routes or UI
    semantics
  - keep starter message ingress explicit and non-authorizing:
    - not raw transcript truth
    - not generic chat memory
    - not native witness by default
    - not act authority
    - not charter mutation by itself
  - keep surface classification typed and replayable:
    - same selected surface facts
    - same frozen policy
    - same descriptor
    - same selected surface facts plus same frozen policy yield the same descriptor
    - descriptor records surface affordance / authority posture only
    - descriptor does not interpret message meaning by itself
  - keep ingress interpretation typed and replayable:
    - same ingress packet
    - same selected surface facts
    - same frozen policy
    - same interpretation posture
    - explicit frozen-policy anchor remains required on interpretation outputs
  - keep interpreted `charter-amendment candidate` posture non-mutating in `V61-A`:
    - posture tag only
    - not charter amendment law
    - not residual mutation
    - not continuation mutation
    - not starter seed-ingress reopening
  - keep communication output typed and replayable:
    - same interpretation
    - same selected `V60` continuation basis
    - same frozen policy
    - same egress posture
  - keep the starter bounded to outbound posture only:
    - status update
    - clarification question
    - authority request
    - escalation notice
    - completion report
    - advisory-only message
  - keep bridge-office binding deferred:
    - runtime may emit governed communication egress over the resident surface
    - this is not yet explicit bridge-office behavior
    - office binding is not yet selected here
  - keep rewitness / message promotion deferred:
    - no native witness promotion here
    - no message-to-witness gate here
  - keep seam evidence non-generalizing by default:
    - not connector-family law
    - not remote-operator law
    - not bridge-office law
    - not rewitness / message-promotion law
    - not independent law for other communication surfaces beyond the same backend
      seam
  - keep connector transport, remote-operator UX, repo-bound writable authority,
    replay widening, execute widening, and dispatch widening not selected in this
    slice
- `V61-B`
  - add:
    - `agentic_de_bridge_office_binding_record@1`
    - `agentic_de_message_rewitness_gate_record@1`
  - keep office posture explicit and replayable:
    - same selected bridge facts
    - same latest communication lineage
    - same selected `V60` continuation basis
    - same frozen policy
    - same office posture
    - missing or inconsistent bridge facts fail closed
  - keep message promotion fail-closed and explicit:
    - raw communication is not native witness by default
    - rewitness remains required for any witness-candidate promotion
    - positive rewitness remains witness-candidate posture only in `V61-B`
    - positive rewitness requires explicit witness basis ref or certificate ref
    - missing positive rewitness basis fails closed
    - positive rewitness is not native witness, reintegration closure, or act
      authority by itself
    - positive rewitness does not mutate charter, residual, loop-state, or
      continuation outputs in `V61-B`
  - keep the same seam exact:
    - same resident `/urm/copilot/send` seam only
    - same `copilot.user_message` method only
    - same downstream continuity-bound exemplar only
  - keep connector and remote-operator transport still deferred to later families
- `V61-C`
  - add one advisory communication hardening surface over the same communication
    lineage
  - keep outputs advisory-only and non-entitling
  - keep evidence basis distinct from recommendation
  - keep communication exemplar evidence non-generalizing by default
    - not connector-family law
    - not remote-operator law
    - not execution-authority conclusions
  - keep any later office or transport widening separate from live behavior by
    default

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

## Interface Ordering Rule

- `V55` remains the constitutional coherence checker over family surfaces
- `V56` remains the resident proposal / checkpoint / ticket family
- `V58` remains the live harness admission / origin / reintegration family
- `V59` remains the persistent continuity family over the selected path
- `V60` remains the continuation / residual-intent kernel
- `V61` owns only governed communication packet, interpretation, surface typing, and
  later bridge-office law over that already governed stack
- `V62` should later own connector-specific transport trust over `V61`
- `V63` should later own remote operator UX over `V61`
- `V48` remains the owner of delegated worker execution after lawful dispatch

## Likely Repo-Native Surfaces

Likely implementation surfaces for `V61-A`:

- `packages/adeu_agentic_de/src/adeu_agentic_de/models.py`
  - new communication packet / interpretation / surface descriptor models
- `packages/adeu_agentic_de/src/adeu_agentic_de/checker.py`
  - loader / renderer / validator / runner support for `V61-A`
- `packages/adeu_agentic_de/src/adeu_agentic_de/export_schema.py`
  - authoritative and mirrored schema export
- `packages/adeu_agentic_de/src/adeu_agentic_de/__init__.py`
  - public export wiring
- `apps/api/scripts/`
  - one thin starter script for `V61-A`
- `apps/api/src/adeu_api/urm_routes.py`
  - likely consumption point later, but only if the slice actually needs route-level
    retrofit
- `packages/adeu_agentic_de/tests/`
  - package and schema tests
- `apps/api/tests/`
  - thin CLI and route/path tests

The starter slice should prefer retrofitting existing communication seams over adding
new product surfaces.

Likely implementation surfaces for `V61-B`:

- `packages/adeu_agentic_de/src/adeu_agentic_de/models.py`
  - new bridge-office binding and rewitness gate models
- `packages/adeu_agentic_de/src/adeu_agentic_de/checker.py`
  - loader / renderer / validator / runner support for `V61-B`
- `packages/adeu_agentic_de/src/adeu_agentic_de/export_schema.py`
  - authoritative and mirrored schema export
- `packages/adeu_agentic_de/src/adeu_agentic_de/__init__.py`
  - public export wiring
- `apps/api/scripts/`
  - one thin follow-on script for `V61-B`
- `packages/adeu_agentic_de/tests/`
  - package and schema tests
- `apps/api/tests/`
  - thin CLI tests

## Do Not Import

- raw transcript semantics as native witness
- generic chat memory as communication law
- communication send access as bridge office
- connector traffic as already-governed communication law
- remote operator UX as if already selected
- bridge-office binding in `V61-A`
- message-to-witness promotion in `V61-A`
- communication packets as execution or ticket authority
- any assumption that later `V61` lanes are authorized merely because they are drafted
