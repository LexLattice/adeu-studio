# Draft ADEU Resident-Agent Connector Admission And External Assistant Bridge V62B Implementation Mapping v0

Status: support-layer slice mapping for `V62-B`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the bounded
`V62-B` follow-on slice into a repo-native implementation shape so the shipped
`V62-A` admitted connector path and ingress bridge can gain one explicit
external-assistant egress bridge packet without letting outbound connector
delivery, bridge-office access, rewitness posture, or upstream assistant output
become ambient authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v45.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_V62_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS170.md`

## Slice Boundary

`V62-B` instantiates only:

- one explicit `V62-A` to `V62-B` lane handoff via `agentic_de_lane_drift_record@1`
- the same exact admitted connector path already shipped in `V62-A`:
  - connector snapshot create route:
    - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot`
  - connector snapshot get route:
    - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot/{snapshot_id}`
  - `provider = codex`
  - `execution_mode = live`
- the same selected connector-carried principal only:
  - `external_assistant`
- one new typed external assistant egress bridge packet only:
  - `agentic_de_external_assistant_egress_bridge_packet@1`

`V62-B` consumes, but does not reopen:

- the shipped `V62-A` connector admission record
- the shipped `V62-A` external assistant ingress bridge packet
- the shipped `V61-A` communication egress basis
- the shipped `V61-B` bridge-office and rewitness posture where selected
- the shipped `V60` continuation lineage

`V62-B` does not instantiate:

- human-via-connector semantics
- new connector admission law
- new ingress bridge law
- connector advisory hardening or provenance-drift registers
- remote-operator UX
- repo-bound writable authority
- execute widening
- dispatch widening

## Egress Bridge Mapping

The external assistant egress bridge packet should remain typed, replayable, and
fail-closed.

At minimum the repo-native follow-on should carry:

- admitted connector ref
- shipped ingress bridge ref
- selected principal class:
  - `external_assistant`
- external assistant egress payload facts or summary
- consumed shipped `V61` communication egress basis:
  - communication egress packet ref
- consumed shipped `V61-B` posture where selected:
  - bridge-office binding ref or none
  - message rewitness gate ref or none
- direct consumed rewitness basis summary or none:
  - explicit positive witness basis / certificate posture when present
  - explicit none when rewitness posture is not selected and not consumed in the
    packet
- latest continuation basis ref or equivalent consumed lineage pointer
- latest continuation basis selection summary
- frozen policy anchor ref
- bridge basis summary
- provenance fields:
  - `field_origin_tags`
  - `field_dependence_tags`
  - `root_origin_dedup_summary`

The packet should remain:

- egress only
- posture-bearing only
- not native witness
- not charter amendment
- not continuation mutation
- not bridge office by itself
- not repo-write authority
- not execute authority

## Bridge Basis Law

The follow-on should prove:

- same admitted connector basis plus same shipped ingress bridge basis plus same
  selected connector principal plus same consumed `V61` communication egress basis
  plus same frozen policy yields the same egress bridge packet
- where `V61-B` bridge-office or rewitness posture is selected, the same
  consumed office / rewitness basis plus the same frozen policy yields the same
  egress bridge packet
- direct consumed rewitness basis summary remains explicit when positive so
  replayability does not depend only on chasing upstream `V61-B` records
- missing or inconsistent connector / egress / office / rewitness basis fails
  closed
- positive rewitness consumption remains basis-bearing:
  - witness basis ref or certificate ref when positive
- `bridge_office_binding_ref_or_none = none` means bridge-office posture was not
  selected and not consumed in this packet
- `message_rewitness_gate_ref_or_none = none` means rewitness posture was not
  selected and not consumed in this packet
- missing optional office / rewitness refs may not be inferred from prior
  emission capability or connector availability
- outbound bridge does not self-promote into:
  - native witness
  - charter mutation
  - continuation mutation
  - bridge office
  - repo-write authority
  - act authority

## Likely Repo-Native Surfaces

Likely implementation surfaces for `V62-B`:

- `packages/adeu_agentic_de/src/adeu_agentic_de/models.py`
  - external assistant egress bridge model
- `packages/adeu_agentic_de/src/adeu_agentic_de/checker.py`
  - validation / rendering / runner support for `V62-B`
- `packages/adeu_agentic_de/src/adeu_agentic_de/export_schema.py`
  - authoritative and mirrored schema export
- `packages/adeu_agentic_de/src/adeu_agentic_de/__init__.py`
  - public export wiring
- `apps/api/scripts/`
  - one thin follow-on runner for `V62-B`
- `packages/adeu_agentic_de/tests/`
  - package, fixture, and schema tests
- `apps/api/tests/`
  - thin CLI / backend seam tests

## Starter Proof Obligations

The first implementation should prove:

- shipped `V62-A` admission and ingress bridge remain the only admitted basis
- outbound bridge remains explicit, replayable, and fail-closed
- the selected connector principal remains `external_assistant` only
- human-via-connector semantics do not land in this slice
- `V61-B` bridge-office / rewitness posture is consumed explicitly when selected
- direct consumed rewitness basis summary is carried when positive
- missing positive rewitness basis fails closed
- optional office / rewitness refs stay explicit when absent and are not
  availability-derived
- raw outbound connector payload does not become witness, charter, continuation,
  bridge-office, repo, execute, or dispatch authority
- the selected connector seam remains non-generalizing by default
