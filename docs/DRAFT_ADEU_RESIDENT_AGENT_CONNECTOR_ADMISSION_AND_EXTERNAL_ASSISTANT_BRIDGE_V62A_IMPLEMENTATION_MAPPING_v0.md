# Draft ADEU Resident-Agent Connector Admission And External Assistant Bridge V62A Implementation Mapping v0

Status: support-layer slice mapping for `V62-A`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the bounded `V62-A`
starter slice into a repo-native implementation shape so one admitted connector path
can carry one external-assistant-only ingress bridge over shipped `V61`
communication law without letting connector transport, connector identity, or raw
upstream assistant output become ambient authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v45.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_V62_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS169.md`

## Slice Boundary

`V62-A` instantiates only:

- one explicit `V61-C` to `V62-A` lane handoff via `agentic_de_lane_drift_record@1`
- one admitted connector path only:
  - connector snapshot create route:
    - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot`
  - connector snapshot get route:
    - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot/{snapshot_id}`
  - `provider = codex`
  - `execution_mode = live`
- one selected connector-carried principal only:
  - `external_assistant`
- one typed connector admission record only:
  - `agentic_de_connector_admission_record@1`
- one typed external assistant ingress bridge packet only:
  - `agentic_de_external_assistant_ingress_bridge_packet@1`

`V62-A` does not instantiate:

- human-via-connector semantics
- outbound bridge packets
- connector advisory hardening or provenance-drift registers
- remote-operator UX
- repo-bound writable authority
- execute widening
- dispatch widening

## Consumed Shipped Surfaces

`V62-A` should consume, not reopen:

- shipped `V60-A`, `V60-B`, and `V60-C` continuation outputs
- shipped `V61-A` communication packet / descriptor / interpretation law
- shipped `V61-B` bridge-office / rewitness posture as prior-family evidence only in
  this starter slice, not as a selected live ingress basis
- shipped `V61-C` advisory communication hardening as prior-family evidence only
- shipped URM connector snapshot / exposure infrastructure in `packages/urm_runtime`

The starter slice should prefer retrofitting the existing connector snapshot /
exposure seams before adding any new connector product routes or UI semantics.

## Admission Basis Mapping

The connector admission record should remain typed, replayable, and fail-closed.

At minimum the repo-native starter should carry:

- connector snapshot ref
- connector snapshot hash
- capability snapshot ref
- provider class
- snapshot create/get route basis
- exposure basis from:
  - `exposed_connectors`
  - `connector_exposure`
- freshness basis summary:
  - `execution_mode = live`
  - explicit `min_acceptable_ts` posture when present
- selected principal class:
  - `external_assistant`
- frozen policy anchor ref
- typed admission verdict
- provenance fields:
  - `field_origin_tags`
  - `field_dependence_tags`
  - `root_origin_dedup_summary`

The starter verdict family should stay explicit and closed:

- `admitted`
- `rejected`
- `stale_basis`
- `unknown_basis`
- `withheld_by_policy`

Missing or stale snapshot / exposure / freshness basis must fail closed.

## Ingress Bridge Mapping

The external assistant ingress bridge packet should remain typed, replayable, and
strictly narrower than `V62-B`.

At minimum the repo-native starter should carry:

- admitted connector ref
- selected principal class:
  - `external_assistant`
- external assistant payload facts
- consumed shipped `V61` communication basis:
  - communication ingress packet ref
  - surface-authority descriptor ref
  - ingress interpretation ref
  - no `V61-B` bridge-office binding ref in `V62-A`
  - no `V61-B` rewitness gate ref in `V62-A`
- latest continuation basis ref or equivalent consumed lineage pointer
- frozen policy anchor ref
- provenance fields:
  - `field_origin_tags`
  - `field_dependence_tags`
  - `root_origin_dedup_summary`

The bridge packet should remain:

- ingress only
- posture-bearing only
- not charter compilation
- not continuation mutation
- not bridge office by itself
- not native witness
- not act authority

## Likely Repo-Native Surfaces

Likely implementation surfaces for `V62-A`:

- `packages/adeu_agentic_de/src/adeu_agentic_de/models.py`
  - connector admission and ingress bridge models
- `packages/adeu_agentic_de/src/adeu_agentic_de/checker.py`
  - validation / rendering / runner support for `V62-A`
- `packages/adeu_agentic_de/src/adeu_agentic_de/export_schema.py`
  - authoritative and mirrored schema export
- `packages/adeu_agentic_de/src/adeu_agentic_de/__init__.py`
  - public export wiring
- `apps/api/scripts/`
  - one thin starter runner for `V62-A`
- `packages/urm_runtime/src/urm_runtime/`
  - consumption only of connector snapshot / exposure facts already emitted by the
    runtime
- `packages/adeu_agentic_de/tests/`
  - package, fixture, and schema tests
- `apps/api/tests/`
  - thin CLI / backend seam tests

## Starter Proof Obligations

The first implementation should prove:

- same connector identity facts plus same snapshot / exposure / freshness basis plus
  same frozen policy yields the same admission verdict
- missing or stale connector basis fails closed
- admission verdict remains drawn only from the explicit starter verdict set
- external-assistant principal selection is explicit
- human-via-connector semantics do not land in `V62-A`
- same admitted connector basis plus same external assistant payload facts plus same
  consumed `V61-A` communication basis plus same frozen policy yields the same
  ingress bridge packet
- raw connector payload does not self-promote into witness, charter, continuation,
  or act authority
- the selected connector seam does not generalize by default into broader connector,
  remote-operator, repo, execute, or dispatch law
