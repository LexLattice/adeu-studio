# Locked Continuation vNext+81

Status: `V40-E` implementation contract.

## V81 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v40e_architecture_ux_domain_packet_compatibility_contract@1",
  "target_arc": "vNext+81",
  "target_path": "V40-E",
  "target_scope": "architecture_ux_domain_packet_compatibility_baseline",
  "semantic_ir_schema": "adeu_architecture_semantic_ir@1",
  "conformance_report_schema": "adeu_architecture_conformance_report@1",
  "checkpoint_trace_schema": "adeu_architecture_checkpoint_trace@1",
  "projection_bundle_schema": "adeu_architecture_projection_bundle@1",
  "projection_manifest_schema": "adeu_architecture_projection_manifest@1",
  "ux_domain_packet_schema": "ux_domain_packet@1",
  "implementation_package": "adeu_architecture_compiler",
  "target_family_package": "adeu_core_ir",
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "decomposition_doc": "docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v21.md",
  "lowering_baseline_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS80.md"
}
```

## Slice

- Arc label: `vNext+81`
- Family label: `V40-E`
- Scope label: architecture UX-domain lowering and compatibility baseline

## Objective

Introduce the first concrete ASIR UX-compatibility slice by extending the released
architecture compiler lane with typed lowering that consumes released semantic-root,
conformance, checkpoint-trace, and projection surfaces and emits canonical
`ux_domain_packet@1` only.

This slice establishes the first repo-native UX compatibility substrate for:

- deterministic lowering from released ASIR / `V40-D` projection lineage into
  `ux_domain_packet@1` only;
- exact reuse of the existing UX governance target-family contract under
  `packages/adeu_core_ir`;
- inspectable lineage from released architecture/projection refs into emitted UX packet
  outputs;
- fail-closed blocked-vs-ready UX-output honesty;
- explicit preservation of no direct brief-to-UI or prompt-to-surface generation.

This slice remains deliberately prior to:

- `ux_morph_ir@1`;
- surface compiler export or rendered-surface release;
- API or web human-review workbench routes;
- broader application target-family release;
- family-complete evidence and release wiring.

Its job is to make one narrow UX packet compatibility path lawful and inspectable before
any wider UX or workbench surface tries to consume ASIR as if typed IR lowering and UI
generation were already the same thing.

## Frozen Implementation Decisions

1. UX-lowering package strategy:
   - keep `packages/adeu_architecture_compiler` as the active lowering package for the
     first `V40-E` slice;
   - keep `packages/adeu_core_ir` authoritative for the existing
     `ux_domain_packet@1` target-family schema and validators;
   - no new UX target-family schema version may be introduced in `vNext+81`.
2. Upstream consumption strategy:
   - `vNext+81` must consume released `V40-A` semantic-root artifacts, released
     `V40-B` conformance outputs, released `V40-C` checkpoint-trace state, and released
     `V40-D` projection bundle/manifest state or exact validated derivatives thereof;
   - no UX packet may be emitted directly from an undervalidated semantic root or
     without released projection lineage;
   - released `V40-C` checkpoint-trace state is a mandatory consumed input in this
     slice; `vNext+81` may not lower from released projection lineage alone;
   - every emitted UX packet must bind back to released semantic-root, conformance,
     checkpoint, and projection lineage through the released lowering surfaces.
3. Target-family release strategy:
   - the only newly legalized emitted target family in this slice is
     `ux_domain_packet@1`;
   - authoritative `ux_domain_packet@1` JSON schema remains under
     `packages/adeu_core_ir/schema/`;
   - mirrored export remains under `spec/`;
   - this slice must consume that released target-family contract rather than minting a
     parallel architecture-local UX packet schema;
   - emitted `ux_domain_packet@1` is an authoritative typed IR target artifact only:
     it is not a rendered UI surface, not a workbench release, and not permission to
     generate React trees.
4. Governance compatibility strategy:
   - every emitted `ux_domain_packet@1` must validate against the released
     `UXDomainPacket` contract in `packages/adeu_core_ir`;
   - frozen approved-profile binding and frozen authority-boundary policy must remain
     exact;
   - any released UX governance reference surfaces required by the existing validator
     lane must be consumed as released refs or exact validated derivatives;
   - `approved_profile_id`, `authority_boundary_policy`, and any required governance
     reference surfaces must resolve to released refs or exact validated derivatives
     with no silent defaults;
   - `vNext+81` may not weaken UX governance by omission, alternate vocabulary, or
     silent defaulting.
5. UX-domain target strategy:
   - every emitted `ux_domain_packet@1` in this slice must bind at least:
     - `schema`
     - `reference_surface_family`
     - `reference_instance_id`
     - `approved_profile_id`
     - `supporting_artifacts`
     - `authority_boundary_policy`
     - `domain`
     - `primary_user_archetype`
     - `device_class`
     - `environment_assumptions`
     - `risk_level`
     - `trust_sensitivity`
     - `interaction_mode`
     - `tasks`
     - `latency_assumptions`
     - `reversibility_policies`
     - `required_evidence_visibility`
     - `utility_ranking`
   - no `ux_morph_ir`-only fields may be smuggled into the packet surface in the first
     baseline;
   - in the first baseline, each emitted `ux_domain_packet@1` must map to exactly one
     released `projection_id` through the released projection-manifest lineage;
   - no ready projection unit may emit more than one `ux_domain_packet@1` in
     `vNext+81`.
6. Projection/UX honesty strategy:
   - a `ux_domain_packet@1` output is lawful only for a released projection unit that
     remains `ready` under the released `V40-D` honesty law;
   - a released projection unit may emit zero or one `ux_domain_packet@1` in this
     slice, never more than one;
   - if the source projection unit is `blocked`, then no `ux_domain_packet@1` artifact
     may be emitted for that unit in this slice;
   - blocked architecture or blocked projection state may not emit a UX packet in this
     slice;
   - no emitted UX packet may appear without matching released projection-manifest
     lineage, explicit source refs, and exact binding to one released `projection_id`;
   - no emitted UX packet may imply that typed UX compatibility is equivalent to direct
     React tree generation, workbench release, or application authority.
7. Morph deferral strategy:
   - `ux_morph_ir@1` remains deferred in the first concrete `V40-E` arc;
   - no surface compiler export, rendered-surface release, or workbench/API route may
     be emitted in `vNext+81`;
   - no direct prompt-to-surface path is authorized in this slice.
8. Path decomposition strategy:
   - `vNext+81` is the first concrete `V40-E` arc;
   - deeper UX reference-bundle compatibility, `ux_morph_ir@1`, or broader UX
     diagnostics may remain available for a later concrete `V40-E` slice if needed.

## Required Deliverables

1. New typed UX-lowering entrypoints inside the existing architecture compiler package:
   - extend `packages/adeu_architecture_compiler` with lowering helpers that emit
     canonical `ux_domain_packet@1` only;
   - consume the released `ux_domain_packet@1` schema/validator surface from
     `packages/adeu_core_ir` rather than copying it.
2. Canonical emitted target artifact in this slice:
   - `ux_domain_packet@1`
3. Deterministic UX-lowering entrypoints that:
   - consume released `adeu_architecture_semantic_ir@1`,
     `adeu_architecture_conformance_report@1`,
     `adeu_architecture_checkpoint_trace@1`,
     `adeu_architecture_projection_bundle@1`, and
     `adeu_architecture_projection_manifest@1` plus any exact released companion inputs
     needed for UX context;
   - emit only `ux_domain_packet@1`;
   - bind each emitted UX packet to exactly one released ready `projection_id`;
   - fail closed when released architecture or projection readiness is blocked, when
     projection lineage is incomplete, or when the emitted packet violates the released
     UX governance contract.
4. Consumed target-family anchors for `ux_domain_packet@1` that must validate in this
   slice:
   - `schema`
   - `reference_surface_family`
   - `reference_instance_id`
   - `approved_profile_id`
   - `supporting_artifacts`
   - `authority_boundary_policy`
   - `domain`
   - `primary_user_archetype`
   - `device_class`
   - `environment_assumptions`
   - `risk_level`
   - `trust_sensitivity`
   - `interaction_mode`
   - `tasks`
   - `latency_assumptions`
   - `reversibility_policies`
   - `required_evidence_visibility`
   - `utility_ranking`
5. Deterministic UX-lowering laws that fail closed on at least:
   - any attempt to emit `ux_domain_packet@1` directly from semantic-root state without
     released conformance, checkpoint, and projection lineage;
   - any blocked architecture or blocked projection unit being emitted as a lawful UX
     packet;
   - any source projection unit with `readiness = blocked` emitting a
     `ux_domain_packet@1` artifact;
   - any emitted UX packet that does not map to exactly one released ready
     `projection_id`;
   - any ready projection unit emitting more than one UX packet in this slice;
   - any `ux_domain_packet@1` output that violates the released approved-profile or
     authority-boundary policy contract;
   - any approved-profile, authority-boundary, or required governance reference surface
     being admitted by silent default rather than released ref or exact validated
     derivative;
   - any emitted UX packet lacking explicit source/projection lineage;
   - any attempt to widen into `ux_morph_ir@1`, surface compiler export, API/workbench
     routes, or direct prompt-to-surface generation in this slice.
6. Committed reference fixtures:
   - one accepted ready UX-lowering fixture ladder under
     `apps/api/fixtures/architecture/vnext_plus81/` covering:
     - released semantic-root input
     - released conformance input
     - released checkpoint-trace input
     - released projection bundle/manifest input
     - canonical `ux_domain_packet@1` output
   - one accepted blocked/no-emit fixture ladder proving:
     - blocked architecture or blocked projection state does not emit a UX packet;
     - blocked source projection units emit zero UX packets exactly;
     - emitted ready UX packets bind to exactly one released ready `projection_id`;
     - no blocked case can misreport direct UX compatibility as a lawful output.
7. Python tests covering:
   - `ux_domain_packet@1` model validation through the released `adeu_core_ir` target
     family;
   - deterministic UX lowering replay from the accepted ready fixture ladder;
   - approved-profile and authority-boundary compatibility checks;
   - one-to-one projection-unit binding and zero-or-one packet-per-ready-unit behavior;
   - fail-closed blocked/no-emit behavior;
   - rejection of `ux_morph_ir`, surface compiler export, workbench/API, and direct
     prompt-to-surface widening inside the first `V40-E` lane.

## Hard Constraints

- `vNext+81` may not reopen or redefine the released `V40-A` root-family schema
  contract.
- `vNext+81` may not reopen or redefine the released `V40-B` conformance contract.
- `vNext+81` may not reopen or redefine the released `V40-C` checkpoint/oracle/trace
  contract.
- `vNext+81` may not reopen or redefine the released `V40-D` projection bundle,
  manifest, and `adeu_core_ir` lowering honesty contract.
- `vNext+81` may not ship:
  - `ux_morph_ir@1`,
  - surface compiler export,
  - rendered-surface release,
  - API or web human-review workbench routes,
  - direct prompt-to-surface generation,
  - direct prompt-to-code generation.
- If a released projection unit is `blocked`, `vNext+81` may not emit any
  `ux_domain_packet@1` artifact for that unit.
- No emitted UX packet in this slice may imply that typed UX compatibility is the same
  thing as released surface generation or application authority.
- No emitted UX packet in this slice may be backed by more than one released
  `projection_id`, and no ready projection unit may emit more than one UX packet.
- No new UX target-family schema version may be minted in this slice; the released
  `adeu_core_ir` UX contract remains authoritative.
- The formal Lean sidecar may continue in parallel:
  - it is not required for slice validity,
  - it may not silently redefine the released UX-lowering contract.

## PR Shape

- Single integrated PR.

Rationale:

- the first UX-domain lowering seam is one atomic architectural brick:
  released architecture/projection consumption, target-family validation, compatibility
  guards, committed fixtures, and fail-closed no-emit behavior belong together;
- splitting that first UX-domain baseline would introduce an artificial seam inside one
  already-bounded target-family widening.
