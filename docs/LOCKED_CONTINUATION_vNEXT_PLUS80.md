# Locked Continuation vNext+80

Status: `V40-D` implementation contract.

## V80 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v40d_architecture_core_ir_lowering_contract@1",
  "target_arc": "vNext+80",
  "target_path": "V40-D",
  "target_scope": "architecture_core_ir_projection_bundle_manifest_and_honesty_baseline",
  "semantic_ir_schema": "adeu_architecture_semantic_ir@1",
  "conformance_report_schema": "adeu_architecture_conformance_report@1",
  "checkpoint_trace_schema": "adeu_architecture_checkpoint_trace@1",
  "projection_bundle_schema": "adeu_architecture_projection_bundle@1",
  "projection_manifest_schema": "adeu_architecture_projection_manifest@1",
  "target_family": "adeu_core_ir@0.1",
  "implementation_package": "adeu_architecture_compiler",
  "upstream_root_package": "adeu_architecture_ir",
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "decomposition_doc": "docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v20.md",
  "hybrid_baseline_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS79.md"
}
```

## Slice

- Arc label: `vNext+80`
- Family label: `V40-D`
- Scope label: architecture core IR lowering, projection bundle, manifest, and honesty
  baseline

## Objective

Introduce the first concrete ASIR lowering slice by extending the released architecture
compiler lane with typed projection artifacts that consume released semantic-root,
conformance, and checkpoint-trace surfaces without reopening any of them.

This slice establishes the first repo-native projection substrate for:

- canonical `adeu_architecture_projection_bundle@1`
- canonical `adeu_architecture_projection_manifest@1`
- deterministic lowering from ASIR into `adeu_core_ir@0.1` only
- inspectable projection-unit lineage and output binding
- fail-closed blocked-vs-ready projection honesty

This slice remains deliberately prior to:

- `ux_domain_packet@1`
- `ux_morph_ir@1`
- API or web human-review workbench routes
- broader target-family release beyond `adeu_core_ir@0.1`
- family-complete evidence and release wiring

Its job is to make one narrow downstream lowering honest and inspectable before any
wider surface family tries to consume ASIR as if projection and UX release were already
the same thing.

## Frozen Implementation Decisions

1. Lowering package strategy:
   - keep `packages/adeu_architecture_compiler` as the active package for the first
     `V40-D` slice;
   - no separate lowering package may be introduced in `vNext+80`;
   - `packages/adeu_architecture_ir` remains authoritative for released root-family
     schemas and may not be silently redefined here.
2. Upstream consumption strategy:
   - `vNext+80` must consume released `V40-A` semantic-root artifacts, released
     `V40-B` conformance outputs, and released `V40-C` checkpoint-trace state or exact
     validated derivatives thereof;
   - no projection artifact may lower directly from an undervalidated semantic root;
   - every emitted projection artifact must bind back to released semantic-root,
     conformance, and checkpoint lineage.
3. Projection artifact-release strategy:
   - the only newly released artifact families in this slice are:
     - `adeu_architecture_projection_bundle@1`
     - `adeu_architecture_projection_manifest@1`
   - authoritative JSON schemas must live under
     `packages/adeu_architecture_compiler/schema/`;
   - mirrored exports must live under `spec/`;
   - none of these artifacts may collapse into UX lowerings, API/workbench surfaces,
     or emitted application authority.
4. Target-family strategy:
   - the only lawful target family in `vNext+80` is `adeu_core_ir@0.1`;
   - ready projection units may emit authoritative `adeu_core_ir@0.1` artifacts in
     this slice;
   - blocked projection units may not emit any target-family artifact refs in this
     slice;
   - no `ux_domain_packet`, `ux_morph_ir`, `api_contract`, `workflow_contract`,
     `event_contract`, or `test_obligation_bundle` target may be emitted in this
     slice.
5. Projection-unit strategy:
   - every `projection_unit` in this slice must bind at least:
     - `projection_id`
     - `target_family`
     - `source_refs`
     - `readiness`
     - `blocked_by_ambiguity_refs`
     - `output_artifact_refs`
     - `compiler_entrypoint`
   - the starter `readiness` vocabulary in this slice must be exactly:
     - `ready`
     - `blocked`
   - no other projection-unit readiness state is allowed in the first baseline.
   - one projection bundle may contain a mix of `ready` and `blocked` units;
   - `projection_unit.readiness = ready` is lawful only when:
     - the released source conformance report has `projection_readiness = ready`; and
     - no active blocking ambiguity refs remain for that unit under released
       checkpoint-trace lineage;
   - `projection_unit.readiness = blocked` requires:
     - `output_artifact_refs = []`; and
     - explicit `blocked_by_ambiguity_refs` lineage.
6. Lowering strategy:
   - lowering must target `adeu_core_ir@0.1` only;
   - ontology objects lower into `O` nodes;
   - facts, assumptions, ambiguities, and evidence requirements lower into `E` nodes;
   - obligations, prohibitions, permissions, gates, invariants, and escalation rules
     lower into `D` nodes;
   - goals, metrics, priorities, and explicit tradeoffs lower into `U` nodes;
   - starter edge use may be limited to:
     - `depends_on`
     - `gates`
     - `serves_goal`
     - `prioritizes`
     - `justifies`
   - no broader edge-family baseline is required in `vNext+80`;
   - no semantic claim beyond those starter edges is released in this slice, and the
     absence of a broader edge family is intentional rather than an omission.
7. Projection-manifest strategy:
   - the manifest must make the lowering relation inspectable:
     - which ASIR refs each projection unit consumed;
     - which released root-family refs were consumed by the lowering;
     - which emitted artifacts or draft outputs were produced;
     - which blocking ambiguity refs remained active;
     - which compiler entrypoint and version materialized the output;
   - no emitted artifact may appear without explicit source-unit lineage.
8. Projection-honesty strategy:
   - no projection unit may claim `readiness = ready` while
     `blocked_by_ambiguity_refs` is non-empty;
   - no projection unit may claim `readiness = ready` when released conformance state
     remains blocked;
   - unresolved blocking ambiguity preserved by released checkpoint-trace state must
     remain blocking at projection time;
   - any source ref with `final_adjudication = escalated_human` remains blocking for
     projection readiness in this slice;
   - final adjudication in checkpoint trace and projection readiness in projection
     artifacts remain distinct surfaces;
   - blocked projection units must not imply emitted authoritative output exists.
9. Checkpoint-trace consumption strategy:
   - released `V40-C` checkpoint trace is a mandatory consumed input in this slice,
     including deterministic-ready lowerings;
   - `checkpoint_trace_ref` is therefore required at the top level for both bundle and
     manifest artifacts in `vNext+80`;
   - no lowering may treat the absence of released checkpoint-trace lineage as
     equivalent to a deterministic-ready projection state.
10. Bundle/compiler provenance strategy:
   - the bundle carries compiler provenance in this slice via:
     - `compiler`
     - `compiler_version`
   - the manifest carries the fuller lowering provenance surface, including:
     - `compiler_entrypoint`
     - `compiler_version`
     - consumed lineage refs.
11. Path decomposition strategy:
   - `vNext+80` is the first concrete `V40-D` arc;
   - broader lowering coverage, richer manifest diagnostics, or wider projection-unit
     validators may remain available for a later concrete `V40-D` slice if needed.

## Required Deliverables

1. New typed projection artifact surfaces inside the existing compiler package:
   - export the two activated projection artifact families from
     `packages/adeu_architecture_compiler`;
   - wire schema-export helpers needed for authoritative and mirrored JSON-schema
     output.
2. Canonical projection artifacts:
   - `adeu_architecture_projection_bundle@1`
   - `adeu_architecture_projection_manifest@1`
3. Deterministic lowering entrypoints that:
   - consume released `adeu_architecture_semantic_ir@1`,
     `adeu_architecture_conformance_report@1`, and
     `adeu_architecture_checkpoint_trace@1` plus any exact released companion inputs
     needed for lowering context;
   - lower only into `adeu_core_ir@0.1`;
   - materialize canonical bundle and manifest artifacts under the frozen vocabularies
     above;
   - fail closed when released readiness is blocked, blocking ambiguity remains active,
     or manifest lineage would be incomplete or dishonest.
4. Top-level schema anchors for `adeu_architecture_projection_bundle@1`:
   - `schema`
   - `bundle_id`
   - `architecture_id`
   - `semantic_hash`
   - `conformance_report_ref`
   - `checkpoint_trace_ref`
   - `target_family`
   - `compiler`
   - `compiler_version`
   - `projection_units`
5. Projection-unit anchors for the bundle in this slice:
   - `projection_id`
   - `target_family`
   - `source_refs`
   - `readiness`
   - `blocked_by_ambiguity_refs`
   - `output_artifact_refs`
   - `compiler_entrypoint`
6. Top-level schema anchors for `adeu_architecture_projection_manifest@1`:
   - `schema`
   - `manifest_id`
   - `architecture_id`
   - `semantic_hash`
   - `conformance_report_ref`
   - `checkpoint_trace_ref`
   - `source_root_refs`
   - `target_family`
   - `compiler_entrypoint`
   - `compiler_version`
   - `projection_units`
   - `touched_artifact_refs`
   - `blocked_by_ambiguity_refs`
7. Deterministic lowering laws that fail closed on at least:
   - any attempt to lower directly from semantic-root state without released
     conformance and checkpoint lineage;
   - any target family other than `adeu_core_ir@0.1`;
   - any blocked projection unit with non-empty `output_artifact_refs`;
   - any projection unit claiming `readiness = ready` while
     `blocked_by_ambiguity_refs` is non-empty;
   - any projection unit claiming `readiness = ready` while source conformance remains
     blocked;
   - any emitted output artifact lacking explicit `source_refs` lineage;
   - any manifest claim that omits emitted-artifact, source-ref, or compiler-entrypoint
     lineage for a released projection unit;
   - any projection unit that misreports unresolved blocking ambiguity or escalated
     human checkpoint state as `ready`;
   - any attempt to widen into UX or application-family lowering in this slice.
8. Committed reference fixtures:
   - one accepted ready lowering fixture ladder under
     `apps/api/fixtures/architecture/vnext_plus80/` covering:
     - released semantic-root input
     - released conformance input
     - released checkpoint-trace input
     - canonical projection bundle output
     - canonical projection manifest output
     - canonical `adeu_core_ir` derivative
   - one accepted blocked-honesty fixture ladder proving:
     - blocked ambiguity remains visible at projection time;
     - blocked projection units carry empty `output_artifact_refs`;
     - blocked projection units do not claim emitted authoritative output.
9. Python tests covering:
   - schema/model validation for the two activated projection artifacts;
   - authoritative/mirrored schema export parity;
   - deterministic lowering replay from the accepted ready fixture ladder;
   - `adeu_core_ir` target-family-only enforcement;
   - O/E/D/U lowering structure over the starter fixture surface;
   - manifest/source-lineage honesty and fail-closed blocked-vs-ready behavior;
   - rejection of UX, API, or workbench lowering artifacts inside the first
     `V40-D` lane.

## Hard Constraints

- `vNext+80` may not reopen or redefine the released `V40-A` root-family schema
  contract.
- `vNext+80` may not reopen or redefine the released `V40-B` conformance contract.
- `vNext+80` may not reopen or redefine the released `V40-C` checkpoint/oracle/trace
  contract.
- `vNext+80` may not ship:
  - `ux_domain_packet@1` lowering,
  - `ux_morph_ir@1` lowering,
  - API or web human-review workbench routes,
  - broader target-family projection beyond `adeu_core_ir@0.1`,
  - direct prompt-to-code generation.
- No projection artifact in this slice may imply that final adjudication itself is
  projection permission; projection readiness remains a downstream lowering surface.
- Blocked projection units may not imply emitted authoritative downstream surfaces
  exist and must carry empty `output_artifact_refs`.
- The formal Lean sidecar may continue in parallel:
  - it is not required for slice validity,
  - it may not silently redefine the released lowering contract.

## PR Shape

- Single integrated PR.

Rationale:

- lowering logic, schema/export baseline, projection-unit grammar, manifest honesty,
  committed fixtures, and validator guards form one tight architectural brick;
- landing them together keeps the first lowering contract exact and avoids inventing an
  artificial sequencing seam inside an already-atomic slice.
