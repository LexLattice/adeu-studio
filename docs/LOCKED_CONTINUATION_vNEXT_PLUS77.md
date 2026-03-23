# Locked Continuation vNext+77

Status: `V40-A` implementation contract.

## V77 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v40a_architecture_semantic_root_schema_contract@1",
  "target_arc": "vNext+77",
  "target_path": "V40-A",
  "target_scope": "architecture_semantic_root_schema_export_and_hash_baseline",
  "intent_packet_schema": "adeu_architecture_intent_packet@1",
  "ontology_frame_schema": "adeu_architecture_ontology_frame@1",
  "boundary_graph_schema": "adeu_architecture_boundary_graph@1",
  "world_hypothesis_schema": "adeu_architecture_world_hypothesis@1",
  "semantic_ir_schema": "adeu_architecture_semantic_ir@1",
  "implementation_package": "adeu_architecture_ir",
  "deferred_package": "adeu_architecture_compiler",
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "decomposition_doc": "docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md"
}
```

## Slice

- Arc label: `vNext+77`
- Family label: `V40-A`
- Scope label: architecture semantic-root schema, export, and canonical-hash baseline

## Objective

Introduce the first concrete ASIR implementation slice by activating the semantic-root
package only and freezing the typed artifact family that architecture intent will flow
through before any deterministic compiler, hybrid adjudication, or lowering surface is
released.

This slice establishes the first repo-native schema substrate for:

- `adeu_architecture_intent_packet@1`
- `adeu_architecture_ontology_frame@1`
- `adeu_architecture_boundary_graph@1`
- `adeu_architecture_world_hypothesis@1`
- `adeu_architecture_semantic_ir@1`
- authoritative and mirrored schema exports
- deterministic canonicalization and hash derivation for the semantic root family
- explicit root/sibling artifact boundary exclusion

This slice remains deliberately prior to:

- deterministic assembly and whole-ASIR integrity compilation;
- checkpoint/oracle/human ambiguity handling;
- projection bundle or projection manifest release;
- conformance-report release;
- `adeu_core_ir` or UX lowerings.

Its job is to make the semantic-root family real and exact before any later slice tries
to consume it.

## Frozen Implementation Decisions

1. First active package:
   - activate `packages/adeu_architecture_ir` in `vNext+77`;
   - `packages/adeu_architecture_compiler` remains reserved and may not become active in
     this arc.
2. Root-family activation strategy:
   - `vNext+77` activates only the five semantic-root artifacts listed above;
   - `adeu_architecture_ir_delta@1`,
     `adeu_architecture_projection_bundle@1`,
     `adeu_architecture_projection_manifest@1`,
     `adeu_architecture_conformance_report@1`,
     `adeu_architecture_oracle_request@1`,
     `adeu_architecture_oracle_resolution@1`,
     `adeu_architecture_checkpoint_trace@1`, and
     `adeu_architecture_variant_manifest@1` are not part of this arc.
3. Schema export strategy:
   - authoritative JSON schemas must live under `packages/adeu_architecture_ir/schema/`;
   - mirrored exports must live under `spec/`;
   - mirrored exports must match the authoritative schemas byte-for-byte after
     canonical export.
4. Compiler provenance strategy:
   - the `compiler` object inside `adeu_architecture_semantic_ir@1` is allowed in this
     arc only as root-family schema/canonicalization provenance;
   - it must not imply active ownership by `packages/adeu_architecture_compiler`,
     released compiler passes, or whole-ASIR integrity execution in `vNext+77`.
5. Canonicalization strategy:
   - the root family must use deterministic canonical JSON serialization compatible with
     the repo's existing fail-closed artifact discipline;
   - `adeu_architecture_semantic_ir@1` alone carries a first-class persisted
     `semantic_hash` in this arc;
   - the other four activated root-family artifacts must still be canonicalizable and
     replayable under the same profile even if they do not persist dedicated content-hash
     fields yet;
   - root-family fixture replay must reject hash drift for the semantic root.
6. Authority policy propagation strategy:
   - all five activated root-family artifacts carry the same frozen
     `authority_boundary_policy` object in `vNext+77`;
   - no activated root-family artifact may weaken that policy by omission or by
     alternative local vocabulary.
7. Boundary strategy:
   - the semantic root is meaning-only and must exclude downstream projection,
     checkpoint, and readiness state;
   - sibling artifacts remain deferred rather than embedded as empty placeholders in the
     root.
8. Path decomposition strategy:
   - `vNext+77` is only the first concrete `V40-A` arc;
   - richer fixture coverage and a broader validator baseline remain available for a
     later concrete `V40-A` slice if needed.

## Required Deliverables

1. New typed ASIR package surface:
   - create `packages/adeu_architecture_ir`;
   - export the five activated artifact families from the package surface;
   - wire schema export helpers needed for authoritative and mirrored JSON-schema output.
2. Canonical semantic-root artifacts:
   - `adeu_architecture_intent_packet@1`
   - `adeu_architecture_ontology_frame@1`
   - `adeu_architecture_boundary_graph@1`
   - `adeu_architecture_world_hypothesis@1`
   - `adeu_architecture_semantic_ir@1`
3. Top-level schema anchors for the five activated artifacts:
   - `adeu_architecture_intent_packet@1` must bind at least:
     - `schema`
     - `intent_packet_id`
     - `source_set`
     - `requested_outcomes`
     - `non_goals`
     - `declared_constraints`
     - `authority_boundary_policy`
   - `adeu_architecture_ontology_frame@1` must bind at least:
     - `schema`
     - `ontology_frame_id`
     - `intent_packet_id`
     - `authority_boundary_policy`
     - `actors`
     - `surfaces`
     - `data_objects`
     - `boundaries`
     - `capabilities`
     - `workflows`
     - `states`
     - `transitions`
     - `decisions`
     - `failure_modes`
   - `adeu_architecture_boundary_graph@1` must bind at least:
     - `schema`
     - `boundary_graph_id`
     - `intent_packet_id`
     - `authority_boundary_policy`
     - `node_refs`
     - `edge_set`
     - `authority_crossings`
     - `sensitivity_crossings`
   - `adeu_architecture_world_hypothesis@1` must bind at least:
     - `schema`
     - `candidate_id`
     - `intent_packet_id`
     - `authority_boundary_policy`
     - `source_set`
     - `coverage_summary`
     - `ontology_bindings`
     - `epistemic_bindings`
     - `deontic_bindings`
     - `utility_bindings`
   - `adeu_architecture_semantic_ir@1` must bind at least the root fields frozen in the
     architecture doc:
     - `schema`
     - `architecture_id`
     - `intent_packet_id`
     - `semantic_hash`
     - `compiler`
     - `authority_boundary_policy`
     - `source_set`
     - `variant_lineage`
     - `ontology`
     - `epistemics`
     - `deontics`
     - `utility`
4. Root-boundary law:
   - `adeu_architecture_semantic_ir@1` must reject downstream fields including:
     - checkpoint-trace state,
     - projection state,
     - projection-manifest state,
     - conformance-summary or readiness state;
   - no root-family artifact may carry embedded emitted artifact refs, target-family
     route refs, or readiness claims;
   - no root artifact may silently embed emitted-surface file refs or route refs as if
     those were already released siblings;
   - `adeu_architecture_world_hypothesis@1` remains advisory and must not be exported as
     the authoritative meaning artifact.
5. Deterministic canonicalization and hashing law:
   - canonical JSON serialization for the five activated artifacts must be deterministic;
   - `semantic_hash` derivation for `adeu_architecture_semantic_ir@1` must be stable
     across repeated runs on the same payload;
   - schema export parity and fixture replay must use the same canonicalization profile.
6. Minimal root semantic-baseline law:
   - `adeu_architecture_semantic_ir@1` must require presence of:
     - `ontology`
     - `epistemics`
     - `deontics`
     - `utility`
     even if a section is empty;
   - every ambiguity object admitted by the root schema in this arc must carry:
     - `impact_class`
     - `resolution_route`
7. Lightweight root-local reference closure:
   - obvious broken refs inside the activated root family must fail closed;
   - `boundary_graph.node_refs` must resolve to ids present in the committed ontology
     fixture surface;
   - root-local ids that must be unique by schema contract must reject exact duplicates.
8. Committed reference fixtures:
   - one accepted root-family fixture ladder under
     `apps/api/fixtures/architecture/vnext_plus77/` covering:
     - intent packet,
     - ontology frame,
     - boundary graph,
     - advisory world hypothesis,
     - canonical semantic root;
   - the accepted fixture ladder must prove:
     - root/sibling separation,
     - schema export parity,
     - deterministic hash replay for the semantic root,
     - lightweight reference closure and duplicate-id rejection.
9. Python tests covering:
   - schema/model validation for the five activated artifacts;
   - authoritative/mirrored schema export parity;
   - deterministic canonicalization and hash replay for the accepted root fixture;
   - schema-level presence requirements for root sections and ambiguity fields;
   - fail-closed root-local reference-closure checks;
   - duplicate-id rejection where the root contract requires uniqueness;
   - rejection of downstream projection/checkpoint/conformance fields inside the
     semantic root;
   - rejection of authoritative export claims from the advisory world-hypothesis
     artifact.

## Hard Constraints

- `vNext+77` may not activate `packages/adeu_architecture_compiler`.
- `vNext+77` may not ship:
  - deterministic assembly entrypoints,
  - conformance-report artifacts,
  - oracle request or resolution artifacts,
  - checkpoint-trace artifacts,
  - projection bundle or projection manifest artifacts,
  - `adeu_core_ir` or UX lowerings,
  - API or web workbench routes,
  - direct prompt-to-code generation.
- The semantic root may not become a catch-all envelope for deferred pipeline state.
- The world-hypothesis artifact remains advisory in this slice:
  - it may describe a candidate world,
  - it may not mint authoritative architecture meaning by itself.
- The `compiler` object in the semantic root may not be used to smuggle in deferred
  compiler-pass claims or package activation.
- The formal Lean sidecar may mirror frozen finite vocabulary only:
  - it is not required for slice validity,
  - it may not silently redefine the released schema contract.
- `vNext+77` may not claim `V40-A` complete if richer validator coverage or follow-on
  fixture surfaces remain deferred.

## PR Shape

- Single integrated PR.

Rationale:

- the package activation, root-family schemas, canonicalization/hashing helpers,
  exported schemas, reference fixture ladder, and tests are tightly coupled and should
  land together so the first ASIR substrate freezes as one coherent baseline.
