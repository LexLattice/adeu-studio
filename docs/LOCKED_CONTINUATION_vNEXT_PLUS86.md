# Locked Continuation vNext+86

Status: `V41-D` implementation contract.

## V86 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v41d_practical_analysis_intended_compile_contract@1",
  "target_arc": "vNext+86",
  "target_path": "V41-D",
  "target_scope": "practical_analysis_intended_semantic_root_compile_baseline",
  "analysis_request_schema": "adeu_architecture_analysis_request@1",
  "analysis_settlement_schema": "adeu_architecture_analysis_settlement_frame@1",
  "observation_frame_schema": "adeu_architecture_observation_frame@1",
  "intent_packet_schema": "adeu_architecture_intent_packet@1",
  "ontology_frame_schema": "adeu_architecture_ontology_frame@1",
  "boundary_graph_schema": "adeu_architecture_boundary_graph@1",
  "world_hypothesis_schema": "adeu_architecture_world_hypothesis@1",
  "semantic_ir_schema": "adeu_architecture_semantic_ir@1",
  "implementation_package": "adeu_architecture_compiler",
  "authoritative_root_package": "adeu_architecture_ir",
  "reuses_released_v40a_root_family": true,
  "intended_observed_lane_separation_required": true,
  "request_and_settlement_normative_priority_required": true,
  "entitled_settlement_required_for_emit": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "decomposition_doc": "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v23.md"
}
```

## Slice

- Arc label: `vNext+86`
- Family label: `V41-D`
- Scope label: practical analysis intended semantic-root compile baseline

## Objective

Introduce the first concrete repo-grounded intended-compile slice by activating only
the intended architecture lane and freezing deterministic materialization of the
already-released `V40-A` semantic-root artifact family over the released `V41-A`
request boundary, `V41-B` settlement boundary, and `V41-C` observed implementation
frame before any alignment, runner, or downstream surface widening is released.

This slice establishes the first repo-native practical-analysis substrate for:

- deterministic repo-grounded compilation of intended architecture into the released
  `V40-A` root-family artifacts;
- exact consumption of the released `V41-A` analysis request boundary;
- exact consumption of the released `V41-B` settlement frame;
- exact consumption of the released `V41-C` observation frame;
- preservation of intended vs observed lane separation;
- fail-closed refusal to emit intended root artifacts when settlement entitlement
  remains blocked;
- explicit handling of unresolved or derived observed facts instead of silently
  laundering them into settled intended truth;
- committed intended-architecture reference fixtures over one bounded repo slice.

This slice remains deliberately prior to:

- `adeu_architecture_alignment_report@1`;
- CLI runner release;
- API or web inspection surfaces;
- remediation or repo-mutation planning;
- repo-grounded conformance, checkpoint-trace, oracle, projection, or UX artifact
  emission inside the practical loop.

Its job is to make intended architecture over a real repo deterministically
materializable before later slices compare intended and observed lanes or orchestrate
the full practical loop.

## Frozen Implementation Decisions

1. Active package strategy:
   - activate the practical intended-compile lane in
     `packages/adeu_architecture_compiler` for `vNext+86`;
   - `packages/adeu_architecture_ir` remains authoritative for the released `V40-A`
     root-family schemas and may not be silently redefined by compiler-local
     vocabulary.
2. Upstream consumption strategy:
   - `vNext+86` must consume one released `V41-A` analysis request, one released
     `V41-B` settlement frame, and one released `V41-C` observation frame, or exact
     validated derivatives thereof;
   - it may not bypass the released repo world with ambient working-tree reads,
     unbound file selection, free-floating prose, or an observation frame outside the
     released request/settlement boundary;
   - the intended compile entrypoint must bind back to the same:
     - `analysis_request_id`
     - `analysis_request_ref`
     - `settlement_frame_id`
     - `settlement_frame_ref`
     - `observation_frame_id`
     - `observation_frame_ref`
     - `source_set_hash`
     - `authority_boundary_policy`
     carried by the released upstream artifacts.
3. Existing root-family reuse strategy:
   - `vNext+86` releases no new schema family;
   - the only emitted artifact families in this slice are the already-released
     `V40-A` root-family artifacts:
     - `adeu_architecture_intent_packet@1`
     - `adeu_architecture_ontology_frame@1`
     - `adeu_architecture_boundary_graph@1`
     - `adeu_architecture_world_hypothesis@1`
     - `adeu_architecture_semantic_ir@1`
   - their authoritative schemas remain the released files under
     `packages/adeu_architecture_ir/schema/` mirrored under `spec/`, and v86 may not
     alter those schema bytes.
4. Intended-lane separation strategy:
   - the authoritative normative driver for intended compile in this slice is the
     released request boundary plus the released settlement frame;
   - the intended lane may consume the released observation frame as a companion
     input, but may not collapse intended and observed artifacts into one blended
     truth surface;
   - the observation frame may surface ambiguity, constrain overreach, force
     advisory posture, or trigger refusal, but it may not become the hidden source
     of intended architecture truth;
   - observed `direct` or `derived` facts may inform intended compile only through
     explicit intended claims or ambiguity handling, not by silent copying;
   - unresolved observed facts may not vanish silently; where they matter, they must
     remain explicit in the emitted root-family posture rather than becoming settled
     truth by omission.
5. Entitlement strategy:
   - lawful emission of intended root-family artifacts is possible only when the
     consumed settlement frame is `compile_entitlement = entitled`;
   - if the consumed settlement frame is `compile_entitlement = blocked` or carries
     non-empty blocking lineage, the intended compile entrypoint must fail closed and
     emit no authoritative root-family output in this slice;
   - the observation frame may still be consumed for validation of carry-through, but
     it may not be used to upgrade blocked settlement into entitled compile authority.
6. Root-family honesty strategy:
   - the emitted root-family artifacts remain meaning-only and may not embed
     alignment, remediation, runner, checkpoint, projection, or UX state;
   - the world-hypothesis artifact remains advisory, just as in released `V40-A`;
   - compiler provenance inside emitted `adeu_architecture_semantic_ir@1` remains
     limited to released root-family canonicalization provenance and may not smuggle
     in deferred practical-runner or alignment claims.
7. Canonicalization strategy:
   - emitted root-family artifacts must remain deterministically canonicalizable under
     the released `V40-A` profile;
   - deterministic fixture replay in this slice must reject lineage drift,
     settlement/observation drift, and root-family hash drift.
8. Path decomposition strategy:
   - `vNext+86` is the first concrete `V41-D` arc;
   - the broader `V41-D` planning path may later admit bounded practical reuse of the
     released checkpoint/oracle lane when ambiguity remains, but `vNext+86`
     intentionally defers that practical reuse and emits no repo-grounded
     checkpoint/oracle artifacts;
   - deterministic alignment, runner release, and practical-loop widening remain
     available only for later concrete `V41` arcs.

## Required Deliverables

1. New typed practical-analysis intended-compile surface:
   - extend `packages/adeu_architecture_compiler` with deterministic helpers that
     materialize repo-grounded intended `V40-A` root-family artifacts;
   - keep alignment, runner, conformance, checkpoint, projection, and UX practical
     outputs out of scope.
2. Canonical repo-grounded intended artifacts:
   - `adeu_architecture_intent_packet@1`
   - `adeu_architecture_ontology_frame@1`
   - `adeu_architecture_boundary_graph@1`
   - `adeu_architecture_world_hypothesis@1`
   - `adeu_architecture_semantic_ir@1`
3. Deterministic intended-compile entrypoints that:
   - consume one released `adeu_architecture_analysis_request@1`, one released
     `adeu_architecture_analysis_settlement_frame@1`, and one released
     `adeu_architecture_observation_frame@1`;
   - compile intended architecture over the same frozen repo `source_set` rather than
     a fresh ambient brief universe;
   - materialize the released `V40-A` root-family artifacts as exact validated
     derivatives;
   - fail closed when request lineage, settlement lineage, observation lineage,
     entitlement posture, or released root-family validation is invalid.
4. Root-family output strategy in this slice:
   - emitted artifacts must validate against the unchanged released `V40-A` schemas;
   - emitted `adeu_architecture_semantic_ir@1` must preserve the released required
     root sections:
     - `ontology`
     - `epistemics`
     - `deontics`
     - `utility`
   - any observation-driven unknown that matters to intended architecture may not be
     silently dropped; it must remain explicit as ambiguity, advisory hypothesis, or
     equivalent released root-family meaning posture.
5. Deterministic intended-compile laws that fail closed on at least:
   - any consumed settlement frame with `compile_entitlement = blocked`;
   - any non-empty upstream blocking lineage at compile time;
   - any attempt to recompute settlement entitlement locally rather than consuming the
     released `compile_entitlement` posture as-is from `V41-B`;
   - any request/settlement/observation drift against the released repo world;
   - any attempt to emit intended artifacts from observation provenance outside the
     released request boundary;
   - any attempt to smuggle observed implementation summaries into intended truth
     without released root-family meaning structure;
   - any attempt to embed alignment, remediation, runner, checkpoint, projection, or
     UX fields into emitted root-family artifacts.
6. Committed reference fixtures:
   - one accepted intended-compile fixture ladder under
     `apps/api/fixtures/architecture/vnext_plus86/` covering:
     - released request input
     - released settlement input
     - released observation input
     - canonical repo-grounded intended root-family outputs
   - the accepted fixture ladder must prove:
     - deterministic intended compile replay,
     - exact request/settlement/observation carry-through,
     - intended vs observed lane separation,
     - at least one unresolved or derived observation that materially affects intent
       remains visible in emitted posture as explicit ambiguity, advisory hypothesis,
       or fail-closed refusal to settle,
     - fail-closed refusal to emit when entitlement is blocked.
7. Python tests covering:
   - deterministic intended compile replay from the accepted fixture ladder;
   - exact request/settlement/observation consumption;
   - validation of emitted root-family outputs against the released `V40-A` schemas;
   - fail-closed blocked-settlement behavior;
   - rejection of silent unresolved-observation laundering into settled intended
     truth;
   - rejection of alignment/remediation/runner/checkpoint/projection creep.

## Hard Constraints

- `vNext+86` may not reopen or redefine the released `V40-A` root-family schema
  contract.
- `vNext+86` may not emit:
  - `adeu_architecture_alignment_report@1`,
  - CLI runner outputs,
  - API or web inspection routes,
  - remediation or repo-mutation plans,
  - repo-grounded conformance reports,
  - repo-grounded checkpoint traces,
  - repo-grounded oracle request/resolution artifacts,
  - repo-grounded projection bundle / manifest artifacts,
  - repo-grounded UX artifacts.
- `vNext+86` may not collapse observed and intended lanes into one blended artifact.
- `vNext+86` may not emit authoritative intended root-family output when consumed
  settlement entitlement is blocked.
- `vNext+86` may not emit shadow advisory intended artifacts under released
  root-family family names when consumed settlement entitlement is blocked.
- The formal Lean sidecar may mirror frozen finite law only:
  - it is not required for slice validity,
  - it may not silently redefine the released practical compile contract.

## PR Shape

- Single integrated PR.

Rationale:

- the intended-compile entrypoints, repo-grounded root-family fixture ladder, and
  fail-closed tests are tightly coupled and should land together so the first
  practical intended lane freezes as one coherent baseline.
