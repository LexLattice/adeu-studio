# Draft Stop-Gate Decision vNext+86

Status: proposed gate for `V41-D`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS86.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- deterministic intended-compile helpers land in
  `packages/adeu_architecture_compiler` without redefining the released `V40-A`
  root-family schemas;
- the compile entrypoint consumes the released `V41-A` request, `V41-B` settlement,
  and `V41-C` observation boundary exactly through:
  - `analysis_request_id`
  - `analysis_request_ref`
  - `settlement_frame_id`
  - `settlement_frame_ref`
  - `observation_frame_id`
  - `observation_frame_ref`
  - `source_set_hash`
  - `authority_boundary_policy`;
- the only emitted artifact families in this slice are the already-released
  `V40-A` root-family artifacts:
  - `adeu_architecture_intent_packet@1`
  - `adeu_architecture_ontology_frame@1`
  - `adeu_architecture_boundary_graph@1`
  - `adeu_architecture_world_hypothesis@1`
  - `adeu_architecture_semantic_ir@1`;
- emitted root-family outputs validate against the unchanged released
  `packages/adeu_architecture_ir/schema/` and `spec/` schema surface;
- intended compile runs over the same frozen repo `source_set` consumed by request,
  settlement, and observation rather than a fresh ambient brief universe;
- the released request boundary plus released settlement frame remain the normative
  driver for intended compile; the observation frame may constrain, block, or force
  ambiguity/advisory posture, but may not become the hidden source of intended
  truth;
- lawful emission of intended root-family outputs requires
  released `compile_entitlement = entitled` consumed as-is from the settlement
  frame;
- blocked settlement or non-empty blocking lineage fails closed and emits no
  authoritative intended root-family output;
- blocked settlement may not emit shadow advisory intended artifacts under the same
  released root-family family names;
- observed facts may inform intended compile only through explicit released
  root-family meaning structure and may not be silently copied in as settled truth;
- any observation-driven unknown that matters to intended architecture remains
  explicit as ambiguity or advisory root-family posture rather than disappearing;
- emitted root-family artifacts remain free of:
  - alignment verdicts,
  - remediation plans,
  - runner state,
  - checkpoint state,
  - projection state,
  - UX state;
- one committed fixture ladder under
  `apps/api/fixtures/architecture/vnext_plus86/` proves deterministic repo-grounded
  intended compile replay over one bounded repo slice;
- Python tests cover:
  - deterministic intended compile replay,
  - exact request/settlement/observation consumption,
  - validation against released `V40-A` schemas,
  - fail-closed blocked-settlement behavior,
  - fixture-visible carry-through of at least one unresolved or derived observation
    into explicit ambiguity, advisory hypothesis, or refusal-to-settle posture,
  - rejection of unresolved-observation laundering,
  - rejection of alignment/remediation/runner/checkpoint/projection creep.

## Do Not Accept If

- the slice redefines released `V40-A` root-family schemas or bytes;
- the compile entrypoint reads ambient repo state outside the released request world;
- the compile entrypoint consumes settlement or observation artifacts outside the
  released request boundary;
- blocked settlement posture is upgraded into emitted intended output;
- settlement entitlement is recomputed locally instead of consumed from the released
  `V41-B` frame;
- observed implementation summaries are silently promoted into intended truth without
  released root-family meaning structure;
- unresolved observed facts disappear instead of remaining explicit in intended
  posture where they matter;
- the slice widens into alignment, runner, checkpoint, projection, or UX outputs;
- intended and observed lanes collapse into one artifact or one mixed truth surface.

## Local Gate

- run `make check`
