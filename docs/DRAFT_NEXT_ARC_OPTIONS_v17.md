# Draft Next Arc Options v17

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v16.md`, updated after
`vNext+76` closeout.

This draft treats the bounded `V39` family as complete on `main` and selects the next
ADEU-governed implementation family.

The next question is no longer how to widen the synthetic pressure-mismatch lane.

The next question is how to turn the ASIR architecture constitution into a repo-sized,
docs-first implementation family without collapsing the whole subsystem into one oversized
first lock.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `vNext+76` is the current baseline implementation state.
- The bounded hybrid checkpoint and oracle-adjudication lane is now released for the
  synthetic pressure-mismatch family at its intentionally narrow baseline.
- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md` now defines the proposed ASIR module
  constitution.
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md` now compiles that architecture constitution
  into a repo-sized `V40` slice ladder.
- `V40` path labels are planning-level seams and may decompose into multiple concrete
  `vNext+` arcs before a path is considered complete.

## Gap

The missing layer is no longer a bounded hybrid lane or a bounded conformance family.

The missing layer is an implementation family that can make architecture intent itself
typed, validated, and progressively lowerable before codegen.

Today the repo still lacks a released way to:

- normalize architecture briefs into a canonical typed intent packet;
- assemble a canonical architecture semantic root separated cleanly from downstream
  projection and conformance state;
- run section-local plus whole-ASIR integrity passes over architecture meaning;
- expose bounded ambiguity handling as an architecture-native lane;
- lower architecture semantics into `adeu_core_ir` and then later into the existing UX
  IR/compiler family;
- carry the resulting family through closeout evidence without overclaiming compiler or UI
  capability too early.

## Recommended Family

- Family name: `V40`
- Family theme: architecture semantic IR and architecture-intent compilation
- Closed prior family:
  - `V39-A`
  - `V39-B`
  - `V39-C`
  - `V39-D`
  - `V39-E`
- Recommended decomposition reference:
  - `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V40-A`
- Recommended next concrete arc:
  - `vNext+77`
- Default path selection:
  - select `V40-A` as the next default candidate

## Closed Earlier Paths

### `V39-A`

Solved:

- imported single-PR lane classification;
- code-alignment vs meta-sequence separation;
- truthful scope recording;
- pinned policy provenance for deterministic replay.

### `V39-B`

Solved:

- canonical pressure-mismatch rule registry;
- bounded vocabularies and counterexample policy;
- anti-authorship and anti-score registry boundaries.

### `V39-C`

Solved:

- canonical observation packet and conformance report substrate;
- deterministic-local detector execution only;
- fail-closed observed-finding handling.

### `V39-D`

Solved:

- canonical advisory fix-plan substrate;
- exact source-finding binding;
- role-separated forward-agent and post-optimizer projection;
- candidate-only safe-autofix planning.

### `V39-E`

Solved:

- canonical oracle request, oracle resolution, and checkpoint trace artifacts;
- bounded hybrid checkpoint classification and deterministic final adjudication;
- replay identity, one-round oracle rule, and fail-closed contradictory-resolution
  handling.

## Recommended Next Path (`V40-A`)

Implement the ASIR semantic-root and schema baseline.

`V40-A` should introduce:

- canonical `adeu_architecture_intent_packet@1`;
- canonical `adeu_architecture_ontology_frame@1`;
- canonical `adeu_architecture_boundary_graph@1`;
- canonical `adeu_architecture_world_hypothesis@1`;
- canonical `adeu_architecture_semantic_ir@1`;
- authoritative and mirrored schema exports;
- deterministic canonicalization and hashing rules;
- one committed reference fixture set;
- explicit root/sibling separation:
  - no projection state in the semantic root,
  - no checkpoint-trace state in the semantic root,
  - no conformance summary in the semantic root.

## Why This Path

- It is the narrowest lawful first consumer of the ASIR architecture doc.
- It preserves the docs-first ADEU pattern: constitution first, then decomposition, then
  a bounded first lock.
- It keeps the first slice comparable in size to earlier ADEU family baselines instead of
  turning ASIR into a one-shot subsystem rollout.
- It avoids forcing hybrid, lowering, UX compatibility, and evidence integration into the
  same first implementation arc.
- It keeps the Lean formal lane visible but non-blocking until frozen finite laws are
  actually ready to be promoted.

## First-Slice Boundary (`V40-A`)

`V40-A` should stay bounded to:

- the semantic root artifact family only;
- canonicalization, hashing, and schema export only;
- committed reference fixtures and validator tests only;
- proof-mirror sidecar work only where it mirrors already-frozen finite vocabularies and
  does not become a blocking dependency.

It should not attempt:

- deterministic compiler pass release;
- hybrid checkpoint/oracle execution;
- `adeu_core_ir` lowering;
- UX lowering;
- API or web workbench routes;
- generic architecture code generation;
- in-place upgrade or widening of the existing `packages/adeu_lean` lane.

## Follow-On Paths Inside `V40`

The recommended family ladder after `V40-A` is:

1. `V40-A`
   - semantic root and schema baseline
2. `V40-B`
   - deterministic assembly and whole-ASIR integrity baseline
3. `V40-C`
   - bounded hybrid ambiguity baseline
4. `V40-D`
   - `adeu_core_ir` lowering baseline
5. `V40-E`
   - first UX lowering baseline
6. `V40-F`
   - evidence and release integration baseline

`V40-E` remains compatible-later and non-blocking for first-family validity.

The detailed decomposition for that ladder lives in:

- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`

## Planning Boundary

- no implicit API or web release is authorized by this planning draft;
- no direct brief-to-code path is authorized by this planning draft;
- no formal Lean proof surface becomes authoritative over the main compiler by this
  planning draft;
- no stop-gate schema-family fork or implicit metric-key expansion is authorized;
- no widening of the closed `V39` family is authorized in place.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v16.md",
  "baseline_arc": "vNext+76",
  "closed_path_family": "V39",
  "closed_paths": [
    "V39-A",
    "V39-B",
    "V39-C",
    "V39-D",
    "V39-E"
  ],
  "next_path_family": "V40",
  "default_next_arc_candidate": "V40-A",
  "default_next_concrete_arc_candidate": "vNext+77",
  "v40_default_arc_span": {
    "from": "vNext+77",
    "to": "vNext+84"
  },
  "v40_paths_may_span_multiple_arcs": true,
  "family_decomposition_doc": "docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md",
  "formal_kernel_mode": "sidecar_only_until_explicitly_promoted",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "no_implicit_metric_key_expansion": true
}
```

## Governing References

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS76.md`
- `docs/ASSESSMENT_vNEXT_PLUS76_EDGES.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
