# Draft Next Arc Options v20

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v19.md`, updated after
`vNext+79` closeout.

This draft treats `V40-C` as closed on `main` at its bounded baseline and selects the
next concrete ASIR slice.

The next question is no longer whether the repo needs a bounded hybrid ambiguity lane.

The next question is how to introduce one narrow downstream lowering into shared
integrity space without collapsing semantic meaning, deterministic conformance, hybrid
disposition, projection honesty, and UX work into one step.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` is closed on `main` at its bounded baseline.
- `V40-B` is closed on `main` at its bounded baseline.
- `V40-C` is now closed on `main` at its bounded baseline.
- `vNext+79` is the current baseline implementation state.
- The released ASIR hybrid substrate now includes:
  - canonical `adeu_architecture_oracle_request@1`
  - canonical `adeu_architecture_oracle_resolution@1`
  - canonical `adeu_architecture_checkpoint_trace@1`
  - canonical `adeu_architecture_ir_delta@1`
  - exact `resolution_route -> checkpoint_class` and
    `resolution_state -> final_adjudication` law
  - exact replay identity and one-round oracle handling
  - advisory-only oracle boundaries and proposal-only delta posture
  - explicit preservation of `V40-B` deterministic authority
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md` remains the active slice ladder for `V40`.

## Gap

The missing layer is no longer semantic-root release, deterministic architecture
conformance, or bounded hybrid disposition.

The missing layer is a narrow deterministic lowering surface that can:

- consume released `adeu_architecture_semantic_ir@1`,
  `adeu_architecture_conformance_report@1`, and
  `adeu_architecture_checkpoint_trace@1` without redefining them;
- emit canonical `adeu_architecture_projection_bundle@1` and
  `adeu_architecture_projection_manifest@1`;
- lower ASIR into `adeu_core_ir@0.1` only;
- keep manifest lineage and blocked-vs-ready projection honesty inspectable;
- remain explicitly prior to UX lowering, API/workbench widening, and broader target
  families.

Today the repo still lacks a released way to:

- lower released ASIR meaning, conformance, and checkpoint disposition into
  `adeu_core_ir@0.1`;
- make the lowering relation inspectable through first-class bundle and manifest
  artifacts;
- prove that blocked ambiguity and checkpoint state honestly govern whether projection
  units may claim readiness;
- keep `adeu_core_ir` lowering narrow enough that it does not silently become a UX or
  application-generation lane.

## Recommended Family

- Family name: `V40`
- Family theme: architecture semantic IR and architecture-intent compilation
- Closed prior family:
  - `V39-A`
  - `V39-B`
  - `V39-C`
  - `V39-D`
  - `V39-E`
- Closed current-family paths:
  - `V40-A`
  - `V40-B`
  - `V40-C`
- Recommended decomposition reference:
  - `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V40-D`
- Recommended next concrete arc:
  - `vNext+80`
- Default path selection:
  - select `V40-D` as the next default candidate

## Closed Earlier Paths

### `V39`

Solved:

- imported single-PR lane classification and truthful scope recording;
- canonical observation, conformance, advisory fix-plan, and hybrid checkpoint
  substrates;
- replay identity, bounded oracle law, and fail-closed contradictory-resolution
  handling.

### `V40-A`

Solved:

- canonical ASIR root-family artifacts and schema exports;
- deterministic semantic-hash replay and canonical set normalization;
- root/sibling separation at the semantic-root boundary;
- advisory-only world-hypothesis posture;
- lightweight root-local reference closure and accepted-hypothesis alignment.

### `V40-B`

Solved:

- canonical deterministic ASIR compiler substrate under
  `packages/adeu_architecture_compiler`;
- canonical `adeu_architecture_conformance_report@1`;
- deterministic consumed-root replay lineage and compiler-profile provenance;
- section-local plus whole-ASIR integrity validation;
- explicit `required` vs advisory check-result posture;
- blocked/ready gating that stays separate from checkpoint adjudication.

### `V40-C`

Solved:

- canonical architecture hybrid request, resolution, checkpoint trace, and proposal
  delta artifacts;
- exact checkpoint classifier and adjudication law under the borrowed `v76` precedent;
- one-round replay identity and fail-closed contradiction/replay-mismatch handling;
- explicit preservation of `V40-B` deterministic authority and static escalation
  lineage;
- merged review hardening for resolution evidence requirements and fail-closed
  escalation triggers.

## Recommended Next Path (`V40-D`)

Implement the ASIR core lowering baseline into `adeu_core_ir@0.1`.

`V40-D` should introduce:

- canonical `adeu_architecture_projection_bundle@1`;
- canonical `adeu_architecture_projection_manifest@1`;
- deterministic lowering from released ASIR surfaces into `adeu_core_ir@0.1` only;
- projection-unit structure that makes source refs, readiness, blocking refs, emitted
  artifacts, and compiler entrypoint explicit;
- manifest lineage that makes the lowering relation inspectable and honest;
- fail-closed blocked-vs-ready projection honesty over released conformance and
  checkpoint-trace state;
- no widening into UX lowerings, API/workbench routes, or generic app generation.

## Why This Path

- It is the narrowest lawful next consumer of the released semantic, conformance, and
  hybrid lanes.
- It preserves the ASIR order:
  meaning first, deterministic conformance second, bounded hybrid third, core lowering
  fourth.
- It takes the architecture doc’s minimal `v1` target-family claim seriously:
  `adeu_core_ir` first, UX later.
- It gives the repo one inspectable projection relation before any wider target-family
  or workbench ambitions begin.
- It keeps the next slice comparable to earlier ADEU arc baselines instead of mixing
  projection honesty, UX lowering, and release integration together.

## First-Slice Boundary (`V40-D`)

`V40-D` should stay bounded to:

- the existing `packages/adeu_architecture_compiler` package surface only;
- `adeu_architecture_projection_bundle@1` and
  `adeu_architecture_projection_manifest@1` only;
- lowering into `adeu_core_ir@0.1` only;
- released `V40-A` semantic-root, `V40-B` conformance, and `V40-C` checkpoint-trace
  inputs only;
- projection-unit readiness/blocking honesty and manifest-lineage checks only;
- committed lowering-reference fixtures and validator tests only.

It should not attempt:

- `ux_domain_packet@1` or `ux_morph_ir@1` lowering;
- API or web human-review workbench routes;
- direct prompt-to-code or prompt-to-UI generation;
- broader target-family release beyond `adeu_core_ir@0.1`;
- evidence/stop-gate family-complete wiring, which belongs later in `V40-F`.

## Follow-On Paths Inside `V40`

The recommended family ladder after `V40-D` is:

1. `V40-D`
   - `adeu_core_ir` lowering baseline
2. `V40-E`
   - first UX lowering baseline
3. `V40-F`
   - evidence and release integration baseline

`V40-E` remains compatible-later and non-blocking for first-family validity.

The detailed decomposition for that ladder lives in:

- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`

## Planning Boundary

- no reopening of `V40-A` root-family semantics is authorized by this planning draft;
- no reopening of `V40-B` deterministic conformance semantics is authorized by this
  planning draft;
- no reopening of `V40-C` hybrid checkpoint semantics is authorized by this planning
  draft;
- no UX lowering is authorized by this planning draft;
- no API or web workbench release is authorized by this planning draft;
- no direct repo mutation or patch artifact emission is authorized by this planning
  draft;
- no formal Lean proof surface becomes authoritative over the main lowering lane by
  this planning draft;
- the formal sidecar may continue in parallel, but it is not a blocker for drafting or
  starting `V40-D`;
- no stop-gate schema-family fork or implicit metric-key expansion is authorized.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v19.md",
  "baseline_arc": "vNext+79",
  "closed_prior_family": "V39",
  "closed_prior_paths": [
    "V39-A",
    "V39-B",
    "V39-C",
    "V39-D",
    "V39-E"
  ],
  "current_family": "V40",
  "closed_current_family_paths": [
    "V40-A",
    "V40-B",
    "V40-C"
  ],
  "default_next_arc_candidate": "V40-D",
  "default_next_concrete_arc_candidate": "vNext+80",
  "v40_default_arc_span": {
    "from": "vNext+80",
    "to": "vNext+86"
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
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS79.md`
- `docs/ASSESSMENT_vNEXT_PLUS79_EDGES.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
