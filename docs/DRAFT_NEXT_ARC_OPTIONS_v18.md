# Draft Next Arc Options v18

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v17.md`, updated after
`vNext+77` closeout.

This draft treats `V40-A` as closed on `main` at its bounded baseline and selects the
next concrete ASIR slice.

The next question is no longer whether the repo needs a canonical architecture
semantic-root substrate.

The next question is how to make that released root family deterministically
assemblable, integrity-checkable, and explicitly gateable before hybrid or lowering
surfaces are introduced.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` is now closed on `main` at its bounded baseline.
- `vNext+77` is the current baseline implementation state.
- The released ASIR root-family substrate now includes:
  - canonical `adeu_architecture_intent_packet@1`
  - canonical `adeu_architecture_ontology_frame@1`
  - canonical `adeu_architecture_boundary_graph@1`
  - canonical `adeu_architecture_world_hypothesis@1`
  - canonical `adeu_architecture_semantic_ir@1`
  - authoritative and mirrored schema exports
  - deterministic canonicalization and semantic-hash replay
  - committed reference fixtures and fail-closed root-local validation
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md` remains the active slice ladder for `V40`.

## Gap

The missing layer is no longer the semantic-root artifact family itself.

The missing layer is a deterministic compiler surface that can:

- consume the released ASIR root family without redefining it;
- run section-local plus whole-ASIR integrity passes;
- emit a first-class `adeu_architecture_conformance_report@1`;
- expose stable check ids and pre-projection blocked/ready gating;
- keep conformance state explicitly downstream of the released semantic root.

Today the repo still lacks a released way to:

- activate `packages/adeu_architecture_compiler` lawfully;
- assemble a deterministic validation context from released root artifacts;
- emit stable `ASIR-O`, `ASIR-E`, `ASIR-D`, `ASIR-U`, and pre-projection `ASIR-P`
  findings;
- report blocked vs ready state without silently widening into checkpoint traces or
  projection manifests.

## Recommended Family

- Family name: `V40`
- Family theme: architecture semantic IR and architecture-intent compilation
- Closed prior family:
  - `V39-A`
  - `V39-B`
  - `V39-C`
  - `V39-D`
  - `V39-E`
- Closed current-family path:
  - `V40-A`
- Recommended decomposition reference:
  - `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V40-B`
- Recommended next concrete arc:
  - `vNext+78`
- Default path selection:
  - select `V40-B` as the next default candidate

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

### `V40-A`

Solved:

- canonical ASIR root-family artifacts and schema exports;
- deterministic semantic-hash replay and canonical set normalization;
- root/sibling separation at the semantic-root boundary;
- advisory-only world-hypothesis posture;
- lightweight root-local reference closure and accepted-hypothesis alignment.

## Recommended Next Path (`V40-B`)

Implement the ASIR deterministic assembly, integrity, and conformance baseline.

`V40-B` should introduce:

- `packages/adeu_architecture_compiler` as the first lawful compiler package;
- deterministic entrypoints that consume released `V40-A` root-family artifacts;
- section-local validators for ontology, epistemics, deontics, and utility;
- whole-ASIR integrity checks across the assembled semantic root;
- canonical `adeu_architecture_conformance_report@1`;
- deterministic consumed-root lineage inside the conformance report;
- stable check-id families for deterministic findings;
- explicit `required` vs advisory check-result posture;
- static deterministic human-escalation lineage only, without checkpoint or hybrid
  artifact emission;
- slice-local `ASIR-P` checks for pre-projection readiness honesty only;
- explicit pre-projection `blocked` vs `ready` gating.

## Why This Path

- It is the narrowest lawful next consumer of the released `V40-A` substrate.
- It preserves the ASIR separation:
  root meaning first, deterministic conformance second, hybrid third, lowering later.
- It activates the compiler package only where the decomposition already said it should
  begin.
- It keeps the next slice comparable to earlier ADEU arc baselines instead of mixing
  deterministic validation, hybrid adjudication, and projection lowering together.
- It makes the next family step honest:
  the repo now has semantic root artifacts, but it still lacks a released deterministic
  architecture compiler lane.

## First-Slice Boundary (`V40-B`)

`V40-B` should stay bounded to:

- `packages/adeu_architecture_compiler` activation only;
- deterministic assembly and validation over released root-family artifacts only;
- `adeu_architecture_conformance_report@1` only;
- consumed-root replay lineage and static escalation lineage only;
- stable deterministic check ids and blocked/ready gating only;
- committed compiler-reference fixtures and validator tests only.

It should not attempt:

- checkpoint/oracle execution;
- `adeu_architecture_checkpoint_trace@1`;
- `adeu_architecture_oracle_request@1` or `adeu_architecture_oracle_resolution@1`;
- `adeu_architecture_projection_bundle@1` or
  `adeu_architecture_projection_manifest@1`;
- `adeu_core_ir` lowering;
- UX lowering;
- API or web workbench routes.

In this first `V40-B` slice, `ASIR-P-xxx` means only pre-projection readiness honesty,
blocked/ready correctness, and empty emitted-artifact posture. Projection-manifest or
bundle integrity remains deferred.

## Follow-On Paths Inside `V40`

The recommended family ladder after `V40-B` is:

1. `V40-B`
   - deterministic assembly and integrity baseline
2. `V40-C`
   - bounded hybrid ambiguity baseline
3. `V40-D`
   - `adeu_core_ir` lowering baseline
4. `V40-E`
   - first UX lowering baseline
5. `V40-F`
   - evidence and release integration baseline

`V40-E` remains compatible-later and non-blocking for first-family validity.

The detailed decomposition for that ladder lives in:

- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`

## Planning Boundary

- no implicit reopening of `V40-A` is authorized by this planning draft;
- no hybrid checkpoint/oracle release is authorized by this planning draft;
- no projection manifest or lowering release is authorized by this planning draft;
- no direct brief-to-code path is authorized by this planning draft;
- no formal Lean proof surface becomes authoritative over the main compiler by this
  planning draft;
- no stop-gate schema-family fork or implicit metric-key expansion is authorized.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v17.md",
  "baseline_arc": "vNext+77",
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
    "V40-A"
  ],
  "default_next_arc_candidate": "V40-B",
  "default_next_concrete_arc_candidate": "vNext+78",
  "v40_default_arc_span": {
    "from": "vNext+78",
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
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS77.md`
- `docs/ASSESSMENT_vNEXT_PLUS77_EDGES.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
