# Draft Next Arc Options v19

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v18.md`, updated after
`vNext+78` closeout.

This draft treats `V40-B` as closed on `main` at its bounded baseline and selects the
next concrete ASIR slice.

The next question is no longer whether the repo needs a deterministic architecture
compiler surface.

The next question is how to introduce a bounded hybrid ambiguity lane that consumes the
released semantic-root and conformance surfaces without collapsing advisory oracle
output, deterministic adjudication, and downstream lowering into one step.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` is closed on `main` at its bounded baseline.
- `V40-B` is now closed on `main` at its bounded baseline.
- `vNext+78` is the current baseline implementation state.
- The released ASIR deterministic compiler substrate now includes:
  - active `packages/adeu_architecture_compiler`
  - canonical `adeu_architecture_conformance_report@1`
  - deterministic consumed-root lineage
  - section-local and whole-ASIR integrity validation
  - stable deterministic `ASIR-O`, `ASIR-E`, `ASIR-D`, `ASIR-U`, and bounded `ASIR-P`
    findings
  - explicit `blocked` vs `ready` gating
  - committed reference fixtures and fail-closed report validation
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md` remains the active slice ladder for `V40`.

## Gap

The missing layer is no longer deterministic ASIR assembly or compile-readiness
reporting.

The missing layer is a bounded hybrid ambiguity surface that can:

- consume released `adeu_architecture_semantic_ir@1` and
  `adeu_architecture_conformance_report@1` without redefining them;
- classify architecture ambiguity into exact checkpoint classes;
- emit first-class `adeu_architecture_oracle_request@1`,
  `adeu_architecture_oracle_resolution@1`,
  `adeu_architecture_checkpoint_trace@1`, and
  `adeu_architecture_ir_delta@1`;
- preserve the `v76` law that oracle output is advisory-only while final adjudication
  remains deterministic;
- pin replay identity exactly and fail closed on contradiction or replay mismatch;
- remain prior to projection manifests, lowering, and workbench release.

Today the repo still lacks a released way to:

- emit canonical architecture-hybrid checkpoints from released ASIR surfaces;
- carry one-round oracle request / resolution state under exact replay identity;
- record deterministic final adjudication as `resolved_pass`, `resolved_fail`, or
  `escalated_human`;
- express bounded repair proposals through `adeu_architecture_ir_delta@1` without
  letting them become direct repo mutation or scope-widening payloads.

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
- Recommended decomposition reference:
  - `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V40-C`
- Recommended next concrete arc:
  - `vNext+79`
- Default path selection:
  - select `V40-C` as the next default candidate

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

### `V40-B`

Solved:

- canonical deterministic ASIR compiler substrate under
  `packages/adeu_architecture_compiler`;
- canonical `adeu_architecture_conformance_report@1`;
- deterministic consumed-root replay lineage and compiler-profile provenance;
- section-local plus whole-ASIR integrity validation;
- stable deterministic `ASIR-O`, `ASIR-E`, `ASIR-D`, `ASIR-U`, and bounded `ASIR-P`
  findings;
- explicit `required` vs advisory check-result posture;
- blocked/ready gating that stays separate from checkpoint adjudication;
- static deterministic human-escalation lineage only;
- review-driven fail-closed hardening for config-hash coverage, exact required-check
  profile matching, and honest ready-fixture posture.

## Recommended Next Path (`V40-C`)

Implement the ASIR bounded hybrid ambiguity baseline.

`V40-C` should introduce:

- canonical `adeu_architecture_oracle_request@1`;
- canonical `adeu_architecture_oracle_resolution@1`;
- canonical `adeu_architecture_checkpoint_trace@1`;
- canonical `adeu_architecture_ir_delta@1`;
- deterministic checkpoint classification over released ASIR ambiguity and conformance
  surfaces;
- frozen `resolution_route -> checkpoint_class` law and exact
  `resolution_state -> final_adjudication` law;
- exact replay identity and one-round oracle request / resolution law;
- deterministic final adjudication under the exact `v76` transition table;
- advisory-only oracle output with fail-closed contradiction and replay-mismatch
  handling;
- bounded repair-delta law that remains proposal-only until deterministic revalidation;
- explicit preservation of `V40-B` deterministic authority:
  failed required checks remain deterministic failures, not oracle-repair entrypoints.

## Why This Path

- It is the narrowest lawful next consumer of the released deterministic compiler lane.
- It preserves the ASIR separation:
  semantic root first, deterministic conformance second, bounded hybrid third, lowering
  later.
- It reuses the repo’s already accepted `v76` hybrid law rather than inventing a new
  mixed-confidence regime.
- It keeps the next slice comparable to earlier ADEU arc baselines instead of mixing
  hybrid adjudication, projection manifests, and lowerings together.
- It closes the remaining semantic gap before `adeu_core_ir` lowering:
  the repo can now say whether architecture intent is blocked, but not yet trace how
  bounded ambiguity is resolved.

## First-Slice Boundary (`V40-C`)

`V40-C` should stay bounded to:

- the existing `packages/adeu_architecture_compiler` package surface only;
- hybrid schemas, exports, builders, validators, and fixtures only;
- deterministic checkpoint classification over released ASIR inputs only;
- one-round oracle request / resolution handling only;
- canonical checkpoint traces and bounded repair-delta artifacts only;
- frozen route/class and resolution/adjudication tables only;
- fail-closed replay identity, contradiction, and authority-boundary enforcement only.

It should not attempt:

- projection bundle or projection manifest release;
- `adeu_core_ir` lowering;
- UX lowering;
- API or web human-review workbench routes;
- direct repo mutation or patch-payload emission;
- multi-round oracle loops.

## Follow-On Paths Inside `V40`

The recommended family ladder after `V40-C` is:

1. `V40-C`
   - bounded hybrid ambiguity baseline
2. `V40-D`
   - `adeu_core_ir` lowering baseline
3. `V40-E`
   - first UX lowering baseline
4. `V40-F`
   - evidence and release integration baseline

`V40-E` remains compatible-later and non-blocking for first-family validity.

The detailed decomposition for that ladder lives in:

- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`

## Planning Boundary

- no reopening of `V40-A` root-family semantics is authorized by this planning draft;
- no reopening of `V40-B` deterministic conformance semantics is authorized by this
  planning draft;
- no projection bundle, projection manifest, or lowering release is authorized by this
  planning draft;
- no API or web workbench release is authorized by this planning draft;
- no direct repo mutation or patch artifact emission is authorized by this planning
  draft;
- no formal Lean proof surface becomes authoritative over the main hybrid lane by this
  planning draft;
- no stop-gate schema-family fork or implicit metric-key expansion is authorized.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v18.md",
  "baseline_arc": "vNext+78",
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
    "V40-B"
  ],
  "default_next_arc_candidate": "V40-C",
  "default_next_concrete_arc_candidate": "vNext+79",
  "v40_default_arc_span": {
    "from": "vNext+79",
    "to": "vNext+85"
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
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS78.md`
- `docs/ASSESSMENT_vNEXT_PLUS78_EDGES.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
