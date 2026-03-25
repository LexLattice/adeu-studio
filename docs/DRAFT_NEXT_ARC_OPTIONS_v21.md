# Draft Next Arc Options v21

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v20.md`, updated after
`vNext+80` closeout.

This draft treats `V40-D` as closed on `main` at its bounded baseline and selects the
next concrete ASIR slice.

The next question is no longer whether the repo needs a narrow downstream lowering into
shared integrity space.

The next question is how to introduce one narrow UX compatibility lowering that can
consume the released ASIR and `adeu_core_ir` projection lane without collapsing typed
IR lowering into direct surface generation.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` is closed on `main` at its bounded baseline.
- `V40-B` is closed on `main` at its bounded baseline.
- `V40-C` is closed on `main` at its bounded baseline.
- `V40-D` is now closed on `main` at its bounded baseline.
- `vNext+80` is the current baseline implementation state.
- The released ASIR lowering substrate now includes:
  - canonical `adeu_architecture_projection_bundle@1`
  - canonical `adeu_architecture_projection_manifest@1`
  - deterministic lowering into `adeu_core_ir@0.1` only
  - explicit projection-unit source refs, readiness, blocking refs, output refs, and
    compiler-entrypoint provenance
  - blocked-vs-ready lowering honesty over released conformance and checkpoint-trace
    lineage
  - authoritative and mirrored schema exports plus committed ready and blocked fixture
    ladders
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md` remains the active slice ladder for `V40`.

## Gap

The missing layer is no longer semantic-root release, deterministic architecture
conformance, bounded hybrid disposition, or one narrow lowering into shared integrity
space.

The missing layer is a narrow UX compatibility lowering surface that can:

- consume released `adeu_architecture_semantic_ir@1`,
  `adeu_architecture_conformance_report@1`,
  `adeu_architecture_checkpoint_trace@1`,
  `adeu_architecture_projection_bundle@1`, and
  `adeu_architecture_projection_manifest@1` without redefining them;
- emit canonical `ux_domain_packet@1` using the existing UX governance target family
  under `packages/adeu_core_ir`;
- preserve the frozen approved-profile and authority-boundary posture of the released
  UX lane;
- bind each emitted UX packet to exactly one released ready `projection_id` rather than
  to loose generic architecture lineage;
- remain explicitly prior to `ux_morph_ir@1`, UX surface compiler export, API/workbench
  widening, and direct prompt-to-surface generation.

Today the repo still lacks a released way to:

- lower released ASIR projection lineage into `ux_domain_packet@1` as an existing typed
  UX IR target;
- prove that the first UX target can be emitted without widening into React trees,
  surface compiler export, or workbench routes;
- demonstrate that blocked ASIR or blocked projection state cannot be misreported as a
  lawful UX packet output;
- keep the first emitted UX target bound one-to-one to released ready projection units
  rather than to looser generic architecture lineage;
- preserve the `V36` UX governance lane as a consumed target-family contract rather
  than silently recreating it inside the ASIR compiler lane.

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
  - `V40-D`
- Recommended decomposition reference:
  - `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V40-E`
- Recommended next concrete arc:
  - `vNext+81`
- Default path selection:
  - select `V40-E` as the next default candidate

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

### `V40-D`

Solved:

- canonical architecture projection bundle and projection manifest artifacts;
- deterministic lowering into `adeu_core_ir@0.1` only;
- explicit bundle/manifest source-lineage and emitted-artifact binding;
- blocked-vs-ready projection honesty over released conformance and checkpoint lineage;
- review-driven hardening for exact emitted core-ir metadata binding and manifest
  blocker/readiness consistency.

## Recommended Next Path (`V40-E`)

Implement the first ASIR UX compatibility baseline into `ux_domain_packet@1`.

`V40-E` should introduce:

- deterministic lowering from released ASIR / `V40-D` projection lineage into the
  existing `ux_domain_packet@1` target family only;
- explicit reuse of the released UX governance schema family under
  `packages/adeu_core_ir` rather than a new parallel UX schema surface;
- approved-profile, authority-boundary, and reference-surface compatibility checks
  against the existing UX governance lane;
- emitted UX packet lineage that stays inspectable through the released architecture
  projection bundle/manifest relation and binds exactly one emitted packet to exactly
  one released ready `projection_id`;
- fail-closed guards that prevent blocked architecture/projection state from being
  misreported as a lawful emitted UX packet;
- no widening into `ux_morph_ir@1`, surface compiler export, API/workbench routes, or
  direct React tree generation.

## Why This Path

- It is the narrowest lawful next consumer of the released semantic, conformance,
  hybrid, and lowering lanes.
- It preserves the ASIR order:
  meaning first, deterministic conformance second, bounded hybrid third, core lowering
  fourth, first UX compatibility fifth.
- It reuses the existing UX governance family rather than silently forking it inside the
  architecture compiler.
- It keeps the next slice comparable to earlier ADEU arc baselines instead of mixing
  UX packet compatibility, morph IR, compiler export, and workbench release together.
- It keeps the formal sidecar parallel and non-blocking while the main repo freezes the
  next concrete UX target boundary.

## First-Slice Boundary (`V40-E`)

`V40-E` should stay bounded to:

- the existing `packages/adeu_architecture_compiler` lowering surface;
- the existing released `ux_domain_packet@1` target-family schema under
  `packages/adeu_core_ir`;
- released `V40-A` semantic-root, `V40-B` conformance, `V40-C` checkpoint-trace, and
  `V40-D` projection bundle/manifest inputs only;
- one-to-one ready-projection-unit to emitted-UX-packet binding only;
- approved-profile and authority-boundary compatibility checks only;
- committed UX-lowering reference fixtures and validator tests only.

It should not attempt:

- `ux_morph_ir@1` lowering in the first concrete `V40-E` arc;
- surface compiler export or rendered-surface release;
- API or web human-review workbench routes;
- direct prompt-to-code or prompt-to-UI generation;
- family-complete evidence/stop-gate wiring, which remains later `V40-F` scope.

## Follow-On Paths Inside `V40`

The recommended family ladder after `V40-E` is:

1. `V40-E`
   - first UX lowering baseline
2. `V40-F`
   - evidence and release integration baseline

`V40-E` remains compatible-later and non-blocking for first-family validity even though
it is the next default candidate after `V40-D`.

The detailed decomposition for that ladder lives in:

- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`

## Planning Boundary

- no reopening of `V40-A` root-family semantics is authorized by this planning draft;
- no reopening of `V40-B` deterministic conformance semantics is authorized by this
  planning draft;
- no reopening of `V40-C` hybrid checkpoint semantics is authorized by this planning
  draft;
- no reopening of `V40-D` `adeu_core_ir` lowering honesty semantics is authorized by
  this planning draft;
- no `ux_morph_ir@1` lowering is authorized by this planning draft;
- no surface compiler export, API, or web workbench release is authorized by this
  planning draft;
- no direct prompt-to-surface or direct prompt-to-code generation is authorized by this
  planning draft;
- no formal Lean proof surface becomes authoritative over the main UX-lowering lane by
  this planning draft;
- the formal sidecar may continue in parallel, but it is not a blocker for drafting or
  starting `V40-E`;
- no stop-gate schema-family fork or implicit metric-key expansion is authorized.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v20.md",
  "baseline_arc": "vNext+80",
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
    "V40-C",
    "V40-D"
  ],
  "default_next_arc_candidate": "V40-E",
  "default_next_concrete_arc_candidate": "vNext+81",
  "first_ux_target_candidate": "ux_domain_packet@1",
  "deferred_follow_on_ux_target": "ux_morph_ir@1",
  "v40_default_arc_span": {
    "from": "vNext+81",
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
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS80.md`
- `docs/ASSESSMENT_vNEXT_PLUS80_EDGES.md`
