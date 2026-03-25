# Draft Next Arc Options v22

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v21.md`, updated after
`vNext+81` closeout.

This draft treats `V40-E` as closed on `main` at its bounded baseline and selects the
next concrete ASIR slice.

The next question is no longer whether the repo can lower released ASIR projection
lineage into one narrow UX target.

The next question is how to bind the released `V40-A` through `V40-E` ladder into one
truthful family-complete evidence and release posture without widening stop-gate
semantics or overclaiming deferred surfaces.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` is closed on `main` at its bounded baseline.
- `V40-B` is closed on `main` at its bounded baseline.
- `V40-C` is closed on `main` at its bounded baseline.
- `V40-D` is closed on `main` at its bounded baseline.
- `V40-E` is now closed on `main` at its bounded baseline.
- `vNext+81` is the current baseline implementation state.
- The released ASIR family substrate now includes:
  - canonical semantic-root artifacts and schema exports;
  - deterministic conformance and blocked/ready gating;
  - bounded hybrid checkpoint, oracle, and delta artifacts;
  - honest `adeu_core_ir@0.1` lowering through canonical projection bundle/manifest
    lineage;
  - first UX compatibility lowering into canonical `ux_domain_packet@1` only;
  - committed closeout evidence and stop-gate continuity for `vNext+77` through
    `vNext+81`.
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md` remains the active slice ladder for `V40`.

## Gap

The missing layer is no longer semantic-root release, deterministic conformance,
bounded hybrid disposition, core lowering, or the first typed UX packet compatibility
path.

The missing layer is a family-level release integration surface that can:

- consume the released closeout evidence, fixtures, and authoritative docs for
  `V40-A` through `V40-E` without redefining them;
- emit one canonical family evidence artifact that binds the shipped surfaces together
  by exact refs and hashes;
- keep released-vs-deferred surface posture explicit rather than leaving family
  completeness implicit in a trail of per-arc closeout notes;
- preserve stop-gate schema-family and metric-key continuity while integrating the
  first ASIR ladder into repo-native release evidence.

Today the repo still lacks a released way to:

- state, in one canonical artifact, exactly what `V40-A` through `V40-E` shipped and
  what remained deferred;
- bind the released family surfaces to exact evidence refs and hashes rather than to
  prose-only release claims;
- preserve the distinction between:
  - shipped `ux_domain_packet@1` compatibility, and
  - deferred `ux_morph_ir@1`, rendered-surface export, workbench routes, and formal
    sidecar integration;
- carry the resulting family through closeout evidence without overclaiming compiler,
  UX, or formal-sidecar authority.

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
  - `V40-E`
- Recommended decomposition reference:
  - `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V40-F`
- Recommended next concrete arc:
  - `vNext+82`
- Default path selection:
  - select `V40-F` as the next default candidate

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

### `V40-E`

Solved:

- deterministic lowering from released ASIR / `V40-D` projection lineage into the
  existing `ux_domain_packet@1` target family only;
- exact reuse of the released UX governance contract under `packages/adeu_core_ir`;
- explicit one-to-one binding from each emitted UX packet to one released ready
  `projection_id`;
- blocked/no-emit honesty for source projection units;
- review-driven hardening for payload-only lineage validation and governance reference
  closure.

## Recommended Next Path (`V40-F`)

Implement the ASIR family evidence and release integration baseline.

`V40-F` should introduce:

- one canonical family-level evidence artifact that binds the released `V40-A` through
  `V40-E` surfaces together by exact refs and hashes;
- authoritative and mirrored schema exports for that new family-evidence artifact with
  byte-for-byte parity after canonical export;
- explicit released-vs-deferred surface accounting for the first ASIR ladder;
- deterministic stop-gate continuity assertions over the completed family path set;
- family-complete release note posture that is still narrower than any future
  workbench, rendered-surface, or broader target-family release;
- no widening into new runtime behavior, new target families, or formal-sidecar
  authority.

## Why This Path

- It is the narrowest lawful next step after the released semantic, conformance,
  hybrid, core-lowering, and first-UX-compatibility lanes.
- It completes the family in the same order the decomposition already promised:
  meaning first, deterministic conformance second, bounded hybrid third, core lowering
  fourth, first UX lowering fifth, evidence/release integration sixth.
- It prevents the repo from treating a sequence of per-arc closeout notes as if that
  were already a canonical family-release surface.
- It keeps the next slice comparable to earlier ADEU evidence-integration baselines
  instead of mixing release integration with new target-family or workbench work.

## First-Slice Boundary (`V40-F`)

`V40-F` should stay bounded to:

- the existing released `V40-A` through `V40-E` surfaces only;
- family-level evidence input and release-summary integration only;
- exact per-path evidence closure for `V40-A` through `V40-E`, not a loose list of
  family references;
- stop-gate continuity assertions and exact metric-key equality only;
- the exact `vNext+81` stop-gate artifact baseline as the continuity comparison target;
- explicit released-vs-deferred surface accounting only;
- committed release-evidence reference fixtures and validator tests only.

It should not attempt:

- new semantic-root, conformance, hybrid, projection, or UX target behavior;
- `ux_morph_ir@1` lowering;
- rendered-surface export or surface-compiler release;
- API or web human-review workbench routes;
- direct prompt-to-surface or direct prompt-to-code generation;
- promotion of the formal Lean sidecar into a required release authority surface.

## Follow-On Path After `V40-F`

After `V40-F`, the current `V40` family should be treated as complete at its bounded
baseline on `main`.

Any additional work should be justified either as:

1. exceptional `V40` hardening with explicit lock text; or
2. a fresh post-`V40` family selection.

The detailed decomposition for the current family still lives in:

- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`

## Planning Boundary

- no reopening of `V40-A` root-family semantics is authorized by this planning draft;
- no reopening of `V40-B` deterministic conformance semantics is authorized by this
  planning draft;
- no reopening of `V40-C` hybrid checkpoint semantics is authorized by this planning
  draft;
- no reopening of `V40-D` projection honesty semantics is authorized by this planning
  draft;
- no reopening of `V40-E` `ux_domain_packet@1` compatibility semantics is authorized by
  this planning draft;
- no `ux_morph_ir@1`, rendered-surface export, API/workbench route, or prompt-to-UI
  release is authorized by this planning draft;
- no formal Lean proof surface becomes authoritative over the family release posture by
  this planning draft;
- runtime-observability deltas remain informational only and may not by themselves
  change shipped/deferred surface status, alter stop-gate continuity, or block family
  evidence materialization;
- the formal sidecar may continue in parallel, but it is not a blocker for drafting or
  starting `V40-F`;
- no stop-gate schema-family fork or implicit metric-key expansion is authorized.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v21.md",
  "baseline_arc": "vNext+81",
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
    "V40-D",
    "V40-E"
  ],
  "default_next_arc_candidate": "V40-F",
  "default_next_concrete_arc_candidate": "vNext+82",
  "v40_default_arc_span": {
    "from": "vNext+82",
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
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS81.md`
- `docs/ASSESSMENT_vNEXT_PLUS81_EDGES.md`
