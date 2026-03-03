# Assessment vNext+42 Edges (V32-E Planning)

This document records pre-implementation edge analysis for `vNext+42` (`V32-E` CI gate + closeout evidence wiring), aligned to `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`.

Status: active planning assessment (pre-implementation, March 4, 2026 UTC).

## Scope

- In scope: deterministic CI/docs wiring for semantic-compiler closeout evidence, deterministic lint/guard behavior, and stop-gate keyset continuity preservation.
- Out of scope: semantic-source/parser evolution (`V32-B`), compiler-core evolution (`V32-C`), surface-governance contract evolution (`V32-D`), stop-gate metric-key expansion (`V32-F`), runtime/provider/proposer boundary changes.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS41.md`
- `artifacts/semantic_compiler/v41/surface_snapshot.json`
- `artifacts/semantic_compiler/v41/surface_diff.json`
- `artifacts/semantic_compiler/v41/evidence_manifest.json`
- `docs/generated/semantic_compiler/v41/PR_SPLITS.md`
- `artifacts/quality_dashboard_v41_closeout.json`
- `artifacts/stop_gate/metrics_v41_closeout.json`
- `apps/api/scripts/lint_closeout_consistency.py`
- `.github/workflows/ci.yml`

## Repository Baseline Anchors

1. v41 surface-governance/codegen outputs already exist and are deterministic:
   - `artifacts/semantic_compiler/v41/surface_snapshot.json`
   - `artifacts/semantic_compiler/v41/surface_diff.json`
   - `artifacts/semantic_compiler/v41/evidence_manifest.json`
   - `docs/generated/semantic_compiler/v41/PR_SPLITS.md`
2. v41 closeout artifacts already exist and are green:
   - `artifacts/quality_dashboard_v41_closeout.json`
   - `artifacts/stop_gate/metrics_v41_closeout.json`
   - `artifacts/stop_gate/report_v41_closeout.md`
3. Stop-gate continuity baseline is active:
   - schema family `stop_gate_metrics@1`
   - derived metric-key cardinality `79`
4. v36/v37/v38/v39/v40/v41 continuity contracts are active and must remain green.

## V32-E Edge Set

1. CI coverage drift:
   - required semantic-compiler closeout checks can be silently dropped by workflow edits.
2. Entry-point ambiguity:
   - multiple ad-hoc scripts can diverge on closeout validation semantics.
3. Closeout-doc block omission:
   - required machine-checkable evidence blocks can be missing while docs still render.
4. Artifact existence drift:
   - closeout docs can reference stale or missing semantic-compiler artifacts.
5. Artifact schema drift:
   - schema IDs in referenced artifacts can drift from frozen contract IDs.
6. Artifact hash drift:
   - evidence blocks can embed non-matching hashes without deterministic recomputation checks.
7. Stop-gate keyset drift:
   - CI wiring work can accidentally alter keyset extraction or introduce new keys.
8. Cardinality drift masking:
   - keyset additions/removals can be missed if only pass/fail aggregate is checked.
9. Cross-arc provenance drift:
   - v42 closeout can accidentally compare against wrong baseline artifacts.
10. Runtime-observability row drift:
   - v42 closeout can omit v41-v42 comparison or report non-deterministic values.
11. Non-deterministic lint output:
   - unordered diagnostics can produce flaky CI outcomes and review noise.
12. False-green risk on malformed JSON blocks:
   - parsable-but-invalid block grammar can bypass naïve validators.
13. Over-scope risk into `V32-F`:
   - CI wiring can unintentionally ship metric-key additions.
14. Continuity regression risk:
   - v42 wiring changes can weaken prior v36-v41 mandatory guard posture.

## Required Guardrails

- CI-lane lock: required checks execute in default Python lane.
- Entrypoint lock: one authoritative closeout lint entrypoint for v42 semantic-compiler evidence checks.
- Closeout-block lock: required JSON block families are present and machine-checkable.
- Artifact-existence lock: referenced semantic-compiler artifacts must exist at frozen paths.
- Artifact-schema lock: referenced artifacts must match frozen schema IDs.
- Artifact-hash lock: referenced hashes must match deterministic recomputation.
- Keyset-continuity lock: exact-set equality against v41 keyset is required.
- Cardinality lock: derived metric-key cardinality must remain `79`.
- Runtime-observability lock: v42 closeout row vs v41 baseline is required and informational-only.
- Scope fence: no `V32-F` metric-key expansion in v42.
- Continuity fence: v36/v37/v38/v39/v40/v41 continuity suites remain merge-blocking.

## Acceptance Evidence Targets (v42)

- Deterministic closeout-lint reruns are byte-stable in outputs/diagnostics under fixed inputs.
- CI fails closed on missing/mismatched semantic-compiler closeout evidence.
- v42 decision doc includes required machine-checkable block families.
- Stop-gate keyset continuity vs v41 remains exact-set equal with cardinality `79`.
- Existing continuity suites remain green and unreverted.

## Implementation Readiness Notes

1. `V32-E` is implementation-ready as a standalone `L0` thin slice on top of closed v41 outputs.
2. Highest risk is silent CI coverage drift and closeout evidence/hash mismatch acceptance.
3. Recommended implementation order:
   - deterministic closeout lint contract + fail-closed diagnostics,
   - CI workflow wiring in Python lane,
   - closeout-decision schema/block checks,
   - deterministic guard suite and regression fixtures.

## Deferred Expansions (Non-v42)

- Stop-gate metric-key extension for semantic-compiler evidence (`V32-F`) remains deferred.
- Semantic-compiler contract evolution (`V32-D` surface behaviors) remains deferred.
- Resolver namespace aliasing/workspace-scoped bindings remain deferred.
- Semantic-equivalency/deep-path keyset semantics remain deferred.
