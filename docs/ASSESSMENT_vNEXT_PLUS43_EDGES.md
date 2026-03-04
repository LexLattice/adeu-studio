# Assessment vNext+43 Edges (V32-F Post-Hoc)

This document records post-implementation edge analysis for `vNext+43` (`V32-F` stop-gate metric extension for semantic-compiler evidence hash parity).

Status: post-hoc assessment (March 4, 2026 UTC).

## Scope

- In scope: additive stop-gate key migration for semantic-compiler evidence hash parity, fixture/manifest deterministic validation, and closeout continuity evidence.
- Out of scope: runtime/provider/proposer boundary changes, solver semantics release changes, schema-family fork, and non-additive key churn.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS42.md`
- PR `#233` (`metrics: add V32-F semantic-compiler stop-gate extension`)
- `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
- `packages/urm_runtime/src/urm_runtime/stop_gate_registry.py`
- `apps/api/scripts/lint_closeout_consistency.py`
- `apps/api/fixtures/stop_gate/vnext_plus27_manifest.json`
- `artifacts/stop_gate/metrics_v42_closeout.json`
- `artifacts/stop_gate/metrics_v43_closeout.json`

## Post-Hoc Edge Set (V32-F)

1. Additive-key drift risk:
   - more than one key could be introduced by accident during metric extension.
2. Key-removal regression risk:
   - legacy keys could be dropped while adding new v43 metric plumbing.
3. Fixture-schema drift risk:
   - semantic-compiler hash fixtures could use a non-frozen schema.
4. Hash-profile drift risk:
   - parity hashing could silently move away from canonical JSON hash profile.
5. Manifest hash-subject drift risk:
   - parity checks could hash raw bytes instead of canonical parsed-object projections.
6. Replay-count drift risk:
   - deterministic replay cardinality could silently change and mask parity failures.
7. Surface-id scope drift risk:
   - manifest could accept non-frozen semantic-compiler surface ids.
8. False-green closeout risk:
   - closeout docs could claim additive migration without concrete baseline/current artifact evidence.
9. Continuity interpretation drift risk:
   - teams could misread additive migration as permission for unrestricted key growth.
10. CI red/green coupling risk:
   - facade signature snapshots can lag behind newly added v43 input parameters.

## Guardrail Evaluation (Observed)

- Additive migration guard: pass.
  - v42 keyset cardinality `79`, v43 keyset cardinality `80`.
  - only added key: `artifact_semantic_compiler_evidence_hash_parity_pct`.
- Schema-family continuity guard: pass.
  - both v42 and v43 closeout artifacts use `stop_gate_metrics@1`.
- Fixture-schema/hash-profile guard: pass.
  - v43 fixtures validate against `semantic_compiler_hash_capture@1` with `sha256_canonical_json_frozen`.
- Manifest determinism guard: pass.
  - v43 manifest schema `stop_gate.vnext_plus27_manifest@1`, deterministic replay count `3`.
- Gate enforcement guard: pass.
  - `artifact_semantic_compiler_evidence_hash_parity` evaluates `true` at closeout.
- CI health guard: pass after snapshot refresh.
  - facade signature snapshot updated to include `vnext_plus27_manifest_path`.

## Post-Hoc Variance vs v6 Planning

- Planned sequencing in `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md` made `V32-F` optional after `V32-E` stabilization.
- Actual sequence realized this immediately in `vNext+43` via PR `#233`.
- Variance impact: low.
  - implementation remained within `L1` additive scope,
  - no schema-family fork,
  - no boundary expansion.

## Residual Risks

1. Future additive migrations could accumulate without explicit per-arc additive-key lock text.
2. Runtime-observability regressions remain informational unless a future lock introduces explicit pass/fail thresholds.
3. Closeout docs still rely on disciplined artifact regeneration cadence; stale artifacts remain an operational risk.

## Follow-on Recommendation

1. Keep additive-key migrations explicitly enumerated per arc in lock and decision docs.
2. Preserve post-hoc audit pass after each merged additive extension.
3. Gate any further stop-gate key additions behind dedicated lock text (no implicit expansion from this arc).
