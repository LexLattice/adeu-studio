# Assessment vNext+38 Edges (V32-A Planning)

This document records pre-implementation edge analysis for `vNext+38` (`V32-A` commitments IR contract bootstrap), aligned to `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`.

Status: historical planning assessment (implementation completed on `main`, March 3, 2026 UTC).

## Closeout Addendum (Post-Implementation)

- `M1` (`V32-A` contract/bootstrap) merged via PR `#222`.
- `M2` (`V32-A` determinism/parity guards) merged via PR `#223`.
- Commitments IR contract package now exists at `packages/adeu_commitments_ir`.
- Authoritative/mirror schema pair is present:
  - `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json`
  - `spec/adeu_commitments_ir.schema.json`
- v38 closeout artifacts are present:
  - `artifacts/quality_dashboard_v38_closeout.json`
  - `artifacts/stop_gate/metrics_v38_closeout.json`
  - `artifacts/stop_gate/report_v38_closeout.md`
- Stop-gate metric keyset continuity is preserved (`v37` -> `v38` exact-set equality; cardinality `79`).

## Scope

- In scope: `V32-A` commitments IR models, schema export, schema mirror, deterministic schema guards.
- Out of scope: semantic source parsing, compiler pass manager, surface snapshots/deltas, CI lane expansion, stop-gate metric-key expansion.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS37.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS37.md`
- `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
- `packages/adeu_kernel/tests/test_fixtures.py`
- `apps/api/src/adeu_api/hashing.py`
- `packages/urm_runtime/src/urm_runtime/hashing.py`

## Repository Baseline Anchors

1. Schema export + mirror discipline already exists:
   - authoritative + mirrored schema writes in `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`.
2. Deterministic canonical JSON profile is frozen and available:
   - `canonical_json`/`sha256_canonical_json` in `apps/api/src/adeu_api/hashing.py` and `packages/urm_runtime/src/urm_runtime/hashing.py`.
3. Deterministic fixture testing style is established:
   - exact JSON equality fixture checks in `packages/adeu_kernel/tests/test_fixtures.py`.
4. Commitments-IR package was greenfield at planning time:
   - `packages/adeu_commitments_ir` is now implemented on `main` via PRs `#222` and `#223`.
5. v36/v37 continuity contracts are active and must remain green through v38:
   - governance continuity from v36,
   - persisted idempotency continuity from v37.

## V32-A Edge Set

1. Schema determinism drift:
   - Pydantic schema export can drift if union/member ordering is not normalized deterministically.
2. Schema identity/version drift:
   - schema-id and file naming convention must be frozen to one v0 style for this arc.
3. Union discriminator drift:
   - discriminated union key rename/removal can silently break contract consumers.
   - generic-string discriminator typing can permit fallback coercion rather than strict member dispatch.
4. Authoritative/mirror divergence:
   - `packages/.../schema` and `spec/...` can drift unless parity is tested as merge-blocking.
5. Over-scoping risk:
   - v38 can accidentally leak into parser/pipeline concerns if model fields encode non-v38 assumptions.
6. Unknown field tolerance risk:
   - missing strict model posture allows silent payload drift; `extra="forbid"` must be mandatory.
7. Schema-export formatting mismatch risk:
   - current repo schema exporters write with `json.dumps(..., indent=2, sort_keys=True) + "\\n"`; using compact hash-profile bytes in v38 would create avoidable convention drift.
8. Cross-arc continuity regression risk:
   - v38 tooling/docs updates must not weaken existing v36/v37 guards.
9. Generated-file sync drift:
   - schema export can pass locally but generated authoritative/mirror files can be omitted from commit without explicit cleanliness guard.

## Required Guardrails

- Model strictness: `extra="forbid"` on commitments IR models.
- Deterministic schema export: repeat export in one test run and assert byte equality.
- Mirror parity: authoritative schema bytes must equal mirrored `spec` bytes.
- Version/file pin: freeze single commitments schema identifier and repo-style naming (`*.v0_1.json` authoritative + `spec/*.schema.json` mirror) for this arc.
- Discriminator pin: freeze union discriminator key to `module_kind`.
- Strict polymorphism pin: union members must bind `module_kind` as unique `Literal[...]` values; non-literal fallback parsing is forbidden.
- Schema-export formatting continuity: follow established repo schema-export writer profile (`indent=2`, `sort_keys=True`, trailing newline, UTF-8).
- Hash-profile continuity: hash-authority canonical JSON profile remains frozen for hashing flows; schema-export byte formatting in this arc remains repo-export-style.
- Regeneration cleanliness: rerun schema export in guard flow and fail closed if tracked generated files differ from committed bytes.
- No-path-leakage guard: fail closed if exported schema content contains environment-local absolute paths.
- Scope fence: no semantic parser/pipeline code in v38 implementation slice.
- Continuity fence: no changes to v36/v37 runtime boundary behaviors or guard expectations.

## Acceptance Evidence Targets (v38)

- New package skeleton + models + schema export entrypoint are present.
- `spec/adeu_commitments_ir.schema.json` exists and is parity-validated against authoritative package schema.
- Deterministic rerun evidence proves schema export byte stability.
- CI remains green with existing v36/v37 continuity guards still active.

## Implementation Readiness Notes

1. `V32-A` is implementation-ready as a standalone `L1` thin slice.
2. Highest risk is contract drift from over-coupling IR v0 to future parser/compiler details.
3. Recommended implementation order:
   - models + IDs/reason-codes,
   - export/mirror wiring,
   - deterministic parity/rerun tests.

## Completion Trace

1. `docs/LOCKED_CONTINUATION_vNEXT_PLUS38.md` was finalized to `V32-A` scope and closed post-merge.
2. `v38` executed as two small-green PRs:
   - PR `#222`: contract package + schema export.
   - PR `#223`: deterministic guard/test suite.
3. v36/v37 continuity checks remained mandatory and green throughout v38 closeout.
