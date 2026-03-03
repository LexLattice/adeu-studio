# Assessment vNext+39 Edges (V32-B Planning)

This document records pre-implementation edge analysis for `vNext+39` (`V32-B` semantic source grammar/parser/normalizer), aligned to `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`.

Status: planning assessment (lock drafted, implementation not started).

## Scope

- In scope: semantic-source grammar definition, deterministic source discovery, parser/normalizer MVP, deterministic parser diagnostics and guard tests.
- Out of scope: commitments IR schema evolution, compiler pass manager, surface snapshots/deltas, CI lane expansion, stop-gate metric-key expansion.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS38.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS38.md`
- `apps/api/src/adeu_api/hashing.py`
- `packages/urm_runtime/src/urm_runtime/hashing.py`
- `apps/api/scripts/lint_closeout_consistency.py`

## Repository Baseline Anchors

1. Commitments IR contract baseline now exists and is closed in v38:
   - `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json`
   - `spec/adeu_commitments_ir.schema.json`
2. Deterministic canonical JSON profile is frozen and available:
   - `canonical_json`/`sha256_canonical_json` in `apps/api/src/adeu_api/hashing.py` and `packages/urm_runtime/src/urm_runtime/hashing.py`.
3. Stop-gate schema family and keyset continuity are active constraints:
   - `stop_gate_metrics@1` remains the only schema family,
   - v38 closeout preserved exact v37 keyset equality.
4. Semantic-source parsing remains greenfield in current `main`:
   - no deterministic parser/normalizer implementation exists yet for lock-doc semantic blocks.
5. v36/v37/v38 continuity contracts are active and must remain green through v39.

## V32-B Edge Set

1. Semantic-authority boundary drift:
   - parser logic can accidentally infer semantics from prose unless explicit blocks are strictly enforced.
2. Grammar ambiguity drift:
   - frontmatter and fenced-block grammar can become non-deterministic without a frozen parse contract.
3. Source-discovery non-determinism:
   - filesystem traversal/order can produce unstable normalized outputs unless ordering is frozen.
4. Normalization drift:
   - parser output can change across reruns if normalization ordering and key ordering are not deterministic.
5. Duplicate/ambiguous semantic identifiers:
   - duplicate module IDs or conflicting block declarations can silently overwrite unless fail-closed checks are mandatory.
6. Unknown schema tolerance risk:
   - unknown `adeu.*` block schema labels may be ignored instead of rejected without strict validation.
7. Scope-creep risk:
   - v39 parser work can leak into compiler pass-manager behavior (`V32-C`) if boundaries are not explicit.
8. Continuity regression risk:
   - parser/normalizer implementation and tests can accidentally weaken existing v36/v37/v38 guard expectations.

## Required Guardrails

- Semantic-authority lock: only explicit semantic blocks (YAML frontmatter and/or fenced `adeu` blocks) may affect semantic outputs.
- Prose lock: narrative prose is non-authoritative for semantic hash derivation.
- Deterministic discovery lock: source selection and traversal order must be stable and deterministic.
- Deterministic normalization lock: normalized record ordering and serialized key ordering must be deterministic.
- Strict parser lock: malformed/unknown semantic block schemas, duplicate module IDs, and ambiguous declarations fail closed.
- Hash-profile continuity lock: canonical JSON/hash profile remains frozen and reused for semantic-source hash assertions.
- Scope fence: no compiler pass-manager release, no surface snapshot/delta release, no CI-gate release in v39.
- Continuity fence: no changes to v36/v37/v38 runtime boundary behaviors or guard expectations.
- Keyset fence: no new stop-gate metric keys and no schema-family fork in v39.

## Acceptance Evidence Targets (v39)

- Semantic-source grammar/parser/normalizer MVP is present for explicit semantic blocks.
- Deterministic parser outputs are reproducible across reruns under fixed inputs.
- Parser diagnostics are deterministic and fail-closed for invalid semantic inputs.
- CI remains green with existing v36/v37/v38 continuity guards still active.

## Implementation Readiness Notes

1. `V32-B` is implementation-ready as a standalone `L1` thin slice.
2. Highest risk is semantic-boundary drift from accidental prose inference.
3. Recommended implementation order:
   - grammar and discovery contract,
   - parser + normalization payload model,
   - deterministic/fail-closed guard suite.

## Next Actions

1. Finalize `docs/LOCKED_CONTINUATION_vNEXT_PLUS39.md` selecting only `V32-B`.
2. Execute `v39` as two small-green PRs:
   - parser/normalizer contract implementation,
   - deterministic/fail-closed guard suite.
3. Keep v36/v37/v38 continuity checks mandatory during both PRs.
