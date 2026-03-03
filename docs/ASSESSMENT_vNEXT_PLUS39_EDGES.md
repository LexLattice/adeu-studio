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
   - v38 closeout preserved exact v37 keyset equality with derived cardinality `79`.
4. Semantic-source parsing remains greenfield in current `main`:
   - no deterministic parser/normalizer implementation exists yet for lock-doc semantic blocks.
5. v36/v37/v38 continuity contracts are active and must remain green through v39.

## V32-B Edge Set

1. Semantic-authority boundary drift:
   - parser logic can accidentally infer semantics from prose unless explicit blocks are strictly enforced.
2. Input-interface drift:
   - parser implementations can diverge on how source inputs are supplied unless CLI/manifest interface, manifest path resolution, and manifest ordering semantics are frozen.
3. Grammar ambiguity drift:
   - frontmatter and fenced-block grammar can become non-deterministic without a frozen parse contract.
4. Source-discovery non-determinism:
   - filesystem traversal/order can produce unstable normalized outputs unless ordering is frozen.
5. Normalization drift:
   - parser output can change across reruns if normalization ordering and key ordering are not deterministic.
6. Fence-style drift:
   - support for multiple fence styles (triple backtick vs tilde vs indented) can produce parser divergence and unstable hash outcomes.
7. Frontmatter authority bleed:
   - unconstrained frontmatter keys can become accidental semantic authority without prefix policy constraints.
8. Diagnostics contract drift:
   - unstable reason-code namespace, diagnostics ordering, indexing base, or collision payload shape can break deterministic byte-level comparisons.
9. Duplicate/ambiguous semantic identifiers:
   - duplicate module IDs or conflicting block declarations can silently overwrite unless fail-closed checks are mandatory.
10. Unknown schema tolerance risk:
   - unknown `adeu.*` block schema labels may be ignored instead of rejected without strict validation.
11. Scope-creep risk:
   - v39 parser work can leak into compiler pass-manager behavior (`V32-C`) if boundaries are not explicit.
12. Continuity regression risk:
   - parser/normalizer implementation and tests can accidentally weaken existing v36/v37/v38 guard expectations.
13. Output-path drift:
   - parser/normalizer outputs can drift to non-canonical locations without an explicit artifact base-directory contract.
14. Frontmatter YAML-profile drift:
   - differing YAML parser features (anchors/aliases/tags vs mapping-only) can yield non-deterministic parse behavior across runtimes.
15. Path canonicalization drift:
   - path separator handling, dot-segment normalization, and symlink resolution policy can diverge across OS/filesystems and alter deterministic ordering/hashes.
16. Root-boundary enforcement ambiguity:
   - without a lexical-after-normalization root check, out-of-root path rejection can vary across implementations.

## Required Guardrails

- Semantic-authority lock: only explicit semantic blocks (YAML frontmatter and/or fenced `adeu` blocks) may affect semantic outputs.
- Input-interface lock: semantic parser inputs must come only from explicit CLI args or explicit manifest; implicit traversal is forbidden.
- Entrypoint lock: semantic compile uses one authoritative command entrypoint; alternates are non-authoritative.
- Prose lock: narrative prose is non-authoritative for semantic hash derivation.
- Deterministic discovery lock: source selection and traversal order must be stable and deterministic.
- Manifest lock: manifest entries resolve relative to manifest directory, absolute manifest paths are forbidden, and manifest file order is authoritative.
- Fence-style lock: triple-backtick fences only; tilde/indented fences fail closed.
- Frontmatter YAML-profile lock: YAML 1.2 mapping-only; anchors/aliases/tags fail closed.
- Frontmatter key-policy lock: only `adeu_`/`asc_` prefixed keys are semantic-authoritative; unknown semantic-prefixed keys fail closed.
- Deterministic normalization lock: normalized record ordering and serialized key ordering must be deterministic.
- Content-normalization lock: LF line endings, trailing-whitespace trimming, and internal-whitespace preservation are frozen.
- Path-normalization lock: canonical path separator is POSIX, dot segments are collapsed deterministically, and symlink resolution is disabled for canonicalization.
- Root-boundary lock: docs-root containment is enforced lexically after path normalization.
- Diagnostics lock: reason-code namespace (`SSC[0-9]{4}`), 1-based positions, deterministic ordering `(path, start_line, code)`, and duplicate-identifier all-claim-site payloads are frozen.
- Output-path lock: semantic-source outputs are emitted only under `artifacts/semantic_compiler/v39`; out-of-base writes fail closed.
- Strict parser lock: malformed/unknown semantic block schemas, duplicate module IDs, and ambiguous declarations fail closed.
- Hash-profile continuity lock: canonical JSON/hash profile remains frozen and reused for semantic-source hash assertions.
- Scope fence: no compiler pass-manager release, no surface snapshot/delta release, no CI-gate release in v39.
- Continuity fence: no changes to v36/v37/v38 runtime boundary behaviors or guard expectations.
- Keyset fence: no new stop-gate metric keys and no schema-family fork in v39.
- Contract-publication fence: `semantic_source_collection@0.1` is an internal v39 label; schema publication is deferred to explicit follow-on lock text.

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
