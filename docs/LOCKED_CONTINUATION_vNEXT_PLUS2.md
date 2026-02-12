# Locked Continuation vNext+2 (Frozen)

This document freezes the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS1.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS1.md`

Status: frozen.

Decision basis:

- vNext+1 stop-gate passed (`stop_gate_metrics@1`, `all_passed=true`) on `main`.
- Selected next primary arc: **Portability Proof v2** (Option C).

## Global Locks

- No solver semantic changes in this arc.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none in this arc).
- Determinism and replayability remain mandatory for new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- No domain-specific fork of URM event taxonomy or URM error envelope.
- Domain expansion is closed-world in this arc:
  - local provided inputs only
  - no network, browsing, or external retrieval

## Arc Scope (Frozen)

This arc implements only:

1. `C1` Domain tool-pack protocol hardening
2. `C2` Second non-ADEU compact domain pack (`urm_domain_digest`)
3. `C3` Cross-domain conformance suite (offline + deterministic)
4. `C4` Portability transfer report v2 (evidence-backed)

## C1) Domain Tool-Pack Protocol Hardening

### Goal

Strengthen cross-domain runtime contracts without introducing ADEU coupling.

### Scope

- Evolve `DomainToolPack` contract from ad-hoc dispatch to explicit metadata surfaces.
- Add deterministic pack metadata/listing APIs in runtime registry.
- Keep `call_tool(...)` semantics stable for current routes.

### Locks

- Tool-pack registry ordering is deterministic:
  - sort by `(domain_pack_id, domain_pack_version)`.
- `domain_pack_version` ordering is lexicographic over opaque version strings in vNext+2 (no semver precedence parsing in this arc).
- Tool metadata/list output ordering is deterministic:
  - sort by `tool_name` ascending.
- Tool names are a global namespace across packs and must be unique; collisions fail registry build.
- Tool names should follow `<domain>.<tool>` naming form to reduce cross-pack collision risk.
- Runtime must not require domain-specific imports in `urm_runtime`.
- Existing tool call response contract remains unchanged (`ToolCallResponse` additive-only).

### Acceptance

- Existing `urm_domain_adeu` and `urm_domain_paper` adapt to the hardened protocol.
- Registry lookup/dispatch tests remain deterministic across registration order permutations.

## C2) Second Compact Domain Pack (`urm_domain_digest`)

### Goal

Pressure-test portability with a second non-ADEU domain pack beyond `paper`.

### Scope

- Add package:
  - `packages/urm_domain_digest/`
- Frozen minimal tool surface:
  - `digest.ingest_text`
  - `digest.extract_digest_candidate`
  - `digest.check_constraints`
  - `digest.emit_artifact`
- Register pack in runtime domain registry wiring.
- Add capability-lattice actions for digest tools.

### Locks

- Domain is closed-world:
  - no web fetch
  - no connector discovery dependency
  - no external knowledge retrieval
- Deterministic/offline baseline must not depend on model availability:
  - fixture/conformance paths must run without live model calls
  - any optional model-assisted path is explicitly non-conformance in this arc
- Domain pack cannot import ADEU internals.
- Any new generic runtime primitive introduced in this arc must be justified by at least two domain packs.
- Output artifact shape is versioned and deterministic (`digest.artifact.v1`).
- `digest.artifact.v1` minimum fields are frozen:
  - `input_hash`
  - `policy_hash`
  - `domain_pack_id`
  - `domain_pack_version`
  - `schema_version`
  - `evidence_refs`
- Digest tool executions must emit `urm-events@1` events so replay/conformance checks need no domain-specific exception paths.

### Acceptance

- Deterministic end-to-end digest flow for identical inputs.
- URM policy/capability gates apply unchanged to digest tools.
- Digest actions emit URM evidence/event artifacts using existing taxonomy.

## C3) Cross-Domain Conformance Suite (Offline)

### Goal

Prove portability claims with deterministic, CI-safe conformance checks.

### Scope

- Add conformance runner script producing:
  - `artifacts/domain_conformance.json`
- Validate for each domain pack in-scope (`paper`, `digest`):
  - event envelope validity (`urm-events@1`)
  - policy gating behavior
  - replay determinism
  - error envelope/taxonomy conformance
- Add import-audit test ensuring `urm_runtime` introduces no ADEU-only imports.

### Locks

- Conformance suite must run offline:
  - no live Codex login requirement
  - no network calls
  - fixture/snapshot-driven inputs only
- Conformance outputs are deterministic and machine-readable.
- Failures must be diff-friendly and identify offending domain/tool/check.
- Conformance runner must include deterministic registry-order checks:
  - permuting domain-pack registration order yields byte-identical registry metadata outputs.
- Conformance runner must include error-envelope/taxonomy checks per domain for:
  - unknown tool
  - policy denied
  - invalid argument/schema input

### Acceptance

- Both non-ADEU domains (`paper`, `digest`) pass conformance suite.
- Import-audit passes with no new ADEU coupling in runtime core.
- CI emits and uploads `domain_conformance.json`.

## C4) Portability Transfer Report v2

### Goal

Publish evidence-backed portability deltas after C1-C3.

### Scope

- Add report:
  - `docs/PORTABILITY_TRANSFER_REPORT_NPLUS2.md`
- Report must include:
  - reused runtime components (unchanged)
  - coupling points removed/avoided
  - domain-only additions and their boundaries
  - evidence references to conformance artifacts

### Locks

- Report claims must be evidence-backed from generated artifacts.
- Report must not claim semantic portability beyond tested scope.
- Report must anchor portability claims to `artifacts/domain_conformance.json` (or CI-uploaded equivalent) as primary evidence.
- Report must explicitly state tested scope boundaries (offline, fixture-driven, closed-world inputs).
- Any new generic runtime primitive added in this arc must list at least two domain packs that require it.

### Acceptance

- Report is reproducible from CI artifacts.
- Report links concrete evidence refs for each portability claim.

## Error-Code Policy (Frozen)

- Reuse existing URM/common codes where applicable.
- New endpoint/domain-specific codes are allowed only when needed and must be prefixed `URM_`.
- Compatibility lock:
  - existing callers handling `URM_POLICY_DENIED` and `URM_NOT_FOUND` remain supported.

## Commit Plan (Small Green Commits)

1. `runtime: harden DomainToolPack protocol and deterministic registry metadata`
2. `domain: add urm_domain_digest package with minimal deterministic tool surface`
3. `policy: add digest actions to capability lattice/allow coverage and tests`
4. `conformance: add offline cross-domain conformance runner and import-audit checks`
5. `docs: add portability transfer report v2 with evidence refs`

## PR Sequence (Frozen)

1. **PR1: Protocol Hardening**
   - C1 protocol/registry metadata hardening
   - adapter updates for existing `adeu` + `paper`
2. **PR2: Digest Domain Pack**
   - C2 new `urm_domain_digest` package + tool adapters + deterministic fixtures
3. **PR3: Conformance + CI**
   - C3 conformance runner + import-audit
   - CI artifact upload for `domain_conformance.json`
4. **PR4: Transfer Report**
   - C4 evidence-backed portability report v2
   - final arc acceptance verification

## Exit Criteria

- C1-C4 merged with green CI.
- Both non-ADEU domains (`paper`, `digest`) pass offline conformance.
- No new ADEU coupling detected in `urm_runtime`.
- Portability transfer report v2 published with evidence refs.
- Follow-on arc decision prepared for `Semantic Depth v2.1` lock.
