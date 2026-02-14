# Locked Continuation vNext+6 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS5.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS5.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- vNext+5 (`B1`-`B4`) merged on `main` with green CI.
- vNext+5 stop-gate draft currently recommends `GO_VNEXT_PLUS6_DRAFT`.
- This arc is reserved for **Semantics v3 operational hardening only**.

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Semantics/runtime outputs must be reproducible from persisted artifacts only:
  - no live environment/process state reads for deterministic decisions/reports.

## Arc Scope (Draft Lock)

This arc proposes only Semantics v3 operational deepening:

1. `S1` Validator evidence packet normalization + schema hardening
2. `S2` Conflict witness determinism + atom-map reproducibility hardening
3. `S3` Semantics diagnostics surfaces (assurance/status/witness) hardening
4. `S4` Semantics v3 replay metrics + stop-gate reporting hardening

## S1) Validator Evidence Packet Hardening

### Goal

Make solver-backed validator runs operationally auditable and replay-stable.

### Scope

- Introduce/freeze a versioned validator evidence artifact for runtime/reporting.
- Ensure payload includes frozen reproducibility anchors from `docs/SEMANTICS_v3.md`:
  - backend name/version
  - timeout and solver options
  - `formula_hash`
  - `request_hash`
  - structured evidence payload (`model` / `unsat_core` / `stats`)

### Locks

- `ValidatorResult.status` set remains frozen (`SAT`, `UNSAT`, `UNKNOWN`, `TIMEOUT`, `INVALID_REQUEST`, `ERROR`).
- Evidence packet ordering is deterministic and canonicalized.
- Identical validator inputs must produce byte-identical normalized evidence packets.

### Acceptance

- Validator evidence artifacts validate against versioned schema.
- Identical replay inputs yield byte-identical normalized validator evidence.

## S2) Conflict Witness + Atom-Map Reproducibility

### Goal

Guarantee deterministic conflict witness reconstruction for SAT/UNSAT outcomes.

### Scope

- Freeze deterministic atom naming and witness projection surfaces.
- Canonicalize unsat-core/witness ordering and atom-map linkage.
- Harden deterministic mapping from named assertions to human-readable witness entries.

### Locks

- Assertion naming remains frozen to `a:<object_id>:<json_path_hash>`.
- `json_path_hash` derivation remains frozen to `sha256(json_path).hexdigest()[:12]`.
- Unsat-core/witness outputs are canonical sorted before emission.
- No fallback to non-deterministic witness reconstruction is allowed.

### Acceptance

- Reconstructed witness outputs are byte-identical for identical replay inputs.
- Unsat-core-to-atom-map linkage is stable and reproducible across reruns.

## S3) Semantics Diagnostics Surfaces

### Goal

Expose semantics outcome diagnostics without changing solver semantics.

### Scope

- Add additive diagnostics surfaces for:
  - assurance level (`kernel_only`, `solver_backed`, `proof_checked`)
  - validator status
  - conflict witness references
- Keep diagnostics derived from persisted artifacts only.

### Locks

- Diagnostics are informational only and may not alter solver or policy decisions.
- No live external lookups are allowed in deterministic/replay diagnostics.
- Closed-world predicate semantics remain frozen:
  - `(defined <def_id>)` and `(refers_to_doc "...")` resolve only against IR/internal refs.

### Acceptance

- Diagnostics replay is deterministic for identical artifacts.
- Diagnostics payloads include explicit artifact/hash references.

## S4) Replay Metrics + Stop-Gate Reporting

### Goal

Add measurable, reproducible semantics-v3 stability metrics for closeout decisions.

### Scope

- Add deterministic replay metrics for validator and witness stability.
- Extend stop-gate reporting templates with semantics-v3 evidence fields.

### Locks

- Metrics are computed from locked fixture/replay inputs only.
- No live-run data may be mixed into deterministic stop-gate deltas.
- Report claims must reference concrete artifact fields/paths.

### Acceptance

- Metrics are reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for S1-S4 thresholds.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- Endpoint/code mapping remains explicit and additive-only.

## Proposed Commit Plan (Draft)

1. `semantics: add validator evidence artifact normalization and schema checks`
2. `semantics: harden atom-map/unsat-core deterministic witness reconstruction`
3. `runtime: add additive semantics diagnostics surfaces and evidence linkage`
4. `metrics: extend stop-gate semantics replay stability reporting`
5. `tests: add deterministic replay fixtures for validator/witness/diagnostics`

## Proposed Exit Criteria (Draft)

- S1-S4 merged with green CI.
- Validator evidence packet determinism is `100%` on locked fixtures.
- Conflict witness reconstruction determinism is `100%` on locked fixtures.
- Semantics diagnostics replay determinism is `100%` on locked fixtures.
- Stop-gate semantics stability metrics are reproducible on rerun.
- No solver-semantics contract delta and no trust-lane regression introduced.
