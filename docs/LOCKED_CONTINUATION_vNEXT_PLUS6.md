# Locked Continuation vNext+6 (Frozen)

This document freezes the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS5.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS5.md`
- `docs/SEMANTICS_v3.md`

Status: frozen.

Decision basis:

- vNext+5 (`B1`-`B4`) merged on `main` with green CI.
- vNext+5 stop-gate recommendation is `GO_VNEXT_PLUS6_DRAFT`.
- This arc selects **Semantics v3 operational hardening only**.

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
- Versioned artifacts introduced in this arc must have explicit schemas under `spec/`:
  - `validator_evidence_packet@1`
  - `semantics_diagnostics@1`
- Stop-gate metrics remain additive on `stop_gate_metrics@1`:
  - no schema-family fork unless an explicit later lock approves it.
- Canonical serialization profile is frozen for deterministic artifacts in this arc:
  - UTF-8 JSON
  - object keys sorted lexicographically
  - deterministic list ordering per each artifact lock
  - absent fields omitted (no implicit null insertion)
- `SEMANTICS_v3` conformance parity is mandatory:
  - new artifacts/surfaces may not alter frozen assurance semantics, status semantics, or closed-world predicate behavior.

## Arc Scope (Frozen)

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
- Introduce/freeze `validator_evidence_packet@1`:
  - schema under `spec/`
  - binding key: `validator_run_id`
  - packet is materialized from persisted validator-run records only (no live solver callback)
  - packet must repeat reproducibility anchors and normalized evidence payload with frozen top-level field names:
    - `model`
    - `unsat_core`
    - `core_trace`
    - `stats`
  - canonical evidence fields are always emitted with deterministic defaults when unavailable
  - packet must include `evidence_packet_hash = sha256(canonical_json(packet_without_nonsemantic_fields))`
- Ensure payload includes frozen reproducibility anchors from `docs/SEMANTICS_v3.md`:
  - backend name/version
  - timeout and solver options
  - `formula_hash`
  - `request_hash`
  - structured evidence payload (`model` / `unsat_core` / `core_trace` / `stats`)

### Locks

- `ValidatorResult.status` set remains frozen (`SAT`, `UNSAT`, `UNKNOWN`, `TIMEOUT`, `INVALID_REQUEST`, `ERROR`).
- Determinism claim boundary is frozen:
  - normalization determinism is guaranteed for the same persisted validator-run record (`request/result/evidence`).
  - live solver-output determinism is not claimed; replay determinism is grounded to persisted artifacts.
- Status classification rules are frozen:
  - solver `UNKNOWN` with `reason_unknown` matching timeout normalizes to `TIMEOUT`.
  - parse/SMT2 decode/request-shape failures normalize to `INVALID_REQUEST`.
  - backend/runtime exceptions outside request-invalid paths normalize to `ERROR`.
  - timeout matcher table is frozen:
    - normalized timeout reasons are case-insensitive/trimmed matches in `{"timeout", "canceled", "resourceout"}` plus explicitly versioned backend-prefixed timeout aliases (if added).
- Evidence packet ordering is deterministic and canonicalized.
- Nonsemantic field exclusion set for `evidence_packet_hash` is frozen:
  - `validator_run_id`
  - `materialized_at`
  - `observed_at`
  - `raw_path`
  - `stderr_path`
  - debug/raw fields (`*_raw`)
  - `operator_note`
  - `operator_message`
- Canonical list semantics are frozen:
  - `unsat_core` is sorted lexicographically before emission.
  - `core_trace` is canonicalized by `assertion_name` ascending.
  - any preserved provider/native ordering must be labeled `*_raw` and treated as non-semantic debug-only fields.
- Canonical `stats` normalization is frozen:
  - normalized `stats` is emitted as a deterministic key-sorted object.
  - scalar `int`/`bool`/`string` values are preserved.
  - `float` values are normalized to deterministic strings.
  - non-scalar values are canonical-serialized to deterministic strings.
- Canonical `model` normalization is frozen:
  - normalized `model` is emitted as a deterministic key-sorted object.
  - model values use deterministic string representation.
- Identical persisted validator-run records must produce byte-identical normalized evidence packets.

### Acceptance

- Validator evidence artifacts validate against versioned schema.
- Identical replay inputs yield byte-identical normalized validator evidence packets.
- Timeout/invalid/error normalization rules are covered by deterministic fixtures.
- `evidence_packet_hash` is reproducible and matches recomputed canonical hash in deterministic fixtures.

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
- Assertion-name collision handling is frozen:
  - duplicate `assertion_name` within one request fails closed as `INVALID_REQUEST`.
  - collision diagnostics must include deterministic sorted collision set metadata.
- Collision detection is mandatory before assertion-name map materialization:
  - no silent overwrite on duplicate assertion names is allowed.
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
- Introduce/freeze versioned diagnostics artifact:
  - `semantics_diagnostics@1` with schema under `spec/`.
- Keep diagnostics derived from S1/S2 persisted artifacts only:
  - `validator_evidence_packet@1`
  - conflict witness/atom-map artifacts.

### Locks

- Diagnostics are informational only and may not alter solver or policy decisions.
- No live external lookups are allowed in deterministic/replay diagnostics.
- Diagnostics builder source-of-truth is frozen:
  - diagnostics are reconstructed from persisted `validator_evidence_packet@1` + witness artifacts, never from raw backend output or live runtime state.
- Multi-run diagnostics selection and ordering are frozen:
  - included records are sorted by `(kind, formula_hash, request_hash, validator_run_id)`.
  - witness references are sorted and must reference canonical assertion names.
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
- Extend stop-gate reporting templates with semantics-v3 evidence fields on additive `stop_gate_metrics@1`.

### Locks

- Metrics are computed from locked fixture/replay inputs only.
- No live-run data may be mixed into deterministic stop-gate deltas.
- Report claims must reference concrete artifact fields/paths.
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `validator_packet_determinism_pct`
  - `witness_reconstruction_determinism_pct`
  - `semantics_diagnostics_determinism_pct`
- Semantics metric thresholds are frozen for this arc:
  - each of the three semantics determinism metrics must be `100.0` on locked fixtures.
- S4 dependency order is frozen:
  - S4 metrics are computed from S1-S3 artifacts only after those artifacts are materialized.
- Determinism metric computation algorithm is frozen:
  - for each fixture/artifact type, compute canonical artifact hash (`evidence_packet_hash` or equivalent canonical hash for witness/diagnostics artifact).
  - run deterministic replay exactly `N=3` times per fixture.
  - fixture passes determinism only when all replay hashes are identical.
  - `*_determinism_pct = 100 * (fixtures_passed / total_fixtures)`.

### Acceptance

- Metrics are reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for S1-S4 thresholds.
- Stop-gate outputs include the frozen additive metric keys.

## Error-Code Policy (Frozen)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- Endpoint/code mapping remains explicit and additive-only.

## Commit Plan (Small Green Commits)

1. `semantics: add validator evidence artifact normalization and schema checks`
2. `semantics: harden atom-map/unsat-core deterministic witness reconstruction`
3. `runtime: add additive semantics diagnostics surfaces and evidence linkage`
4. `metrics: extend stop-gate semantics replay stability reporting`
5. `tests: add deterministic replay fixtures for validator/witness/diagnostics`

## Exit Criteria

- S1-S4 merged with green CI.
- Validator evidence packet determinism is `100%` on locked fixtures.
- Conflict witness reconstruction determinism is `100%` on locked fixtures.
- Semantics diagnostics replay determinism is `100%` on locked fixtures.
- Stop-gate semantics stability metrics are reproducible on rerun.
- `SEMANTICS_v3` conformance parity tests remain green with no contract deltas.
- No solver-semantics contract delta and no trust-lane regression introduced.
