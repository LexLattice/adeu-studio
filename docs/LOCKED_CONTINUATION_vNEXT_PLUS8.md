# Locked Continuation vNext+8 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS7.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS7.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- vNext+7 (`P1A`-`P2B`) merged on `main` with green CI and stop-gate `all_passed = true`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` recommends `vNext+8 = Path 3` thin slice.
- This arc is reserved for explainability productization only:
  - API/CLI contract hardening first (`3a`)
  - minimal read-only UI evidence surfaces second (`3b`)

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS7.md` remain authoritative for policy/proof semantics; explain surfaces are informational only.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Explain read/derive calls are pure by default in this arc:
  - read-only explain endpoints do not append events.
  - event emission for explain artifacts is allowed only via explicit materialization flow in this arc.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Explainability outputs/reports must be reproducible from persisted artifacts only:
  - no live environment/process reads for deterministic replay decisions/reports.
- Versioned artifacts introduced in this arc must have explicit schemas under `spec/`:
  - `explain_diff@1`
- Stop-gate metrics remain additive on `stop_gate_metrics@1`:
  - no schema-family fork unless an explicit later lock approves it.
- Canonical serialization profile is frozen for deterministic artifacts in this arc:
  - UTF-8 JSON
  - object keys sorted lexicographically
  - deterministic list ordering per each artifact lock
  - absent fields omitted (no implicit null insertion)

## Arc Scope (Draft Lock)

This arc proposes only Path 3 thin-slice implementation:

1. `E1` Explain endpoint contract normalization + `explain_diff@1` schema hardening
2. `E2` Explain API/CLI parity + canonical hash reproducibility
3. `E3` Minimal read-only UI evidence views
4. `E4` Replay metrics + stop-gate hardening for explain determinism

## E1) Explain Contract Normalization

### Goal

Freeze deterministic explain contracts on existing endpoints without endpoint reshuffle.

### Scope

- Normalize existing explain/diff endpoint outputs under a versioned `explain_diff@1` envelope.
- Keep existing endpoint paths (`/diff`, `/concepts/diff`, `/puzzles/diff`, `/explain_flip`) and add normalized explain contract fields additively.
- Freeze minimum linkage and hashing semantics for explain artifacts.
- Add optional explicit explain materialization endpoint for evidence capture:
  - `POST /urm/explain/materialize` (idempotent via `client_request_id`).
- Freeze materialization storage model for explain artifacts:
  - persist materialized explain packets as dedicated explain-artifact records keyed by `explain_id`.
  - do not overload IR `artifacts` source-of-truth rows for explain packet persistence.

### Locks

- Explain outputs are informational only:
  - no policy/solver/trust decision semantics may depend on explain payloads.
- Contract-first lock is frozen:
  - no endpoint rename/reshuffle is required for thin-slice delivery.
- Explain derivation side-effect lock is frozen:
  - `/diff`, `/concepts/diff`, `/puzzles/diff`, `/explain_flip` are pure derivations and do not append events.
  - materialized explain artifact/event emission is allowed only through explicit `POST /urm/explain/materialize`.
- `explain_diff@1` envelope top-level contract is frozen:
  - `schema = "explain_diff@1"`
  - `explain_kind` (frozen enum)
  - `explain_hash`
  - `input_artifact_refs`
  - `sections`
  - optional `builder_version`
  - optional `nonsemantic_fields`
- `explain_diff@1` minimum linkage contract is frozen:
  - `input_artifact_refs` (sorted canonical refs)
  - canonical `diff_refs`
  - canonical `witness_refs`
  - optional `semantics_diagnostics_ref`
  - optional `validator_evidence_packet_refs`
  - `explain_hash = sha256(canonical_json(explain_payload_without_nonsemantic_fields))`
- Sections shape map is frozen by `explain_kind`:
  - `semantic_diff`:
    - required section: `diff_report` (normalized `DiffReport` projection)
  - `concepts_diff`:
    - required section: `diff_report` (normalized `DiffReport` projection for concept IR)
  - `puzzles_diff`:
    - required section: `diff_report` (normalized `DiffReport` projection for puzzle IR)
  - `flip_explain`:
    - required sections: `diff_report`, `flip_explanation`
    - optional section: `analysis_delta`
    - mismatch diagnostics (`run_ir_mismatch`, `left_mismatch`, `right_mismatch`) are non-semantic diagnostics only
- `DiffReport` projection contract is frozen:
  - `diff_report` section projection version is fixed to `DiffReport projection v1` for this arc.
  - projection source is current `adeu_explain.models.DiffReport` shape only (no implicit field widening).
  - all list fields inside projected `diff_report` sections must follow explicit deterministic ordering rules; provider/native order is allowed only in `*_raw`.
- Explain ref format is frozen:
  - `artifact:<opaque_id>` or `event:<stream_id>#<seq>` only.
  - `artifact:<opaque_id>` may include typed opaque forms (for example `inline_sha256:<hash>`).
  - refs outside frozen forms fail closed in deterministic validation/materialization paths.
- Explain artifact resolver lock is frozen:
  - `artifact:` refs are resolved by one unified deterministic resolver over:
    - persisted IR artifact records
    - persisted explain-artifact records
  - unresolved refs fail closed in deterministic validation/materialization paths.
- Explain kind enum is frozen:
  - `semantic_diff`
  - `concepts_diff`
  - `puzzles_diff`
  - `flip_explain`
- Per-kind section contract is frozen:
  - each `explain_kind` must declare required/optional `sections` in `spec/explain_diff.schema.json`.
- Canonical ordering lock is frozen:
  - `input_artifact_refs`, `diff_refs`, and `witness_refs` are sorted lexicographically before emission.
  - all list fields in `sections` must define frozen deterministic ordering; provider/native order is allowed only in `*_raw` non-semantic fields.
- Nonsemantic field exclusion lock is frozen:
  - `explain_hash` exclusion set is explicit and schema-frozen:
    - `client_request_id`
    - `request_id`
    - `materialized_at`
    - `generated_at`
    - `*_raw`
    - `operator_note`
    - `run_ir_mismatch`
    - `left_mismatch`
    - `right_mismatch`
  - exclusion set is shared by API/CLI/materialization builders (no per-surface divergence).
- Optional linkage behavior is frozen:
  - absent optional refs are omitted (no implicit `null` insertion).
- Inline-input ref construction lock is frozen:
  - when explain calls are based on inline source text and no persisted artifact IDs are supplied, deterministic synthetic refs must be emitted:
    - `artifact:inline_sha256:<canonical_source_hash>`
  - canonical source hash is computed from normalized source input payload; equal semantic inputs must yield equal synthetic refs.
- Materialization event lock is frozen:
  - `POST /urm/explain/materialize` emits exactly one `EXPLAIN_MATERIALIZED` event per idempotency key.
  - event appends to the parent governed stream identified by `parent_stream_id`; if parent stream is unavailable, append to deterministic fallback stream `urm_audit:<parent_stream_id>`.
  - event payload must include deterministic linkage (`parent_stream_id`, `parent_seq`, `artifact_ref`, `client_request_id`).
- Materialization idempotency conflict semantics are frozen:
  - same `client_request_id` with different semantic payload hash fails deterministically with conflict code.
  - explain materialization reuses existing idempotency conflict code:
    - `URM_IDEMPOTENCY_KEY_CONFLICT`
- Explain builder version lock is frozen:
  - `builder_version` value format is `odeu.explain-builder.v<N>`.
  - thin-slice baseline value is `odeu.explain-builder.v1`.

### Acceptance

- Explain payloads validate against `explain_diff@1`.
- Identical persisted inputs replay to byte-identical `explain_diff@1` payloads.
- `explain_hash` recomputation matches embedded hash on deterministic fixtures.

## E2) Explain API/CLI Parity + Hash Stability

### Goal

Guarantee one deterministic explain builder across API/CLI with frozen parity fixtures.

### Scope

- Add/standardize CLI explain surfaces that emit `explain_diff@1`.
- Ensure API and CLI outputs are derived from the same normalized explain builder path.
- Freeze one canonical golden fixture for parity checks.
- Freeze CLI architecture for parity:
  - CLI parity path must call shared library-level explain builders directly (no HTTP-wrapper parity path for lock conformance tests).

### Locks

- API/CLI source-of-truth lock is frozen:
  - API and CLI explain outputs must use one shared normalization/hash builder.
- Parity lock is frozen:
  - API and CLI normalized semantic payloads/hashes must be byte-identical for identical fixture inputs.
  - parity comparison is over normalized `explain_diff@1` semantic payload (after frozen nonsemantic-field exclusion), not raw transport envelopes.
- Golden fixture lock is frozen:
  - one canonical explain fixture per `explain_kind` is version-locked and required in CI.
- Explain hash stability lock is frozen:
  - changing nonsemantic fields may not change `explain_hash`.

### Acceptance

- API/CLI parity fixtures pass with byte-identical semantic payloads and hashes.
- Golden fixture outputs validate and remain deterministic across reruns.

## E3) Minimal Read-Only UI Evidence Views

### Goal

Provide thin-slice user-facing explainability views without adding write paths.

### Scope

- Add minimal read-only UI views for:
  - semantic diff
  - conflict witness drilldown
  - policy/semantics evidence linkage

### Locks

- UI read-only lock is frozen:
  - UI consumes API artifacts only; no direct DB mutation path.
- Contract-before-UI lock is frozen:
  - `E1` + `E2` contract/parity fixtures must pass before UI completion can be claimed.
- Cross-schema evidence rendering lock is frozen:
  - UI treats `policy_explain@1`, `semantics_diagnostics@1`, and `explain_diff@1` as separate read-only artifacts.
  - linkage is by explicit artifact/event refs only; no new cross-schema semantic merge contract is introduced in this arc.
- Witness drilldown scope cap is frozen:
  - thin-slice drilldown is limited to persisted explain/causal-slice/witness refs already present in normalized explain artifacts.
  - no new source-text span highlighter or semantic reconstruction path is required in this slice.
- UI determinism lock is frozen:
  - deterministic fixtures must assert stable ordering for rendered refs/sections as derived from `explain_diff@1`.
  - pixel snapshot determinism is not a required acceptance gate in this slice.

### Acceptance

- UI rendering fixtures pass against frozen explain API fixtures.
- UI views reference explicit artifact refs/hashes exposed by `explain_diff@1` payloads.

## E4) Explain Replay Metrics + Stop-Gate Hardening

### Goal

Add reproducible explainability closeout metrics to decide if `vNext+9` may start.

### Scope

- Extend additive `stop_gate_metrics@1` fields for explain thin-slice determinism.
- Add deterministic fixture-based metric computation and report rendering.

### Locks

- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `explain_diff_determinism_pct`
  - `explain_api_cli_parity_pct`
  - `explain_hash_stability_pct`
- Determinism metric computation algorithm is frozen:
  - canonical hash per artifact/fixture
  - replay exactly `N=3` times per fixture
  - fixture passes only when all replay hashes match
  - `pct = 100 * passed / total`
- Metric denominator and fixture selection are frozen:
  - fixture selection is defined by a locked manifest file:
    - `apps/api/fixtures/stop_gate/vnext_plus8_manifest.json`
  - manifest schema is frozen:
    - `stop_gate.vnext_plus8_manifest@1`
  - `total` for each vNext+8 metric equals number of fixture entries listed for that metric in the manifest.
  - fixture contributes to pass count only if all required artifacts for that fixture/metric satisfy frozen hash-determinism checks.
- Explain metric fixture-boundary lock is frozen:
  - `explain_diff_determinism_pct` and `explain_hash_stability_pct` are computed from persisted normalized `explain_diff@1` fixture artifacts (snapshot boundary).
  - end-to-end explain pipeline determinism from input pairs to packet output is validated in dedicated E1/E2 deterministic tests and is not inferred solely from E4 snapshot metrics.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus8_manifest_hash`.
  - hash is computed as `sha256(canonical_json(manifest_payload))`.
  - metric computation is invalid if runtime manifest hash does not match recomputed canonical hash.
- Metrics are computed only from locked fixtures/replay artifacts.
- No live-run data may be mixed into deterministic stop-gate deltas.
- `vNext+8 -> vNext+9` thresholds are frozen:
  - `explain_diff_determinism_pct == 100.0`
  - `explain_api_cli_parity_pct == 100.0`
  - `explain_hash_stability_pct == 100.0`
  - if any fail: continue Path 3 hardening; do not start Path 4.

### Acceptance

- Stop-gate explain metrics are reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen thresholds.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- Explainability path code family should remain explicit/additive:
  - `URM_EXPLAIN_*` for explain contract/runtime errors when new codes are required.
- Frozen explain ref-validation code:
  - `URM_EXPLAIN_INVALID_REF`
- Frozen explain idempotency conflict code reuse:
  - `URM_IDEMPOTENCY_KEY_CONFLICT`
- Endpoint/code mapping remains explicit and additive-only.

## Proposed PR Plan (Draft)

1. `explain: add explain_diff@1 schema + canonical envelope/hashing on existing endpoints`
2. `explain: add API/CLI shared builder and frozen parity fixtures`
3. `ui: add minimal read-only explain evidence views tied to artifact refs`
4. `metrics: extend stop-gate metrics/reporting with explain determinism keys`
5. `tests: add deterministic replay/hash-stability fixtures for explain path`

## Proposed Exit Criteria (Draft)

- `E1`-`E4` merged with green CI.
- Explain replay determinism is `100%` on locked fixtures.
- Explain API/CLI parity is `100%` on locked fixtures.
- Explain packet hash stability is `100%` on locked fixtures.
- `vNext+8 -> vNext+9` frozen stop-gate thresholds all pass.
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing `vNext+6` and `vNext+7` determinism metrics remain at threshold.
