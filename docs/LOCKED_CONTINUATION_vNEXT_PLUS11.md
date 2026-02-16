# Locked Continuation vNext+11 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS10.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS10.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- vNext+10 (`D1`-`D4`) merged on `main` with green CI and stop-gate `all_passed = true`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` recommends `vNext+11 = Path 6` (portability/conformance v3 expansion).
- This arc is reserved for portability/conformance hardening only:
  - conformance contract and determinism normalization first
  - cross-domain artifact parity expansion second
  - stop-gate and transfer-report closeout third

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS7.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS8.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS9.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS10.md` remain authoritative for policy/proof/explain/runtime/semantic-depth semantics.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- Hidden randomness is forbidden in deterministic/replay mode:
  - UUID/random ids must be explicit input, deterministic derivation, or used only behind persisted-artifact determinism boundaries.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Conformance decisions/reports must be reproducible from persisted fixtures/artifacts only:
  - no live environment/process reads in deterministic acceptance paths.
- Conformance execution-mode lock is frozen:
  - conformance suite runs offline and deterministic.
  - no remote network dependency is permitted in deterministic conformance gates.
- Domain-neutral boundary lock is frozen:
  - `urm_runtime` core remains domain-agnostic.
  - domain-specific logic is confined to domain packs and explicitly scoped adapters.
- Conformance report contract authority is frozen:
  - `domain_conformance@1` remains the authoritative conformance artifact in this arc (additive fields only).
- Canonicalization authority lock is frozen:
  - conformance and portability hash/replay paths in this arc use `urm_runtime.hashing.canonical_json` as authoritative canonical serializer.
- Conformance replay boundary is frozen:
  - stop-gate conformance replay metrics are computed from persisted conformance/artifact fixtures.
  - stop-gate replay may not invoke live domain-pack runners in deterministic acceptance paths.
- Stop-gate metrics remain additive on `stop_gate_metrics@1`:
  - no schema-family fork unless an explicit later lock approves it.
- Canonical serialization profile is frozen for deterministic artifacts in this arc:
  - UTF-8 JSON
  - object keys sorted lexicographically
  - deterministic list ordering per each artifact lock
  - absent fields omitted (no implicit null insertion)

## Arc Scope (Draft Lock)

This arc proposes only Path 6 thin-slice implementation:

1. `C1` Domain conformance contract normalization + deterministic report hardening
2. `C2` Cross-domain artifact parity expansion for post-vNext+10 artifacts
3. `C3` Conformance coverage accountability + portability transfer-report refresh
4. `C4` Replay metrics + stop-gate hardening for portability closeout

## C1) Domain Conformance Contract Normalization

### Goal

Freeze deterministic domain-conformance report semantics and replay boundaries.

### Scope

- Harden deterministic `domain_conformance@1` report generation under `apps/api/src/adeu_api/urm_domain_conformance.py`.
- Add canonical report hash semantics for deterministic closeout reporting.
- Freeze deterministic report ordering and issue sorting conventions.
- Add deterministic runtime-root resolution for import-audit:
  - report builder accepts explicit runtime-root override for deterministic fixture runs.
  - default runtime-root derivation is allowed only as fallback for local convenience execution.

### Locks

- `domain_conformance@1` envelope contract is frozen:
  - `schema = "domain_conformance@1"`
  - `valid`
  - `registry_order_determinism`
  - `import_audit`
  - `domains`
  - `issues`
  - optional `hash_excluded_fields`
  - optional `domain_conformance_hash`
- Domain ordering lock is frozen:
  - `domains` are ordered deterministically by canonical domain key.
- Issue ordering lock is frozen:
  - `issues` must be sorted before hash/replay comparison by:
    - `(code ASC, canonical_json(context) ASC, message ASC)`.
  - absent `context` is treated as `{}`.
- Domain check shape lock is frozen:
  - per-domain checks must include:
    - `event_envelope`
    - `replay_determinism`
    - `policy_gating`
    - `error_taxonomy`
- Import-audit lock is frozen:
  - runtime import audit remains authoritative for coupling guardrails.
  - forbidden import prefixes remain explicit and deterministic.
- Runtime-root resolution lock is frozen:
  - deterministic conformance fixtures must pass explicit runtime-root input to import-audit/report builder.
  - fallback relative-path runtime-root derivation may not be relied on for deterministic acceptance fixtures.
- Import-audit missing-root behavior lock is frozen:
  - missing runtime-root/import-audit prerequisites are deterministic hard failures.
  - environment-specific path diagnostics from missing-root failure paths are nonsemantic-only and excluded from success-hash acceptance fixtures.
- Report-hash lock is frozen:
  - `domain_conformance_hash = sha256(canonical_json(report_without_nonsemantic_fields))`.
- Report-hash exclusion lock is frozen:
  - `domain_conformance_hash` exclusion set is explicit and schema-frozen:
    - `hash_excluded_fields`
    - `generated_at`
    - `runtime_root_path`
    - `missing_runtime_root_path`
    - `operator_note`
  - when present, `hash_excluded_fields` must equal the frozen exclusion list exactly.
- Failure behavior lock is frozen:
  - malformed report payloads fail closed in deterministic validation paths.
- Issue-code compatibility lock is frozen:
  - conformance issues may retain existing legacy `code` values for additive compatibility.
  - canonical URM taxonomy must be exposed via `urm_code` on new/updated issues.
  - deterministic conformance gates consume `urm_code` when present.

### Acceptance

- Identical persisted fixture inputs replay to byte-identical `domain_conformance@1` reports.
- `domain_conformance_hash` recomputation matches embedded hash on locked fixtures.

## C2) Cross-Domain Artifact Parity Expansion

### Goal

Expand deterministic cross-domain parity coverage for artifacts introduced across prior arcs.

### Scope

- Add deterministic parity checks for:
  - `policy_lineage@1`
  - `proof_evidence@1`
  - `explain_diff@1`
  - `semantic_depth_report@1`
- Freeze parity projection rules for semantic payload comparison.
- Add parity fixture pairs for deterministic comparison:
  - each parity fixture entry contains:
    - `fixture_id` (required)
    - `artifact_schema`
    - `left_ref`
    - `right_ref`
    - optional `notes`

### Locks

- Parity projection lock is frozen:
  - artifact parity comparison uses semantic projections only.
  - semantic projection for each artifact schema is derived from that artifact family's authoritative semantic/hash exclusion contract (no independent exclusion table in conformance layer).
  - artifact-specific nonsemantic exclusions remain authoritative from each artifact lock.
- Policy-lineage projection authority lock is frozen:
  - `policy_lineage@1` parity requires an authoritative lineage semantic-projection/hash-exclusion contract in policy-lineage source-of-truth modules.
  - conformance parity code may not introduce policy-lineage-specific exclusion logic outside that authoritative contract.
  - if authoritative policy-lineage projection contract is unavailable, parity fixture evaluation fails closed with `URM_CONFORMANCE_PROJECTION_UNSUPPORTED`.
- Parity pass-condition lock is frozen:
  - fixture passes only when:
    - `semantic_projection(left) == semantic_projection(right)`.
  - semantic mismatch fails closed with `URM_CONFORMANCE_ARTIFACT_PARITY_MISMATCH`.
- Parity fixture lock is frozen:
  - each parity fixture must reference persisted fixture artifacts only.
  - `left_ref`/`right_ref` are frozen to:
    - workspace-relative fixture file paths under locked fixture roots, OR
    - canonical `artifact:<...>` refs resolvable from persisted artifact stores.
  - unresolved artifact refs fail closed in deterministic parity paths with `URM_CONFORMANCE_ARTIFACT_REF_INVALID`.
- Domain-extension lock is frozen:
  - domain-specific extensions may exist only in explicit nonsemantic/raw fields and may not alter semantic parity outcomes.
- Ordering lock is frozen:
  - parity fixture evaluation order is deterministic by `fixture_id ASC`.
  - `fixture_id` values must be unique within parity fixture manifests.
- Parity output placement lock is frozen:
  - parity-check outcomes are emitted as deterministic conformance checks (additive report field allowed) and are consumable by C4 stop-gate metrics without recomputation drift.

### Acceptance

- Cross-domain parity fixtures are deterministic across replay reruns.
- Semantic parity checks pass for locked fixtures with stable canonical hashes.

## C3) Coverage Accountability + Transfer Report Refresh

### Goal

Make conformance coverage growth measurable and reproducible.

### Scope

- Add deterministic coverage accounting for exercised conformance surfaces.
- Refresh portability transfer report with reproducible evidence references.
- Allow one compact additional domain pressure test only when coverage deltas justify it.

### Locks

- Coverage accounting lock is frozen:
  - coverage metrics are computed from a locked fixture manifest, not ad-hoc runtime scans.
- Coverage manifest contract lock is frozen:
  - portability/conformance coverage accounting is carried by:
    - `apps/api/fixtures/stop_gate/vnext_plus11_manifest.json`.
  - manifest includes an explicit `coverage` section with frozen shape:
    - `surface_id` (for example `domain.digest.event_envelope`, `runtime.import_audit`)
    - `fixture_ids` (sorted list)
    - optional `pressure_test` boolean (default omitted/false)
  - gate-valid coverage requires every declared conformance surface to map to at least one fixture id.
- Pressure-test scope lock is frozen:
  - at most one additional compact pressure-test domain/suite may be added in this arc.
  - addition requires explicit coverage-gap justification in report context.
- Transfer-report reproducibility lock is frozen:
  - transfer report outputs must be reproducible from persisted fixture artifacts and deterministic computations only.
- Transfer-report format lock is frozen:
  - portability transfer report output path is:
    - `docs/PORTABILITY_TRANSFER_REPORT_vNEXT_PLUS11.md`.
  - report must contain machine-checkable fenced JSON block (`json`) with frozen top-level keys:
    - `schema = "portability_transfer_report.vnext_plus11@1"`
    - `vnext_plus11_manifest_hash`
    - `domain_conformance_hash`
    - `coverage_summary`
    - `parity_summary`
    - `pressure_test_justification` (optional)
- Transfer-report provenance lock is frozen:
  - refreshed transfer report must include:
    - `vnext_plus11_manifest_hash`
    - canonical `domain_conformance_hash` for golden conformance fixtures
    - parity fixture/hash summary references used in closeout.
- Runtime coupling guard lock is frozen:
  - import-audit and registry-order determinism remain mandatory conformance gates.

### Acceptance

- Coverage metrics are reproducible across reruns for identical fixture inputs.
- Transfer report references deterministic evidence artifacts and passes reproducibility checks.

## C4) Portability Replay Metrics + Stop-Gate Hardening

### Goal

Add reproducible portability closeout metrics to decide if `vNext+12` may start.

### Scope

- Extend additive `stop_gate_metrics@1` fields for portability/conformance closeout.
- Add deterministic fixture-based metric computation and report rendering.

### Locks

- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `domain_conformance_replay_determinism_pct`
  - `cross_domain_artifact_parity_pct`
  - `runtime_domain_coupling_guard_pct`
- Determinism metric computation algorithm is frozen:
  - canonical hash per artifact/fixture
  - replay exactly `N=3` times per fixture
  - fixture passes only when all replay hashes match
  - `pct = 100 * passed / total`
- Conformance replay-definition lock is frozen:
  - for `domain_conformance_replay_determinism_pct`, replay is hash-recomputation over persisted `domain_conformance@1` fixture artifacts.
  - this metric may not be computed by rerunning live conformance generators during stop-gate evaluation.
- Metric denominator and fixture selection are frozen:
  - fixture selection is defined by a locked manifest file:
    - `apps/api/fixtures/stop_gate/vnext_plus11_manifest.json`
  - manifest schema is frozen:
    - `stop_gate.vnext_plus11_manifest@1`
  - `total` for each vNext+11 metric equals number of fixture entries listed for that metric in the manifest.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus11_manifest_hash`.
  - hash is computed as `sha256(canonical_json(manifest_payload))`.
  - metric computation is invalid if runtime manifest hash does not match recomputed canonical hash and fails closed with `URM_CONFORMANCE_MANIFEST_HASH_MISMATCH`.
- Runtime coupling metric definition lock is frozen:
  - `runtime_domain_coupling_guard_pct` is computed from persisted conformance fixture outcomes only:
    - fixture passes iff both `import_audit.valid == true` and `registry_order_determinism.valid == true`.
  - this metric is a deterministic regression guard over persisted conformance artifacts; it does not require live source rescans during stop-gate replay.
- Stop-gate execution-order lock is frozen:
  - fixture evaluations may execute in parallel for CI throughput.
  - aggregation and report emission ordering remain deterministic by metric key then fixture id.
- Metrics are computed only from locked fixtures/replay artifacts.
- No live-run data may be mixed into deterministic stop-gate deltas.
- `vNext+11 -> vNext+12` thresholds are frozen:
  - `domain_conformance_replay_determinism_pct == 100.0`
  - `cross_domain_artifact_parity_pct == 100.0`
  - `runtime_domain_coupling_guard_pct == 100.0`
  - if any fail: continue Path 6 hardening; do not start Path 7.

### Acceptance

- Stop-gate portability metrics are reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen vNext+11 thresholds.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- Conformance code family in this arc is explicit/additive:
  - `URM_CONFORMANCE_*`
- Frozen additions in this arc:
  - `URM_CONFORMANCE_REPORT_INVALID`
  - `URM_CONFORMANCE_ARTIFACT_PARITY_MISMATCH`
  - `URM_CONFORMANCE_ARTIFACT_REF_INVALID`
  - `URM_CONFORMANCE_PROJECTION_UNSUPPORTED`
  - `URM_CONFORMANCE_MANIFEST_HASH_MISMATCH`
  - `URM_CONFORMANCE_RUNTIME_IMPORT_AUDIT_FAILED`
  - `URM_CONFORMANCE_FIXTURE_INVALID`
- Endpoint/code mapping remains explicit and additive-only.

## Commit Plan (Small Green Commits)

1. `conformance: harden domain_conformance@1 ordering/hash/validation contracts`
2. `conformance: add cross-domain parity fixtures for policy/proof/explain/semantic-depth artifacts`
3. `conformance: add deterministic coverage accounting and refresh transfer-report evidence`
4. `metrics: extend stop-gate with vnext_plus11 portability manifest-driven keys`
5. `tests: add deterministic replay/parity/coupling fixtures for portability closeout`

## Exit Criteria (Draft)

- `C1`-`C4` merged with green CI.
- Domain conformance replay determinism is `100%` on locked fixtures.
- Cross-domain artifact parity is `100%` on locked fixtures.
- Runtime/domain coupling guard is `100%` on locked fixtures.
- `vNext+11 -> vNext+12` frozen stop-gate thresholds all pass.
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing `vNext+6`, `vNext+7`, `vNext+8`, `vNext+9`, and `vNext+10` determinism metrics remain at threshold.
