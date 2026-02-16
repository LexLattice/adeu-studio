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

### Locks

- `domain_conformance@1` envelope contract is frozen:
  - `schema = "domain_conformance@1"`
  - `valid`
  - `registry_order_determinism`
  - `import_audit`
  - `domains`
  - `issues`
  - optional `domain_conformance_hash`
- Domain ordering lock is frozen:
  - `domains` are ordered deterministically by canonical domain key.
- Domain check shape lock is frozen:
  - per-domain checks must include:
    - `event_envelope`
    - `replay_determinism`
    - `policy_gating`
    - `error_taxonomy`
- Import-audit lock is frozen:
  - runtime import audit remains authoritative for coupling guardrails.
  - forbidden import prefixes remain explicit and deterministic.
- Report-hash lock is frozen:
  - `domain_conformance_hash = sha256(canonical_json(report_without_nonsemantic_fields))`.
- Failure behavior lock is frozen:
  - malformed report payloads fail closed in deterministic validation paths.

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

### Locks

- Parity projection lock is frozen:
  - artifact parity comparison uses semantic projections only.
  - artifact-specific nonsemantic exclusions remain authoritative from each artifact lock.
- Parity fixture lock is frozen:
  - each parity fixture must reference persisted fixture artifacts only.
  - unresolved artifact refs fail closed in deterministic parity paths.
- Domain-extension lock is frozen:
  - domain-specific extensions may exist only in explicit nonsemantic/raw fields and may not alter semantic parity outcomes.
- Ordering lock is frozen:
  - parity fixture evaluation order is deterministic by fixture id.

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
- Pressure-test scope lock is frozen:
  - at most one additional compact pressure-test domain/suite may be added in this arc.
  - addition requires explicit coverage-gap justification in report context.
- Transfer-report reproducibility lock is frozen:
  - transfer report outputs must be reproducible from persisted fixture artifacts and deterministic computations only.
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
- Metric denominator and fixture selection are frozen:
  - fixture selection is defined by a locked manifest file:
    - `apps/api/fixtures/stop_gate/vnext_plus11_manifest.json`
  - manifest schema is frozen:
    - `stop_gate.vnext_plus11_manifest@1`
  - `total` for each vNext+11 metric equals number of fixture entries listed for that metric in the manifest.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus11_manifest_hash`.
  - hash is computed as `sha256(canonical_json(manifest_payload))`.
  - metric computation is invalid if runtime manifest hash does not match recomputed canonical hash.
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
