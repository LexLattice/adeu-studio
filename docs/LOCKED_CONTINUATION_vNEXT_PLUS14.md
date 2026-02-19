# Locked Continuation vNext+14 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS13.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+13` (`A1`-`A4`) merged on `main` with green CI and closeout `all_passed = true`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md` recommends `vNext+14 = Path 8 thin slice (8a)`.
- Operational runs in the prior stage exposed provider parity/reliability gaps worth isolating:
  - route-level provider acceptance drift across module surfaces
  - codex candidate parse/shape normalization drift across proposer modules
  - module action gating inconsistencies when provider=`codex`
- This arc is reserved for provider parity/reliability hardening only:
  - provider contract normalization first
  - codex candidate normalization and parity checks second
  - fixture coverage accountability third
  - stop-gate closeout fourth

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS12.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md` remain authoritative for policy/proof/explain/runtime/core-ir/ledger semantics.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- Hidden randomness is forbidden in deterministic/replay mode:
  - UUID/random ids must be explicit input, deterministic derivation, or used only behind persisted-artifact determinism boundaries.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Canonical serialization profile is frozen for deterministic artifacts in this arc:
  - UTF-8 JSON
  - object keys sorted lexicographically
  - deterministic list ordering per each artifact lock
  - absent fields omitted (no implicit null insertion)
- Stop-gate metrics remain additive on `stop_gate_metrics@1`:
  - no schema-family fork unless an explicit later lock approves it.
- `adeu_core_ir@0.1` and `adeu.sbr.v0_1` contracts from `vNext+13` remain frozen and unchanged in this arc.
- Provider-parity scope boundary lock is frozen:
  - proposer parity in this arc targets existing proposer artifact families only:
    - `adeu.ir.v0` proposer
    - `adeu.concepts.v0` proposer
    - puzzles proposer
  - adding a new `adeu_core_ir` proposer route is out of scope for this arc.

## Arc Scope (Draft Lock)

This arc proposes Path 8 thin slice only:

1. `B1` Provider contract parity normalization for supported module routes
2. `B2` Codex candidate normalization/repair hardening + module parity assertions
3. `B3` Deterministic parity coverage accountability + transfer-report refresh
4. `B4` Stop-gate additive metrics and deterministic closeout for `vNext+14 -> vNext+15`

## B1) Provider Contract Parity Normalization

### Goal

Freeze provider acceptance/contract behavior so supported module routes treat `mock|openai|codex` consistently.

### Scope

- Normalize provider enum acceptance on module routes that expose provider selection.
- Freeze an explicit supported-route/provider matrix for deterministic validation.
- Ensure unsupported provider paths fail closed with deterministic codes.

### Locks

- Provider taxonomy lock is frozen:
  - provider set for module proposer surfaces is exactly `mock`, `openai`, `codex`.
- Dispatch asymmetry lock is frozen:
  - provider support is measured at `surface_id` contract level and may map to distinct handler implementations.
  - mock may remain on separate handler paths from `openai`/`codex` in this arc; parity requirements apply to surface behavior, not handler symmetry.
- Supported-surface lock is frozen for this arc:
  - module proposer surfaces are keyed by `surface_id` (route + mode variant when applicable), not route path only.
  - mode-dependent surfaces are explicit (for example `concepts.tournament.live_generation`, `concepts.tournament.replay_candidates`).
  - each `surface_id` provider support set is authoritative from the frozen matrix.
- Provider matrix authority lock is frozen:
  - authoritative matrix artifact path:
    - `apps/api/fixtures/provider_parity/vnext_plus14_provider_matrix.json`
  - matrix schema lock:
    - `provider_parity.vnext_plus14_matrix@1`
  - matrix entries are frozen to include:
    - `surface_id`
    - `supported_providers` (sorted, subset of `mock|openai|codex`)
    - optional `notes`
- Surface enumeration completeness lock is frozen:
  - the frozen v14 proposer `surface_id` set is exactly:
    - `adeu.propose`
    - `concepts.propose`
    - `puzzles.propose`
    - `concepts.tournament.live_generation`
    - `concepts.tournament.replay_candidates`
  - matrix entries are exhaustive for exactly this frozen `surface_id` set.
  - completeness is validated deterministically against this frozen set only; no reflective route discovery is used in deterministic acceptance.
  - inventory-to-matrix drift fails closed with `URM_PROVIDER_PARITY_SURFACE_MATRIX_DRIFT`.
- Fail-closed lock is frozen:
  - requests using an unsupported provider on a route fail deterministically with `URM_PROVIDER_PARITY_PROVIDER_UNSUPPORTED`.
  - fail-closed checks are applied at proposer entrypoint before provider dispatch.
  - `URM_PROVIDER_PARITY_PROVIDER_UNSUPPORTED` applies only when provider is within frozen `ProviderKind` but unsupported for the selected `surface_id`.
  - literal-invalid provider inputs remain request-validation failures.
- Contract-shape lock is frozen:
  - successful proposer responses must preserve existing envelope contracts (`provider`, `candidates`, proposer logs/attempts) independent of provider kind.
  - for `concepts.tournament.replay_candidates`, provider is accepted for all frozen `ProviderKind` values and is execution-inert for replay semantics.

### Acceptance

- Locked route matrix validates with no provider-literal drift.
- No supported module route rejects `provider=codex` with schema literal mismatch errors.

## B2) Codex Candidate Normalization + Module Parity

### Goal

Harden codex candidate parsing/normalization so codex outputs become contract-valid, deterministic module inputs.

### Scope

- Normalize codex candidate extraction/repair behavior for module proposer flows.
- Freeze deterministic parse/repair diagnostics and candidate rejection reasons.
- Add cross-provider parity assertions at response-contract level (shape, ranking metadata, gating fields), not semantic equivalence.

### Locks

- Normalization boundary lock is frozen:
  - normalization may repair transport/schema-shape noise only.
  - normalization may not rewrite candidate semantics.
  - ADEU-IR invariant carve-out:
    - missing/null candidate `context` may be repaired by injecting request-context before schema validation.
    - this is invariant restoration (external context contract), not semantic candidate rewriting.
- Deterministic parse diagnostics lock is frozen:
  - parse failures and repairs emit deterministic ordered reason codes.
- Candidate contract lock is frozen:
  - accepted codex candidates must satisfy the same module artifact schema contracts as existing providers.
- Module normalizer parity lock is frozen:
  - codex parse/shape normalization is required across all proposer modules in scope:
    - ADEU IR proposer
    - Concepts proposer
    - Puzzles proposer
  - module-specific normalization behavior may differ, but normalization boundaries remain identical (transport/schema-shape only).
- Parity-comparison lock is frozen:
  - parity checks are contract-level and deterministic:
    - response envelope fields present
    - candidate rank/order fields deterministic
    - provider metadata explicit (`kind`, `api`, `model`)
  - parity checks in this arc do not require cross-provider semantic identity.
- Replay boundary lock is frozen:
  - deterministic acceptance/replay uses persisted provider output fixtures only.
  - stop-gate replay may not require live codex binary invocation.
- Volatile field exclusion lock is frozen for deterministic parity hashing:
  - deterministic parity/replay hashes use a canonical contract-fingerprint projection that excludes nonsemantic provider-telemetry volatility.
  - exclusion set is frozen:
    - `created_at`
    - `raw_prompt`
    - `raw_response`
    - `prompt_hash`
    - `response_hash`
  - excluded volatile fields may be preserved for diagnostics but are not part of deterministic parity hash acceptance.
  - environment/runtime toggles (for example raw-log enable flags) may not alter deterministic parity outcomes for locked fixtures.

### Acceptance

- Locked codex fixture outputs normalize into contract-valid responses across targeted module proposer flows.
- Deterministic reruns over persisted fixtures produce byte-identical normalized outcomes.

## B3) Coverage Accountability + Transfer Report Refresh

### Goal

Make provider parity coverage measurable and reproducible.

### Scope

- Add manifest-driven coverage accounting for provider parity surfaces.
- Refresh v14 transfer report with machine-checkable evidence references.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus14_manifest.json`
  - schema:
    - `stop_gate.vnext_plus14_manifest@1`
- Manifest shape continuity lock is frozen:
  - manifest follows existing stop-gate list-style fixture pattern used in prior arcs.
  - required metric fixture lists are frozen:
    - `provider_route_contract_parity_fixtures`
    - `codex_candidate_contract_valid_fixtures`
    - `provider_parity_replay_determinism_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs (for example `fixture_id`, `surface_id`, `runs`/artifact refs).
- Fixture compactness lock is frozen:
  - fixture inventory must remain thin-slice and coverage-justified; avoid unconstrained Cartesian expansion beyond frozen metric-unit requirements.
- Coverage section lock is frozen:
  - manifest includes deterministic `coverage` entries:
    - `surface_id`
    - `fixture_ids` (sorted)
    - optional `notes`
- Coverage validity lock is frozen:
  - each declared provider-parity surface must map to at least one fixture id.
- Transfer report lock is frozen:
  - output path:
    - `docs/PROVIDER_PARITY_TRANSFER_REPORT_vNEXT_PLUS14.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "provider_parity_transfer_report.vnext_plus14@1"`
    - `vnext_plus14_manifest_hash`
    - `provider_matrix_hash`
    - `parity_summary`
    - `coverage_summary`

### Acceptance

- Coverage accounting is reproducible across reruns for identical fixture inputs.
- Transfer report references deterministic evidence artifacts only.

## B4) Stop-Gate Metrics + Provider-Parity Closeout

### Goal

Add reproducible provider parity/reliability closeout metrics to decide if `vNext+15` may start.

### Scope

- Extend additive `stop_gate_metrics@1` fields for provider parity closeout.
- Add deterministic fixture-based metric computation and report rendering.

### Locks

- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `provider_route_contract_parity_pct`
  - `codex_candidate_contract_valid_pct`
  - `provider_parity_replay_determinism_pct`
- Determinism metric computation lock is frozen:
  - canonical hash per fixture/output artifact
  - replay exactly `N=3` times per fixture
  - fixture passes only when all replay hashes match
  - `pct = 100 * passed / total`
- Metric denominator lock is frozen:
  - fixture selection is defined by:
    - `apps/api/fixtures/stop_gate/vnext_plus14_manifest.json`
  - denominator units are frozen per metric:
    - route/provider parity metrics are computed over explicit `(surface_id, provider)` units derived from each fixture entry.
    - replay determinism metrics are computed over fixture replay units defined by manifest entries and `replay_count`.
  - `total` for each metric equals the number of frozen units derived from that metric's fixture list.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus14_manifest_hash`.
  - mismatch fails closed with `URM_PROVIDER_PARITY_MANIFEST_HASH_MISMATCH`.
- Replay boundary lock is frozen:
  - closeout metrics are computed from persisted fixtures/artifacts only.
  - no live provider calls are permitted in deterministic stop-gate acceptance paths.
  - this gate validates deterministic contract replay, not live provider service health.
- Threshold lock is frozen for `vNext+14 -> vNext+15`:
  - `provider_route_contract_parity_pct == 100.0`
  - `codex_candidate_contract_valid_pct == 100.0`
  - `provider_parity_replay_determinism_pct == 100.0`

### Acceptance

- Provider parity metrics are reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+14` thresholds.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_PROVIDER_PARITY_*` additions in this arc are frozen:
  - `URM_PROVIDER_PARITY_PROVIDER_UNSUPPORTED`
  - `URM_PROVIDER_PARITY_RESPONSE_INVALID`
  - `URM_PROVIDER_PARITY_ROUTE_MATRIX_INVALID`
  - `URM_PROVIDER_PARITY_SURFACE_MATRIX_DRIFT`
  - `URM_PROVIDER_PARITY_PARSE_ERROR`
  - `URM_PROVIDER_PARITY_FIXTURE_INVALID`
  - `URM_PROVIDER_PARITY_MANIFEST_HASH_MISMATCH`
- Compatibility lock is frozen:
  - existing legacy endpoint error shapes/codes remain accepted for compatibility.
  - new URM provider-parity codes are additive and must not remove prior legacy error identifiers where already exposed.
  - when legacy structured error payloads already include `detail.code`, preserve that code and add `urm_code` additively.
  - when legacy endpoints return string `detail`, preserve string detail for compatibility and emit deterministic `urm_code` in evidence/stop-gate artifacts.

## Commit Plan (Small Green Commits)

1. `provider-parity: normalize route provider contracts and freeze v14 provider matrix`
2. `provider-parity: harden codex candidate normalization/repair and parity diagnostics`
3. `provider-parity: add deterministic fixture coverage accounting and transfer-report refresh`
4. `metrics: extend stop-gate with vnext_plus14 provider parity manifest-driven keys`
5. `tests: add deterministic provider-route/candidate/parity replay fixtures for closeout`

## Intermediate Stage Outputs (Draft)

Before implementation PR1 for `vNext+14`, prepare and review:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS13.md` (closeout gate artifact)
2. `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md` (post-`vNext+13` baseline refresh)
3. `apps/api/fixtures/provider_parity/vnext_plus14_provider_matrix.json` (route/provider authority matrix draft)
4. initial fixture inventory for `vnext_plus14_manifest.json` keyed by the three frozen metrics

## Exit Criteria (Draft)

- `B1`-`B4` merged with green CI.
- `provider_route_contract_parity_pct == 100.0` on locked fixtures.
- `codex_candidate_contract_valid_pct == 100.0` on locked fixtures.
- `provider_parity_replay_determinism_pct == 100.0` on locked fixtures.
- `vNext+14 -> vNext+15` frozen thresholds all pass.
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing stop-gate tracked `vNext+6` through `vNext+13` metrics remain at threshold.
- `vNext+12` closeout evidence remains green and reproducible.
- `vNext+13` closeout evidence remains green and reproducible.
