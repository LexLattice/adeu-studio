# Locked Continuation vNext+7 (Frozen)

This document freezes the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS6.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS6.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md`
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`

Status: frozen.

Decision basis:

- vNext+6 (`S1`-`S4`) merged on `main` with green CI and stop-gate `all_passed = true`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` recommends `vNext+7 = Path 1 thin slice + Path 2 thin slice`.
- This arc is reserved for governance/trust-lane completion only:
  - Policy/Kernel Realism v2 (thin slice)
  - Proof Activation v1 (thin slice)

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` is authoritative for policy IR/evaluator semantics in this arc.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Policy/proof decisions and reports must be reproducible from persisted artifacts only:
  - no live environment/process reads for deterministic replay decisions.
- Versioned artifacts introduced in this arc must have explicit schemas under `spec/`:
  - `policy_lineage@1`
  - `proof_evidence@1`
- Stop-gate metrics remain additive on `stop_gate_metrics@1`:
  - no schema-family fork unless an explicit later lock approves it.
- Canonical serialization profile is frozen for deterministic artifacts in this arc:
  - UTF-8 JSON
  - object keys sorted lexicographically
  - deterministic list ordering per each artifact lock
  - absent fields omitted (no implicit null insertion)

## Arc Scope (Frozen)

This arc proposes only first-slice implementation for Path 1 + Path 2:

1. `P1A` Instruction-kernel policy thin slice integration + lemma-pack compilation boundary
2. `P1B` Policy lineage artifact + lint/conformance lock hardening
3. `P2A` Proof evidence packet normalization + proof lifecycle events/codes
4. `P2B` Replay metrics + stop-gate hardening for policy/proof determinism

## P1A) Instruction-Kernel Policy Thin Slice

### Goal

Operationalize policy-first instruction governance via the locked instruction kernel without creating a parallel policy contract.

### Scope

- Integrate policy evaluation on the `LOCKED_INSTRUCTION_KERNEL_v0` contract path.
- Add exactly one deny-lemma family and one require-lemma family as macro-only compiled packs.
- Compile lemma packs into ordinary instruction-kernel `deny|require` rules using existing evaluator atoms only.
- Materialize compiled policy at policy materialization time and persist expanded policy into `policy_registry@1`.
- Preserve deterministic reload/restart behavior from `policy_registry@1` + `policy_activation_log@1`.

### Locks

- Thin-slice cap is frozen:
  - exactly one deny-lemma family + one require-lemma family + linting only.
- No new evaluator atom semantics are allowed in this slice.
- Policy decision determinism anchor tuple is frozen:
  - `policy_hash`
  - `input_context_hash`
  - `capability_snapshot_id`
  - `connector_snapshot_id` (when connector-dependent capabilities/evidence are in scope)
  - `evaluation_ts` (explicit in deterministic/replay mode)
  - `evaluator_version`
  - `policy_ir_version`
- Lemma pack compilation boundary is frozen:
  - closed-world inputs only (`lemma spec`, static repo constants, explicit materialize inputs).
  - deterministic mode may not read runtime state (`connectors`, domain registry, process env).
- Lemma-to-rule identity contract is frozen:
  - `rule_id = lemma:<lemma_pack_id>@<lemma_pack_version>:<family>:<local_id>`.
  - compiled rule `code` convention is frozen:
    - `LEMMA_<PACK>_<FAMILY>_<LOCAL_ID>_<EFFECT>`.
  - compiled rule `priority` layout is frozen:
    - deny-family compiled rules occupy a dedicated lower priority block than require-family compiled rules.
    - intra-family ordering is deterministic by `(local_priority ASC, local_id ASC)`.
  - duplicate emitted `rule_id` fails closed deterministically.
- Compilation output ordering is frozen:
  - compiled policy rules must be canonical-sorted by `(priority ASC, rule_id ASC)` at materialize time and persisted in that order.
- Policy hash source-of-truth is frozen:
  - `policy_hash` is computed from compiled policy semantic form only.
  - lemma-source metadata is lineage-only and non-semantic; it must not affect `policy_hash`.
- Cache/reload semantics are frozen:
  - key is `policy_hash` (optionally `policy_hash + evaluator_version` once evaluator versioning is introduced).
  - no TTL/time-based invalidation in deterministic/replay mode.
  - no secondary file fallback in deterministic mode.
- `LOCKED_INSTRUCTION_KERNEL_v0` evaluation order and approval-consumption semantics remain frozen and authoritative.
- Approval ordering lock is explicit:
  - approval is prechecked before kernel eval (shape/hash/expiry, no consumption),
  - requiredness is determined by matched instruction-kernel rules,
  - approval consumption is atomic with execution only when required.

### Acceptance

- Same frozen determinism anchor tuple yields byte-identical decisions/traces.
- Restart/reload fixture passes:
  - identical active `policy_hash` after restart yields identical decision traces and no reload drift.
- Lemma feasibility fixture/report proves selected deny/require families compile to existing atoms only.

## P1B) Policy Lineage + Lint/Conformance Hardening

### Goal

Add deterministic lineage and lint/conformance evidence surfaces for policy materialization/activation.

### Scope

- Introduce/freeze `policy_lineage@1` artifact contract and schema under `spec/`.
- Emit lineage records with deterministic linkage to activation evidence.
- Add deterministic lint/conformance failure codes and event emission.

### Locks

- `policy_lineage@1` linkage contract is frozen:
  - includes `policy_hash`
  - includes canonical `activation_ref` (for example `event:urm_policy:<profile_id>#<seq>`)
  - optional `lemma_pack_id@version` metadata is non-authoritative lineage only.
- Lint/conformance error codes are frozen:
  - `URM_POLICY_LINT_FAILED`
  - `URM_POLICY_PROFILE_REGISTRY_INVALID`
- Lint failure evidence event is frozen:
  - `POLICY_LINT_FAILED` appended to governed policy stream context (`urm_policy:<profile_id>` for profile-scoped operations).
- `POLICY_LINT_FAILED` payload contract is frozen:
  - `lint_rule_id`
  - `lint_code`
  - `policy_hash`
  - `profile_id`
  - `activation_ref`
- Lint/conformance failures are fail-closed and deterministic.

### Acceptance

- `policy_lineage@1` artifacts validate and replay byte-identically for identical persisted inputs.
- Lint failure fixtures emit frozen codes/events deterministically.

## P2A) Proof Evidence Packet + Lifecycle Hardening

### Goal

Operationalize `proof_checked` with deterministic evidence packets grounded to persisted proof rows.

### Scope

- Introduce/freeze `proof_evidence@1` schema under `spec/`.
- Materialize `proof_evidence@1` from persisted `proof_artifacts` rows only in deterministic/replay paths.
- Emit proof lifecycle events and deterministic backend/evidence failure codes.
- Add canonical proof hash normalization and grouped ordering semantics.

### Locks

- Proof determinism boundary is frozen:
  - normalization/materialization determinism is guaranteed for identical persisted proof-run records.
  - live backend output determinism is not claimed.
  - replay determinism is grounded to persisted proof evidence, not re-running backend tooling.
- CI reality lock is frozen:
  - required determinism checks use persisted golden proof fixtures.
  - live Lean/toolchain execution is optional and non-blocking for determinism CI in this slice.
- Proof lifecycle code/event locks are frozen:
  - codes: `URM_PROOF_BACKEND_UNAVAILABLE`, `URM_PROOF_EVIDENCE_NOT_FOUND`
  - events: `PROOF_RUN_PASS`, `PROOF_RUN_FAIL`
- Proof event stream placement is frozen:
  - `PROOF_RUN_PASS|PROOF_RUN_FAIL` append to the governed action stream that requested/required proof evaluation.
  - events must include deterministic linkage fields:
    - `parent_stream_id`
    - `parent_seq`
    - `proof_id`
    - `artifact_ref`
- `proof_evidence@1` packet contract is frozen:
  - binding key: `proof_id`
  - hash anchor: `proof_hash`
  - includes `proof_evidence_hash = sha256(canonical_json(proof_evidence_without_nonsemantic_fields))`
  - grouped ordering sorted by `(theorem_id ASC, proof_id ASC)`
  - duplicate `(theorem_id, proof_id)` in one grouped packet fails closed deterministically
  - nonsemantic exclusion field set is explicit and schema-frozen
  - provider-native payloads are `*_raw` and non-semantic.
- Schema relationship is frozen:
  - `adeu.proof_artifact.v0.json` remains IR-layer artifact schema.
  - `proof_evidence@1` is the operational normalized/reporting packet contract.
- Proof budget interaction lock is frozen:
  - proof-check accounting must explicitly declare budget lane (shared runtime budget vs dedicated proof budget), and mixed implicit accounting is forbidden.
- Proof trust-promotion gate is frozen:
  - `proof_checked` may be emitted only when:
    - a `proof_evidence@1` packet exists,
    - `proof_evidence_hash` recomputes successfully,
    - normalized proof status is `proved`.
  - otherwise trust remains at pre-proof lane (`solver_backed` or `kernel_only`) with explicit deterministic failure reason.

### Acceptance

- `proof_evidence@1` artifacts validate and hash recomputation matches embedded hash.
- Identical persisted proof rows replay to byte-identical `proof_evidence@1` packets.
- Missing-backend/missing-evidence fixtures emit frozen deterministic codes/events.

## P2B) Policy/Proof Replay Metrics + Stop-Gate Hardening

### Goal

Add reproducible closeout metrics to decide if vNext+8 may start.

### Scope

- Extend additive `stop_gate_metrics@1` fields for vNext+7 policy/proof slices.
- Add deterministic fixture-based metric computation and report rendering.

### Locks

- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `policy_lint_determinism_pct`
  - `proof_replay_determinism_pct`
  - `policy_proof_packet_hash_stability_pct`
- Determinism metric computation algorithm is frozen:
  - canonical hash per artifact/fixture.
  - replay exactly `N=3` times per fixture.
  - fixture passes only when all replay hashes match.
  - `pct = 100 * passed / total`.
- Metric denominator and fixture selection are frozen:
  - fixture selection is defined by a locked manifest file:
    - `apps/api/fixtures/stop_gate/vnext_plus7_manifest.json`
  - `total` for each vNext+7 metric equals the number of fixture entries listed for that metric in the manifest.
  - a fixture contributes to pass count only if all required artifacts for that fixture/metric satisfy the frozen hash-determinism checks.
- Metrics are computed only from locked fixtures/replay artifacts.
- No live-run data may be mixed into deterministic stop-gate deltas.
- vNext+7 -> vNext+8 thresholds are frozen:
  - `policy_lint_determinism_pct == 100.0`
  - `proof_replay_determinism_pct == 100.0`
  - `policy_proof_packet_hash_stability_pct == 100.0`
  - if any fail: continue Path 1/2 hardening; do not start Path 3/4.

### Acceptance

- Stop-gate metrics are reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen thresholds.

## Error-Code Policy (Frozen)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- Endpoint/code mapping remains explicit and additive-only.

## Commit Plan (Small Green Commits)

1. `policy: integrate instruction-kernel thin slice + lemma-pack compile boundary + deterministic reload fixtures`
2. `policy: add policy_lineage@1 schema/materialization + lint/conformance codes/events`
3. `proof: add proof_evidence@1 normalization/hashing + proof lifecycle codes/events`
4. `metrics: extend stop-gate metrics/reporting with policy/proof determinism fields`
5. `tests: add deterministic replay/hash-stability fixtures for policy/proof slices`

## Exit Criteria

- `P1A`-`P2B` merged with green CI.
- Policy lint/reload determinism is `100%` on locked fixtures.
- Proof evidence replay determinism is `100%` on locked fixtures.
- Policy/proof packet hash stability is `100%` on locked fixtures.
- `vNext+7 -> vNext+8` frozen stop-gate thresholds all pass.
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing `vNext+6` determinism metrics remain at threshold.
