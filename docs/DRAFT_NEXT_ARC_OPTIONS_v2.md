# Draft Next Arc Options v2 (Consolidated)

This document is the single working continuation-planning draft for the current stage after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS6.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS6.md`
- `docs/SEMANTICS_v3.md`

Status: draft only (not frozen).  
Goal: provide clear high-level directions for future arcs and a clean recommended order.

## Consolidation Note

This v2 document consolidates and supersedes prior parallel continuation drafts from this stage.
The consolidated predecessor drafts were removed after merge into this document to keep one planning source of truth.

For this stage, planning should use this file only.

## Baseline Snapshot (Post vNext+6)

Current baseline includes:

- Governance ops hardening complete (`vNext+4`):
  - deterministic `policy_explain@1`, `incident_packet@1`
  - profile lifecycle and rollout/rollback by `policy_hash`
- Runtime dynamics hardening complete (`vNext+5`):
  - bounded multi-child queueing (`max_children = 2`, `max_active_children = 1`)
  - budget-v1 enforcement, connector snapshot replay, steer diagnostics
- Semantics-v3 operational hardening complete (`vNext+6`):
  - `validator_evidence_packet@1`
  - deterministic witness reconstruction
  - `semantics_diagnostics@1`
  - deterministic stop-gate metrics on additive `stop_gate_metrics@1`
- Cross-domain conformance tooling exists and is CI-integrated:
  - `apps/api/scripts/build_domain_conformance.py`
  - `apps/api/src/adeu_api/urm_domain_conformance.py`
- Explain/diff surfaces already exist in API today:
  - `/diff`, `/concepts/diff`, `/puzzles/diff`, `/explain_flip`

Net: governance, runtime orchestration, and semantics evidence are operationally hardened; next arcs should focus on strategic depth and product leverage.

## Repo-Grounded Clarifications

1. Runtime baseline is not single-child anymore.
   - Current defaults are the v2 queue thin slice (`2 total`, `1 active`), not legacy `1`.
2. Explainability is not greenfield.
   - Core endpoints exist; the gap is productization, canonical contracts, and UX.
3. Conformance is not manual-only.
   - Deterministic domain conformance build/test path already exists in CI.
4. Proof lane is partially activated in plumbing/tests.
   - Trust label promotion paths exist; missing piece is a locked proof-operational arc with explicit artifacts/metrics.
5. Runtime maintainability pressure is real.
   - `packages/urm_runtime/src/urm_runtime/copilot.py` remains large; scale arcs should include decomposition slices.

## Shared Locks For Any Next Arc

- No solver semantic contract changes unless explicitly versioned and locked.
- `docs/SEMANTICS_v3.md` remains authoritative unless a versioned follow-on lock says otherwise.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- New behavior is additive-only unless explicitly marked breaking.
- Replay determinism is mandatory for acceptance tests.
- Runtime behavior must emit evidence in `urm-events@1`.
- New `/urm/...` endpoints must be idempotent via `client_request_id`.
- Deterministic claims must be grounded to persisted artifacts/hashes only.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input or fixed deterministic default only.
- New versioned artifacts/registries must include schemas under `spec/`.
- Stop-gate metrics schema continuity is frozen:
  - additive key evolution on `stop_gate_metrics@1` only unless a later lock explicitly authorizes a version-family bump.

## Path 1: Policy/Kernel Realism v2

### Goal

Upgrade policy/instruction governance expressivity and safety without changing solver semantics.

### Scope

1. Add one frozen deny-lemma family and one frozen require-lemma family.
2. Harden policy load/cache/reload semantics with explicit boundaries.
3. Add deterministic policy conformance/lint gates for profile-policy registry and semantic diff invariants.
4. Add deterministic policy lineage/provenance reporting.
5. Introduce/freeze `policy_lineage@1` artifact contract:
   - schema under `spec/`
   - deterministic linkage to policy activation evidence

### Locks

- No best-effort policy fallback.
- No live remote policy fetch in deterministic mode.
- Thin-slice cap is frozen:
  - exactly one deny-lemma family + one require-lemma family + linting only.
- `vNext+7` policy core authority is frozen:
  - `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` remains the authoritative policy IR/evaluator contract for the thin slice.
  - lemma packs are a macro layer compiling into instruction-kernel rules; they may not create a parallel policy contract.
- Lemma implementation mode is frozen for thin slice:
  - macro-only compiled lemma packs expanding to ordinary `deny|require` rules using existing evaluator atoms only.
  - no new evaluator atom semantics in this path.
- Lemma family operational contract is frozen:
  - `rule_id` format is frozen:
    - `lemma:<lemma_pack_id>@<lemma_pack_version>:<family>:<local_id>`.
  - deterministic `rule_id` prefix convention.
  - deterministic decision `code` convention.
  - deterministic `priority` layout.
  - duplicate emitted `rule_id` fails closed at materialize-time with deterministic lint/conformance error.
- Lemma-pack compilation boundary is frozen:
  - compilation is closed-world and may depend only on:
    - versioned lemma-pack spec,
    - static repo constants,
    - explicit `policy materialize` inputs.
  - deterministic mode compilation may not read runtime state (`connectors`, domain registry, process env).
- Compilation/storage mode is frozen:
  - compile at materialize-time.
  - persist expanded compiled policy as source-of-truth payload in `policy_registry@1`.
  - optional lemma-source metadata is allowed only as non-authoritative lineage evidence.
- Cache/reload behavior must be hash-anchored and replay-safe.
- Cache/reload source-of-truth is frozen to existing governance artifacts:
  - `policy_registry@1` + `policy_activation_log@1`.
  - no secondary file-based fallback source in deterministic mode.
- Cache/reload key semantics are frozen:
  - no TTL/time-based cache invalidation in deterministic/replay mode.
  - cache key is `policy_hash` (optionally `policy_hash + evaluator_version` if evaluator versioning is introduced).
- `policy_lineage@1` linkage contract is frozen:
  - includes `policy_hash`.
  - includes `activation_ref` canonical event ref (for example `event:urm_policy:<profile_id>#<seq>`).
  - may include `lemma_pack_id@version` lineage metadata, non-authoritative only.
- Lint/conformance lock codes are frozen:
  - `URM_POLICY_LINT_FAILED`
  - `URM_POLICY_PROFILE_REGISTRY_INVALID`
- Lint failure evidence event is frozen:
  - `POLICY_LINT_FAILED`
  - appended to governed policy stream context (for profile-scoped operations: `urm_policy:<profile_id>`).
- Policy-language expansion must stay minimal and versioned.

### Acceptance

- Same policy/profile/context inputs produce byte-identical decisions and lineage.
- Cache/reload behavior is deterministic across restart/replay.
- Restart/reload determinism fixture is required:
  - restart with identical active `policy_hash` yields identical decision traces with no reload drift.
- Lemma feasibility proof is required before freeze:
  - the selected deny/require lemma families must be shown as expressible with existing evaluator atoms only.
- Conformance/lint checks fail closed on invalid mappings.

### Risk

- Policy-language scope can expand too quickly without tight locks.

## Path 2: Proof Activation v1 (Trust-Lane Completion)

### Goal

Operationalize `proof_checked` as a first-class production trust path with deterministic evidence.

### Scope

1. Activate end-to-end proof-check flow for a narrow obligation slice.
2. Introduce `proof_evidence@1` with deterministic `proof_hash`.
3. Add replay fixtures and stop-gate proof stability metrics.
4. Add policy/profile controls for when proof checking is required/optional.

### Locks

- Proof failure degrades deterministically (never silent trust promotion).
- Missing proof backend degrades deterministically with stable code/event.
- Proof evidence must be persisted and replay-safe.
- Proof missing/backend error code family is frozen:
  - `URM_PROOF_BACKEND_UNAVAILABLE`
  - `URM_PROOF_EVIDENCE_NOT_FOUND`
- Proof run lifecycle evidence event symmetry is frozen:
  - `PROOF_RUN_PASS`
  - `PROOF_RUN_FAIL`
- Path framing is frozen as operational hardening:
  - normalize/materialize from persisted proof rows first; no requirement to re-run Lean in determinism CI.
- Proof determinism boundary is frozen:
  - deterministic normalization/materialization is guaranteed for identical persisted proof-run records.
  - live proof-backend output determinism is not claimed.
  - replay determinism is grounded to persisted proof evidence, not re-running backend tooling.
- CI reality lock (thin slice) is frozen:
  - required CI determinism checks use persisted golden proof-run fixtures.
  - live Lean/toolchain execution is optional and non-blocking for determinism CI in this path.
- `proof_evidence@1` contract lock is frozen:
  - schema under `spec/`.
  - relationship to existing IR schema is frozen:
    - `adeu.proof_artifact.v0.json` remains IR-layer artifact shape.
    - `proof_evidence@1` is the operational normalized/reporting packet contract derived from persisted proof rows.
  - binding key: `proof_id`.
  - hash anchor: `proof_hash`.
  - includes `proof_evidence_hash = sha256(canonical_json(proof_evidence_without_nonsemantic_fields))`.
  - materialized packet is derived from persisted `proof_artifacts` rows only in deterministic/replay paths.
  - status normalization remains aligned to current proof artifact status set (`proved` | `failed`); backend timeout/error paths are represented as deterministic failure reasons under `failed.reason`.
  - canonical ordering for grouped proof evidence is deterministic (by `theorem_id`, then `proof_id`).
  - duplicate `(theorem_id, proof_id)` within one grouped packet fails closed deterministically.
  - nonsemantic fields excluded from proof-evidence hash are explicitly frozen as a concrete field set in schema (not prose-only implementation notes).
  - preserved provider-native/raw payloads must be marked with `*_raw` and treated as non-semantic.
- Proof runtime budget interaction is frozen:
  - proof-check execution must declare whether it debits existing runtime budget counters or a dedicated proof budget lane; mixed/implicit accounting is not allowed.
- No solver semantics changes to support proof activation.

### Acceptance

- `proof_checked` outcomes are produced end-to-end with evidence for scoped fixtures.
- Replay of proof outcomes is deterministic for identical inputs.
- `proof_evidence@1` validates and hash checks pass.

### Risk

- Toolchain stability and proof latency.

## Path 3: Explainability Productization v1 (API/CLI/UI)

### Goal

Convert existing explain/diff capabilities into a coherent product surface with deterministic contracts.

### Scope

1. `3a` Normalize existing explain/diff endpoints under frozen output contracts.
2. `3a` Add explicit versioned explain artifact schema (`explain_diff@1`).
3. `3a` Add/standardize CLI surfaces for explain/diff parity with API.
4. `3b` Add minimal frontend evidence views:
   - semantic diff
   - conflict witness drilldown
   - policy decision/evidence linkage

### Locks

- Explain/diff outputs remain informational only (non-semantic).
- Contract-first lock is frozen:
  - normalize output envelopes/hashes additively on existing endpoints first.
  - no endpoint reshuffle/rename as a prerequisite for thin-slice delivery.
- `explain_diff@1` minimum linkage contract is frozen:
  - `input_artifact_refs` (sorted canonical refs).
  - canonical `diff_refs` and `witness_refs`.
  - optional `semantics_diagnostics_ref` linkage.
  - optional `validator_evidence_packet_refs` linkage.
  - `explain_hash` over canonical semantic fields.
- Output ordering and hashes must be deterministic and canonical.
- Path split gate is frozen:
  - `3b` UI scope may start only after `3a` API/CLI/schema parity fixtures pass.
- UI remains read-only over API artifacts (no direct DB mutation path).

### Acceptance

- Explain/diff outputs are replay-deterministic and schema-valid.
- API/CLI parity fixtures pass on identical inputs.
- One canonical explain golden fixture is required and frozen for parity checks.
- UI rendering checks are additive:
  - deterministic API/CLI contract pass is required for path completion.
  - minimal UI views are required for planned user-facing thin slice, but may be tracked as a trailing sub-milestone once `3a` gate passes.

### Risk

- UX scope can outrun backend hardening if not kept thin-slice.

## Path 4: Runtime Scale + Recovery v3

### Goal

Increase orchestration throughput and restart resilience while preserving replay determinism.

### Scope

1. Controlled increase to `max_active_children > 1` with deterministic scheduler semantics.
2. Queue and dispatch recovery hardening across restart.
3. Deterministic cancellation/termination propagation under concurrency.
4. Targeted decomposition of high-complexity runtime modules touched by scale work.

### Locks

- Scheduler/recovery must not reorder persisted queue keys.
- Scheduler-decision persistence lock is frozen:
  - persisted scheduler token must include `dispatch_seq` (monotonic) and `lease_id` (stable).
  - replay resolves dispatch ordering from persisted `dispatch_seq`; it may not recompute scheduling decisions.
- Concurrent budget accounting mode is frozen:
  - a single explicit accounting model must be selected and version-locked (`spawn-time reservation` or `runtime running-total`) before `max_active_children > 1` rollout.
  - mixed accounting modes are forbidden.
- Parent-stream interleaving semantics are frozen:
  - parent-visible child lifecycle events under concurrency must include deterministic ordering anchors (`dispatch_seq`, `lease_id`) and replay must preserve persisted order.
- Restart orphan-lease recovery rule is frozen:
  - on restart, any leased-but-not-started dispatch emits deterministic failure event (`WORKER_FAIL`) with reason `lease_orphaned`.
- Runtime scale error family pre-lock is frozen:
  - concurrent scheduling/recovery failures must use explicit `URM_SCHEDULER_*` / `URM_DISPATCH_*` code families (exact codes locked in the arc lock doc).
- Decomposition prerequisite is frozen for scale work:
  - extract high-risk lifecycle methods from `packages/urm_runtime/src/urm_runtime/copilot.py` before or alongside concurrency rollout:
    - `_run_child_workflow_v2`
    - `_spawn_child_v2`
    - `_recover_stale_child_runs`
- Failure paths must be deterministic and evented.
- No best-effort emulation of unavailable runtime capability.
- Concurrency behavior must remain replay-stable.

### Acceptance

- Concurrency/recovery fixtures replay byte-identically across reruns.
- Queue ordering/linkage remains deterministic through restart.
- Budget/termination semantics remain stable under load.

### Risk

- Highest runtime regression surface and debugging complexity.

## Path 5: Semantic Depth v3.1 (Cross-Artifact Reasoning)

### Goal

Improve reasoning quality on top of hardened semantics-v3 operations.

### Scope

1. Thin-slice cap:
   - initial scope is pairwise (two-document) interaction/conflict surfaces only; no N-way cross-document rollout in first slice.
2. Quality/ranking objective uplift with explicit deterministic provenance.
3. Coherence diagnostics expansion with permutation-invariant behavior.
4. Quality dashboard metric uplift tied to locked fixtures.

### Locks

- LLM-derived signals cannot override deterministic evidence dimensions.
- Ranking/score/tie-break versions remain explicit in artifacts.
- Replay mode remains authoritative for acceptance.
- Any optimization/soft-constraint solver extension is deferred unless separately version-locked.

### Acceptance

- Locked eval fixtures show measurable quality improvements with deterministic replay on frozen metrics:
  - `concept_conflict_precision_pct`
  - `concept_conflict_recall_pct`
  - `coherence_permutation_stability_pct`
- Coherence diagnostics remain permutation-invariant.
- No regression on existing semantics-v3 determinism metrics.

### Risk

- Quality work can drift subjective without strong fixture gates.

## Path 6: Portability + Conformance v3

### Goal

Re-validate platform portability under the hardened governance/runtime/semantics stack.

### Scope

1. Expand automated cross-domain conformance coverage and CI gates.
2. Add one compact additional domain pressure test if justified.
3. Prove artifact/taxonomy parity across domains.
4. Publish transfer report v3 with coupling deltas and concrete evidence refs.

### Locks

- `urm_runtime` remains domain-agnostic.
- No domain-specific forks of URM event/error taxonomy.
- Generic runtime primitives require at least two-domain justification.
- Conformance suite remains offline and deterministic.
- Conformance scope boundary is frozen:
  - domain-neutral conformance checks apply to all domains (URM envelope/events, policy/governance flows, replay/idempotency surfaces).
  - ADEU-specific checks remain explicitly scoped (solver-semantics artifacts, proof-obligation semantics, ADEU concept-specific metrics).
- Conformance coverage accountability is frozen:
  - each conformance release must report deterministic coverage metrics for exercised URM event/error/artifact surfaces.
  - adding a new domain pressure test is justified only when coverage deltas or new runtime behaviors are not captured by existing domains.
- New artifact conformance expansion is frozen:
  - as paths land, conformance must explicitly cover cross-domain handling for new domain-neutral artifacts (`policy_lineage@1`, `proof_evidence@1`, `explain_diff@1`) or document deterministic ADEU-only scoping.

### Acceptance

- Multi-domain conformance passes deterministically in CI.
- Import-audit confirms no new domain coupling in runtime core.
- Transfer report is reproducible from persisted artifacts.

### Risk

- Domain expansion and suite maintenance overhead.

## Decision Matrix

### If priority is governance safety and trust-lane completion

- Start with Path 1 + Path 2.

### If priority is immediate user-facing value

- Start with Path 3.

### If priority is throughput under load

- Start with Path 4.

### If priority is reasoning quality depth

- Start with Path 5.

### If priority is platform-thesis portability

- Start with Path 6.

## Recommended Arc Order (Clean Sequence)

1. `vNext+7`: Path 1 (thin slice) + Path 2 (thin slice)
2. `vNext+8`: Path 3 (thin slice, API/CLI first, then minimal UI)
3. `vNext+9`: Path 4 (controlled scale/recovery)
4. `vNext+10`: Path 5 (semantic depth v3.1)
5. `vNext+11`: Path 6 (portability/conformance v3 expansion)

Why this order:

- It secures governance/trust first, then exposes product value, then scales runtime, then deepens reasoning, then re-validates portability at higher maturity.

## Proposed Freeze Candidate (Next Step)

Create `docs/LOCKED_CONTINUATION_vNEXT_PLUS7.md` with:

1. Path 1 thin slice:
   - deny/require lemma minimal set + policy conformance/lint gate
2. Path 2 thin slice:
   - one scoped proof activation flow + `proof_evidence@1`
3. Explicit stop gate for selecting `vNext+8` emphasis:
   - productization-heavy (Path 3) vs runtime-scale-heavy (Path 4)

Suggested measured outcomes:

- policy conformance/lint determinism = `100%` on locked fixtures.
- scoped proof replay determinism = `100%` on locked fixtures.
- policy/proof packet hash stability = `100%`:
  - recomputed canonical hash must match embedded hash on all locked fixtures.
- `vNext+7 -> vNext+8` stop-gate thresholds are frozen:
  - `policy_lint_determinism_pct == 100.0`
  - `proof_replay_determinism_pct == 100.0`
  - `policy_proof_packet_hash_stability_pct == 100.0`
  - if any threshold fails: continue Path 1/2 hardening; do not start Path 3/4.
- no solver-semantics delta and no trust-lane regression.
- all existing `vNext+6` determinism metrics remain at threshold.
