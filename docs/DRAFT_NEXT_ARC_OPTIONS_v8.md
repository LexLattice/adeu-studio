# Draft Next Arc Options v8 (Post vNext+47, Post V33 Closure)

This document defines the post-`vNext+47` planning baseline for continued ADEU-governed harness evolution.

Status: active planning draft (`V33-A` through `V33-D` closed; next family selection in progress).

Goal:

- carry forward deterministic, fail-closed, artifact-authoritative harness behavior after V33 closure;
- sequence deferred trust/distribution and verifier-hardening tracks without unlocking unintended boundary releases;
- keep integrated and standalone packaging semantics identical while introducing optional higher-assurance lanes under explicit locks.

This is a planning document only. It is not a lock doc and does not authorize runtime behavior changes.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS47.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS47.md`
- `docs/ASSESSMENT_vNEXT_PLUS47_EDGES.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

## Baseline Agreement (Current Ground Truth)

- Baseline implementation is `vNext+47` (`V33-D`) on `main`.
- `V33-A` through `V33-D` are closed.
- `stop_gate_metrics@1` remains the active stop-gate schema family.
- Stop-gate metric-key cardinality baseline remains `80` (derived from `metrics` object keys only).
- Determinism/replayability, canonical JSON hashing, and fail-closed posture remain mandatory.
- No implicit carryover of metric-key expansion authority is allowed post-v47.

## Planning Boundary (For This Family)

- No solver/runtime semantics contract change is authorized by this planning draft.
- No provider/proposer endpoint expansion is implicitly authorized by this planning draft.
- No implicit `L2` boundary release is authorized; any `L2` candidate requires explicit lock text and dedicated stop-gate posture.
- Packaging mode identity remains frozen:
  - integrated and standalone surfaces must consume identical kernel contracts,
  - adapters cannot redefine policy semantics.

## Naming Convention (New Family)

- `V34-*` identifiers are reserved for single-path families in this planning cycle.
- `B34-*` identifiers are reserved for explicit multi-path bundles.
- `V33-*` remains historical/closed and is not reused.

## Family Scale Note

- `V34` currently defines `7` paths (`V34-A` through `V34-G`) with a default sequential planning span of `vNext+48` through `vNext+54`.
- This sequence is planning intent only; each arc still requires explicit lock/assessment/decision docs before implementation authority is granted.

## Vision Contract (Planning-Level)

- Authoritative sources:
  - lock/decision docs + canonical taskpack/verifier/evidence/packaging artifacts + explicit contract schemas.
- Non-authoritative sources:
  - free-form repository prose and model natural-language self-claims as policy authority.
- Operational rule:
  - higher-assurance lanes (signing, recomputation, attestation) must compose over existing canonical artifacts, not replace artifact authority with prose authority.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "agent_harness_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v7.md",
  "closed_path_family": "V33",
  "closed_paths": [
    "V33-A",
    "V33-B",
    "V33-C",
    "V33-D"
  ],
  "next_path_family": "V34",
  "v34_path_count": 7,
  "v34_default_arc_span": {
    "from": "vNext+48",
    "to": "vNext+54"
  },
  "v34_dependency_edges": [
    {
      "from": "V34-E",
      "to": "V34-A",
      "relation": "requires_trust_anchor_registry_contract"
    }
  ],
  "default_next_arc_candidate": "V34-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality_baseline": 80,
  "no_implicit_metric_key_expansion": true,
  "path_level_metric_key_policy": "no_new_keys_without_explicit_lock_doc_authorization",
  "artifact_authority_model": "canonical_artifacts_only",
  "v34a_signature_envelope_schema": "taskpack_signature_envelope@1",
  "v34a_single_signature_only": true,
  "v34a_signature_subject_default": "taskpack_bundle_hash",
  "v34a_signature_verification_artifact": "signature_verification_result@1",
  "v34a_algorithm_key_binding_required": true,
  "v34b_matrix_lane_resolution": "declared_registry_only",
  "v34b_lane_id_tuple": [
    "deployment_mode",
    "adapter_id",
    "runtime_id"
  ],
  "v34c_recompute_scope": "policy_checks_only",
  "v34c_mismatch_artifact": "policy_recompute_result@1",
  "v34d_retry_payload_content_policy": "references_and_bounded_canonical_artifact_excerpts_only",
  "v34d_retry_excerpt_sanitization_required": true,
  "v34e_attestation_schema": "remote_enclave_attestation@1",
  "v34e_trust_anchor_registry_reuse_required": true,
  "standalone_portability_required": true
}
```

## Harness Diagnostic Namespace (Planning)

- Harness diagnostics remain under `AHK[0-9]{4}` with arc-scoped subsets.
- Existing URM runtime error-code families remain unchanged by this planning draft.

## Path Family V34 (Post-V33 Deferred Continuation)

### Path V34-A: TaskPack Signing + Trust-Anchor Distribution

Lock class: `L1`

Goal:

- add optional artifact authenticity verification over canonical taskpack inputs.

Scope:

- define deterministic signature envelope schema for taskpack artifacts (`taskpack_signature_envelope@1`) as a layer distinct from algorithm policy;
- define v48/V34-A envelope semantics as single-signature only (exactly one signature entry per envelope);
- define signature algorithm policy enum (for example `ed25519`, `p256`) with additive-only extension posture;
- define trust-anchor registry/distribution contract with key identity fields and algorithm binding policy;
- define signature subject policy: sign `taskpack_bundle_hash` as the manifest-authoritative subject and include `taskpack_manifest_hash` as a bound redundant field;
- place signature verification as deterministic pre-flight gate and emit `signature_verification_result@1` for downstream runner/verifier/packaging consumption.

Locks:

- signature verification is additive and must not alter existing semantic authority inputs;
- single-signature envelope posture is frozen for this path; multi-signer verification policy is out of scope;
- signature envelope schema and signature-subject definition are frozen for the path; algorithm enum growth is additive-only;
- trust-anchor identity binding is required: verifier resolves signer key by stable key identifier and enforces exact algorithm pinning for that key; algorithm/key mismatch is a deterministic fail-closed downgrade-protection violation;
- canonical JSON/hash profile remains frozen;
- no new stop-gate metric keys are authorized in this path unless explicitly released in the corresponding lock doc;
- failed signature verification is error-only and fail-closed.

Acceptance:

- identical signed inputs verify deterministically across reruns;
- pre-flight verification emits deterministic `signature_verification_result@1` bytes for identical inputs;
- algorithm downgrade attempts (including algorithm/key mismatch for a registered signer) fail closed deterministically;
- invalid/missing signatures fail closed with deterministic diagnostics.

### Path V34-B: Packaging Adapter Matrix-Lane Parity Checks

Lock class: `L1`

Goal:

- extend V33-D parity checks to a matrix of adapter/runtime combinations while preserving mode identity.

Scope:

- define matrix-lane fixtures for integrated/standalone adapters;
- define matrix lanes from a finite declared registry contract (`adapter_matrix@1`); adapter discovery from local runtime state is non-authoritative;
- freeze lane identity tuple as `(deployment_mode, adapter_id, runtime_id)` with uniqueness required;
- enforce canonical parity + policy-equivalence invariants per lane.

Locks:

- matrix lane cannot relax V33-D parity/policy contracts;
- matrix lane set and ordering must derive from declared registry values only;
- tuple ordering is lexicographic over `(deployment_mode, adapter_id, runtime_id)` for stable parity reporting;
- lane-specific policy overrides are forbidden;
- cryptographic multi-signer quorum/merge-policy governance is out of scope for this path and requires a separate explicitly locked path;
- no new stop-gate metric keys are authorized in this path unless explicitly released in the corresponding lock doc.

Acceptance:

- each enabled lane satisfies canonical parity + policy-equivalence exact-match requirements.

### Path V34-C: Independent Zero-Trust Policy-Validation Recomputation

Lock class: `L1`

Goal:

- add independent policy recomputation in verifier lane to remove transitional trust dependency on runner-recorded validation outcomes.

Scope:

- recompute allowlist/forbidden/operation-kind policy checks from canonical candidate-change-plan + taskpack contracts;
- emit `policy_recompute_result@1` containing runner outcome, recompute outcome, and typed diff summary (including mismatch paths) even on failure;
- compare independent recompute outcome with runner-recorded outcome and fail closed on mismatch.

Locks:

- recompute engine authority derives only from canonical artifacts;
- recomputation scope is policy checks only and excludes test/lint reruns and semantic-diff inference;
- mismatch/failure paths must still emit deterministic `policy_recompute_result@1`;
- no natural-language override lane;
- no new stop-gate metric keys are authorized in this path unless explicitly released in the corresponding lock doc;
- mismatch is error-only and fail-closed.

Acceptance:

- recomputation is deterministic across reruns and detects injected runner-result inconsistencies.
- recomputation evidence artifact (`policy_recompute_result@1`) is deterministic and schema-valid for identical inputs.

### Path V34-D: Rejection-Diagnostic Retry-Context Feeder Automation

Lock class: `L0`

Goal:

- provide deterministic machine-readable retry context from structured diagnostics without policy-authority drift.

Scope:

- derive bounded retry-context payload from rejection diagnostics + canonical artifacts;
- restrict payload content to references plus bounded excerpts already present in canonical artifacts; raw repository file-content inclusion is forbidden;
- apply deterministic sanitization and strict typed encoding to reflected diagnostic excerpts before prompt assembly;
- define frozen sanitization-profile contract for this path (`retry_context_sanitization_profile@1`);
- emit deterministic feeder artifact with frozen schema.

Locks:

- feeder payload is advisory-only and non-authoritative for policy decisions;
- reflected diagnostic text is untrusted input; sanitization profile (length bounds + control-token neutralization + deterministic escaping) is required before any model-facing composition;
- sanitization profile semantics are contract-authoritative via `retry_context_sanitization_profile@1`; ad-hoc sanitizer behavior outside contract is forbidden;
- no new stop-gate metric keys are authorized in this path unless explicitly released in the corresponding lock doc;
- no bypass of primary verification/packaging gates.

Acceptance:

- feeder generation is deterministic and schema-valid for identical inputs;
- sanitized feeder payload excludes disallowed raw control markers under frozen sanitization profile.

### Path V34-E: Remote/Enclave Attested Verifier Execution

Lock class: `L2-candidate`

Goal:

- enable optional attested remote verifier execution while preserving deterministic artifact authority.

Scope:

- define provider-neutral attestation evidence schema (`remote_enclave_attestation@1`) and trust-anchor validation flow for remote verifier output;
- normalize provider-specific attestation formats through adapter mappings into the provider-neutral schema before policy evaluation;
- reuse V34-A trust-anchor registry/distribution contract (or explicit additive extension) rather than introducing a parallel trust-anchor system;
- bind attestation verification to canonical artifact hashes and verifier result artifacts.

Locks:

- no implicit `L2` release; explicit lock text required;
- trust-anchor authority must remain single-source with V34-A compatibility;
- provider-specific attestation PKI details are non-authoritative until normalized into `remote_enclave_attestation@1`;
- no new stop-gate metric keys are authorized in this path unless explicitly released in the corresponding lock doc;
- non-attested or invalid-attestation outputs fail closed.

Acceptance:

- attested and local verifier outputs are contract-equivalent for identical inputs;
- normalized attestation validation remains deterministic for identical provider evidence bytes.

### Path V34-F: Standalone Bundle Integrity Self-Verification

Lock class: `L0`

Goal:

- provide deterministic end-user integrity verification for standalone bundle files.

Scope:

- add deterministic integrity checker (`verify_integrity.py` or equivalent) against packaging manifest inventory + bundle hash.

Locks:

- integrity verifier is manifest-authoritative and must not accept alternate hash subjects;
- no new stop-gate metric keys are authorized in this path unless explicitly released in the corresponding lock doc;
- failure is deterministic and fail-closed.

Acceptance:

- checker reproduces packaging manifest hash results exactly for intact bundles and fails on drift.

### Path V34-G: Optional `remote_enclave` Packaging Deployment Mode

Lock class: `L1`

Goal:

- optionally extend deployment mode set with `remote_enclave` while preserving V33-D mode-identity contracts.

Scope:

- define deterministic mode-selection and adapter boundary for `remote_enclave`;
- require policy-equivalence parity with existing integrated/standalone modes.

Locks:

- deployment mode source remains explicit and deterministic;
- no new stop-gate metric keys are authorized in this path unless explicitly released in the corresponding lock doc;
- mode-specific policy override remains forbidden.

Acceptance:

- `remote_enclave` mode passes canonical parity + policy-equivalence checks under frozen subject set.

## Inter-Path Dependencies (Planning)

1. `V34-E` depends on `V34-A` trust-anchor registry/distribution contracts and cannot be authorized ahead of `V34-A` without explicit replacement lock text.
2. `V34-G` extends V33-D deployment-mode family and must preserve frozen V33-D mode-identity and parity/policy-equivalence invariants.

## Decision Matrix (Post-v47)

| Option ID | Includes | Max lock class | Benefit | Risk |
|---|---|---:|---|---|
| `V34-A` | signing + trust-anchor baseline | `L1` | authenticity lane without semantics churn | medium |
| `B34-AB` | `V34-A + V34-B` | `L1` | authenticity + adapter matrix hardening | high |
| `B34-ABC` | `V34-A + V34-B + V34-C` | `L1` | authenticity + matrix + independent recompute | very high |
| `B34-ABCD` | `V34-A + V34-B + V34-C + V34-D` | `L1` | full local trust/retry hardening bundle | very high |
| `B34-ABCDE` | `V34-A + ... + V34-E` | `L2-candidate` | adds attested remote verifier posture | extreme |

## Recommended Sequencing (Default)

1. `vNext+48`: `V34-A` (taskpack signing + trust-anchor distribution).
2. `vNext+49`: `V34-B` (packaging adapter matrix-lane parity checks).
3. `vNext+50`: `V34-C` (independent zero-trust policy recomputation).
4. `vNext+51`: `V34-D` (retry-context feeder automation).
5. `vNext+52`: `V34-E` (remote/enclave attested verifier execution) under explicit `L2` lock text and after `V34-A` registry stabilization.
6. `vNext+53`: `V34-F` (standalone integrity self-verification utility).
7. `vNext+54`: `V34-G` (optional `remote_enclave` packaging deployment mode).

Portability-first variant (optional):

1. move `V34-F` to `vNext+50` before `V34-C`;
2. shift `V34-C`/`V34-D`/`V34-E` by one arc while preserving lock-class requirements.

Recommendation note:

- if standalone distribution trust/portability is the near-term priority, prefer the portability-first variant to ship `V34-F` earlier as an `L0` hardening lane.

## Proposed First Arc Candidate (`vNext+48`)

Candidate: `V34-A` only (thin-slice, additive hardening).

Suggested PR split:

1. `contracts: add V34-A signing envelope + trust-anchor registry MVP`
2. `tests: add V34-A signing determinism and fail-closed guard suite`

## Continuity and Non-Regression Requirements

- Existing v36-v47 continuity guards remain mandatory and unreverted.
- `stop_gate_metrics@1` remains the only stop-gate schema family unless explicitly re-locked.
- Stop-gate metric-key continuity remains frozen by default (no implicit key additions).
- V33-D integrated/standalone policy-equivalence invariants remain frozen and mandatory.

## Disposition of Deferred V33 Follow-ons

- Deferred non-v47 candidates captured in `LOCKED_CONTINUATION_vNEXT_PLUS47.md` are promoted into explicit V34 planning paths (`V34-A` through `V34-G`).
- Promotion into planning paths does not authorize implementation; lock selection remains required per arc.

## Proposed Next Step

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md` selecting either `V34-A` default or an explicitly justified alternative from this matrix.
2. Draft companion `docs/ASSESSMENT_vNEXT_PLUS48_EDGES.md` and `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS48.md` against the selected `V34` path.
