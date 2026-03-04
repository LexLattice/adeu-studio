# Locked Continuation vNext+43 (Post-Hoc Lock)

This document captures the implemented arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS42.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS42.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/SEMANTICS_v3.md`

Status: closed lock (post-hoc capture, March 4, 2026 UTC).

Decision basis:

- `vNext+42` (`V32-E`) is merged on `main` via PR `#232`.
- `vNext+43` (`V32-F`) is merged on `main` via PR `#233`.
- `vNext+43` scope is the optional stop-gate metric-key extension described in `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`.
- Arc-completion merge commit for v43 is `8a8a3236476ab29d55cd7d25199a34a5c46decaa`.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes are authorized in this arc.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork.
- Stop-gate keyset continuity pivot for v43 is frozen to additive-only migration:
  - baseline authority: `artifacts/stop_gate/metrics_v42_closeout.json` metrics keys.
  - current authority: `artifacts/stop_gate/metrics_v43_closeout.json` metrics keys.
  - required relation: `baseline_subset_with_required_additions`.
  - required additive keys in v43: exactly `artifact_semantic_compiler_evidence_hash_parity_pct`.
  - removed keys are forbidden.
  - derived cardinality continuity: `79 -> 80`.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion.
- Continuity guards from v36/v37/v38/v39/v40/v41/v42 remain mandatory release preconditions.
- No `L2` boundary release is authorized in this arc.

## Arc Scope (Closed)

This arc closes one thin-slice path:

1. `R1` Add semantic-compiler evidence hash parity metric into stop-gate (`V32-F`).
2. `R2` Add deterministic guard coverage for new manifest and hash-capture fixtures (`V32-F`).

Out-of-scope:

- runtime/provider/proposer boundary changes,
- schema-family fork away from `stop_gate_metrics@1`,
- non-additive stop-gate key churn,
- solver/runtime semantics release changes.

## V32-F Contract Assertion (Machine-Checkable)

```json
{
  "schema": "v32f_metric_extension_contract@1",
  "target_arc": "vNext+43",
  "target_path": "V32-F",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v42_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v43_closeout.json",
  "schema_family": "stop_gate_metrics@1",
  "expected_relation": "baseline_subset_with_required_additions",
  "required_additive_keys": [
    "artifact_semantic_compiler_evidence_hash_parity_pct"
  ],
  "forbidden_removed_keys": true,
  "vnext_plus27_manifest_schema": "stop_gate.vnext_plus27_manifest@1",
  "semantic_compiler_hash_capture_schema": "semantic_compiler_hash_capture@1",
  "hash_profile": "sha256_canonical_json_frozen",
  "replay_count": 3,
  "required_surface_id": "adeu.semantic_compiler.evidence_hashes"
}
```

## Locks (V32-F)

- Additive-key lock:
  - v43 may add only the required semantic-compiler evidence parity metric key.
- Manifest-schema lock:
  - v43 semantic-compiler metric fixtures must validate against `stop_gate.vnext_plus27_manifest@1`.
- Hash-capture lock:
  - baseline/candidate fixtures must validate against `semantic_compiler_hash_capture@1` and frozen canonical hash profile.
- Replay lock:
  - deterministic replay count for v43 semantic-compiler evidence checks is frozen to `3`.
- Gate lock:
  - new gate `artifact_semantic_compiler_evidence_hash_parity` is required and fail-closed.
- Historical compatibility lock:
  - historical closeout artifacts remain parseable without schema-family churn.

## Acceptance (v43 Closeout)

- `artifacts/stop_gate/metrics_v43_closeout.json` is valid and reports `all_passed = true`.
- Keyset relation vs v42 is additive-only with exactly one added key and no removals.
- New v43 metric/gate are deterministic and pass at closeout:
  - metric `artifact_semantic_compiler_evidence_hash_parity_pct = 100.0`
  - gate `artifact_semantic_compiler_evidence_hash_parity = true`
- v36-v42 continuity posture remains unreverted.

## Exit Criteria (Closed)

- `V32-F` merged with green CI on `main`.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Additive key migration is explicit, deterministic, and evidence-backed.
- No boundary-release or solver semantics expansion is introduced.
