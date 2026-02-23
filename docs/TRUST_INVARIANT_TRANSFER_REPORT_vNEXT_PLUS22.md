# Trust-Invariant Transfer Report vNext+22

Deterministic transfer summary generated from fixture-backed vNext+22 trust-invariant packet/projection artifacts.

```json
{
  "schema": "trust_invariant_transfer_report.vnext_plus22@1",
  "vnext_plus22_manifest_hash": "449411ae6665aae84f3561c30c0fc41cf17b79281e5e0ae00be96c6f7de00e24",
  "coverage_summary": {
    "coverage_pct": 100.0,
    "covered_surface_count": 2,
    "surface_count": 2,
    "surfaces": [
      {
        "fixture_count": 2,
        "surface_id": "adeu.trust_invariant.packet"
      },
      {
        "fixture_count": 1,
        "surface_id": "adeu.trust_invariant.projection"
      }
    ],
    "valid": true
  },
  "trust_invariant_packet_summary": {
    "bridge_pair_count": 1,
    "trust_invariant_packet_fixture_count": 2,
    "proof_item_count": 8,
    "proof_counts_by_invariant_code": {
      "CANONICAL_JSON_CONFORMANCE": 2,
      "HASH_RECOMPUTE_MATCH": 2,
      "MANIFEST_CHAIN_STABILITY": 2,
      "REPLAY_HASH_STABILITY": 2
    },
    "proof_counts_by_status": {
      "fail": 1,
      "pass": 7
    },
    "bridge_manifest_hashes": [
      "3f0de140e2078c6f5492a3e6f9b06d0077d166da20c4c00da61152e85c51bb53"
    ],
    "required_non_empty_floor": {
      "passed": true,
      "required_invariant_codes_present": [
        "HASH_RECOMPUTE_MATCH",
        "REPLAY_HASH_STABILITY"
      ],
      "required_fail_status_present": true,
      "total_checks_gt_zero": true
    },
    "valid": true
  },
  "trust_invariant_projection_summary": {
    "trust_invariant_projection_fixture_count": 1,
    "bridge_pair_count": 1,
    "proof_item_count": 4,
    "proof_counts_by_invariant_code": {
      "CANONICAL_JSON_CONFORMANCE": 1,
      "HASH_RECOMPUTE_MATCH": 1,
      "MANIFEST_CHAIN_STABILITY": 1,
      "REPLAY_HASH_STABILITY": 1
    },
    "proof_counts_by_status": {
      "fail": 1,
      "pass": 3
    },
    "valid": true
  },
  "replay_summary": {
    "all_passed": true,
    "determinism_pct": {
      "artifact_trust_invariant_packet_determinism_pct": 100.0,
      "artifact_trust_invariant_projection_determinism_pct": 100.0
    },
    "fixture_counts": {
      "trust_invariant_packet": 2,
      "trust_invariant_projection": 1
    },
    "replay_count": 3,
    "replay_unit_counts": {
      "trust_invariant_packet": 6,
      "trust_invariant_projection": 3
    },
    "runtime_observability": {
      "elapsed_ms": 45,
      "total_fixtures": 12,
      "total_replays": 36,
      "bytes_hashed_per_replay": 5463,
      "bytes_hashed_total": 16389
    },
    "valid": true
  }
}
```
