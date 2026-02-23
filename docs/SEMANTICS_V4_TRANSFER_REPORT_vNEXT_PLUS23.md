# Semantics-v4 Transfer Report vNext+23

Deterministic transfer summary generated from fixture-backed vNext+23 semantics-v4 candidate packet/projection artifacts.

```json
{
  "schema": "semantics_v4_transfer_report.vnext_plus23@1",
  "vnext_plus23_manifest_hash": "6ae645e5ce18e62d3a7bde3329eabbced786cdf1d789461e73c6af3a6e3a7ef2",
  "coverage_summary": {
    "coverage_pct": 100.0,
    "covered_surface_count": 2,
    "surface_count": 2,
    "surfaces": [
      {
        "fixture_count": 1,
        "surface_id": "adeu.semantics_v4_candidate.packet"
      },
      {
        "fixture_count": 1,
        "surface_id": "adeu.semantics_v4_candidate.projection"
      }
    ],
    "valid": true
  },
  "candidate_packet_summary": {
    "bridge_pair_count": 1,
    "candidate_packet_fixture_count": 1,
    "comparison_item_count": 4,
    "comparison_counts_by_code": {
      "ASSURANCE_SET_CONTINUITY_REVIEW": 1,
      "REQUEST_FORMULA_HASH_CONTINUITY_REVIEW": 1,
      "STATUS_SET_CONTINUITY_REVIEW": 1,
      "WITNESS_REF_STRUCTURE_REVIEW": 1
    },
    "comparison_counts_by_status": {
      "compatible": 2,
      "drift": 2
    },
    "comparison_counts_by_severity": {
      "high": 1,
      "low": 2,
      "medium": 1
    },
    "trust_invariant_packet_hashes": [
      "826b4e9de3038f701e2751529609e4ba1da9298be7e984aaaeea757d61e74b6a"
    ],
    "baseline_semantics_hashes": [
      "7c85f1802e5a55015917ddd7450b31d3ad348b4a8b26d1efc5e8675574facc67"
    ],
    "candidate_semantics_hashes": [
      "0f1f19dd2d1b71790a12ae7310175392d740c49222356b79efc0dd4cbdb12b68"
    ],
    "required_non_empty_floor": {
      "passed": true,
      "required_comparison_codes_present": [
        "REQUEST_FORMULA_HASH_CONTINUITY_REVIEW",
        "STATUS_SET_CONTINUITY_REVIEW"
      ],
      "required_status_values_present": [
        "compatible",
        "drift"
      ],
      "required_witness_review_present": true,
      "required_witness_drift_present": true,
      "total_comparisons_gt_zero": true
    },
    "valid": true
  },
  "candidate_projection_summary": {
    "candidate_projection_fixture_count": 1,
    "bridge_pair_count": 1,
    "comparison_item_count": 4,
    "comparison_counts_by_code": {
      "ASSURANCE_SET_CONTINUITY_REVIEW": 1,
      "REQUEST_FORMULA_HASH_CONTINUITY_REVIEW": 1,
      "STATUS_SET_CONTINUITY_REVIEW": 1,
      "WITNESS_REF_STRUCTURE_REVIEW": 1
    },
    "comparison_counts_by_status": {
      "compatible": 2,
      "drift": 2
    },
    "comparison_counts_by_severity": {
      "high": 1,
      "low": 2,
      "medium": 1
    },
    "valid": true
  },
  "replay_summary": {
    "all_passed": true,
    "determinism_pct": {
      "artifact_semantics_v4_candidate_packet_determinism_pct": 100.0,
      "artifact_semantics_v4_candidate_projection_determinism_pct": 100.0
    },
    "fixture_counts": {
      "semantics_v4_candidate_packet": 1,
      "semantics_v4_candidate_projection": 1
    },
    "replay_count": 3,
    "replay_unit_counts": {
      "semantics_v4_candidate_packet": 3,
      "semantics_v4_candidate_projection": 3
    },
    "runtime_observability": {
      "bytes_hashed_per_replay": 9260,
      "bytes_hashed_total": 27780,
      "elapsed_ms": 60,
      "total_fixtures": 14,
      "total_replays": 42
    },
    "valid": true
  }
}
```
