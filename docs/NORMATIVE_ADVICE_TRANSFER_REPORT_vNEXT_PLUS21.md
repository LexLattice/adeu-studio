# Normative Advice Transfer Report vNext+21

Deterministic transfer summary generated from fixture-backed vNext+21 normative-advice packet/projection artifacts.

```json
{
  "schema": "normative_advice_transfer_report.vnext_plus21@1",
  "vnext_plus21_manifest_hash": "6f6d1c66f9facd78c1ca986973b56a7451c533632040af2163ba8e932ae5ec77",
  "coverage_summary": {
    "coverage_pct": 100.0,
    "covered_surface_count": 2,
    "surface_count": 2,
    "surfaces": [
      {
        "fixture_count": 2,
        "surface_id": "adeu.normative_advice.packet"
      },
      {
        "fixture_count": 1,
        "surface_id": "adeu.normative_advice.projection"
      }
    ],
    "valid": true
  },
  "advice_packet_summary": {
    "bridge_pair_count": 1,
    "advice_packet_fixture_count": 2,
    "advice_item_count": 2,
    "advice_counts_by_code": {
      "MAPPING_GAP_REVIEW": 1,
      "SOURCE_DIVERGENCE_REVIEW": 1
    },
    "advice_counts_by_priority": {
      "high": 1,
      "medium": 1
    },
    "bridge_manifest_hashes": [
      "3f0de140e2078c6f5492a3e6f9b06d0077d166da20c4c00da61152e85c51bb53"
    ],
    "required_non_empty_floor": {
      "passed": true,
      "required_codes_present": [
        "MAPPING_GAP_REVIEW",
        "SOURCE_DIVERGENCE_REVIEW"
      ],
      "total_advice_gt_zero": true
    },
    "valid": true
  },
  "advice_projection_summary": {
    "projection_fixture_count": 1,
    "bridge_pair_count": 1,
    "advice_item_count": 1,
    "advice_counts_by_code": {
      "SOURCE_DIVERGENCE_REVIEW": 1
    },
    "advice_counts_by_priority": {
      "high": 1
    },
    "valid": true
  },
  "replay_summary": {
    "all_passed": true,
    "determinism_pct": {
      "artifact_normative_advice_packet_determinism_pct": 100.0,
      "artifact_normative_advice_projection_determinism_pct": 100.0
    },
    "fixture_counts": {
      "normative_advice_packet": 2,
      "normative_advice_projection": 1
    },
    "replay_count": 3,
    "replay_unit_counts": {
      "normative_advice_packet": 6,
      "normative_advice_projection": 3
    },
    "runtime_observability": {
      "elapsed_ms": 57,
      "total_fixtures": 9,
      "total_replays": 27
    },
    "valid": true
  }
}
```
