# Extraction-Fidelity Transfer Report vNext+24

Deterministic transfer summary generated from fixture-backed vNext+24 extraction-fidelity packet/projection artifacts.

```json
{
  "schema": "extraction_fidelity_transfer_report.vnext_plus24@1",
  "vnext_plus24_manifest_hash": "a2d6362a0983754d517b40aaa1d60537da15fa47d95fb9fb17fb964f23a394db",
  "coverage_summary": {
    "coverage_pct": 100.0,
    "covered_surface_count": 2,
    "surface_count": 2,
    "surfaces": [
      {
        "fixture_count": 1,
        "surface_id": "adeu.extraction_fidelity.packet"
      },
      {
        "fixture_count": 1,
        "surface_id": "adeu.extraction_fidelity.projection"
      }
    ],
    "valid": true
  },
  "extraction_fidelity_packet_summary": {
    "source_count": 1,
    "extraction_fidelity_packet_fixture_count": 1,
    "fidelity_item_count": 3,
    "fidelity_counts_by_code": {
      "label_text_mismatch": 1,
      "score_mismatch": 1,
      "span_mismatch": 1
    },
    "fidelity_counts_by_status": {
      "compatible": 1,
      "drift": 2
    },
    "fidelity_counts_by_severity": {
      "high": 1,
      "low": 1,
      "medium": 1
    },
    "projection_alignment_hashes": [
      "5128cc6206fe54a5bf654a6843d55ede63fe35e701e9ea639b3103493640e639"
    ],
    "fidelity_input_hashes": [
      "98991c9b848f2968d651b33a95dd1b6e016a06cac3eb4e188a1d96b1747b80ac"
    ],
    "required_non_empty_floor": {
      "passed": true,
      "required_fidelity_codes_present": [
        "label_text_mismatch",
        "score_mismatch",
        "span_mismatch"
      ],
      "required_status_values_present": [
        "compatible",
        "drift"
      ],
      "required_score_drift_present": true,
      "total_checks_gt_zero": true
    },
    "valid": true
  },
  "extraction_fidelity_projection_summary": {
    "source_count": 1,
    "extraction_fidelity_projection_fixture_count": 1,
    "fidelity_item_count": 3,
    "fidelity_counts_by_code": {
      "label_text_mismatch": 1,
      "score_mismatch": 1,
      "span_mismatch": 1
    },
    "fidelity_counts_by_status": {
      "compatible": 1,
      "drift": 2
    },
    "fidelity_counts_by_severity": {
      "high": 1,
      "low": 1,
      "medium": 1
    },
    "valid": true
  },
  "replay_summary": {
    "all_passed": true,
    "determinism_pct": {
      "artifact_extraction_fidelity_packet_determinism_pct": 100.0,
      "artifact_extraction_fidelity_projection_determinism_pct": 100.0
    },
    "fixture_counts": {
      "extraction_fidelity_packet": 1,
      "extraction_fidelity_projection": 1
    },
    "replay_count": 3,
    "replay_unit_counts": {
      "extraction_fidelity_packet": 3,
      "extraction_fidelity_projection": 3
    },
    "runtime_observability": {
      "elapsed_ms": 48,
      "total_fixtures": 16,
      "total_replays": 48,
      "bytes_hashed_per_replay": 11794,
      "bytes_hashed_total": 35382
    },
    "valid": true
  }
}
```
