# Cross-IR Coherence Transfer Report vNext+20

Deterministic transfer summary generated from fixture-backed vNext+20 cross-IR bridge/coherence/quality artifacts.

```json
{
  "schema": "cross_ir_transfer_report.vnext_plus20@1",
  "vnext_plus20_manifest_hash": "721c917032a79003c2a4520962a3a0251ce1900cb1f64ba504ffb95e1f4263d9",
  "coverage_summary": {
    "coverage_pct": 100.0,
    "covered_surface_count": 3,
    "surface_count": 3,
    "surfaces": [
      {
        "fixture_count": 1,
        "surface_id": "adeu.cross_ir.bridge_mapping"
      },
      {
        "fixture_count": 1,
        "surface_id": "adeu.cross_ir.coherence_diagnostics"
      },
      {
        "fixture_count": 1,
        "surface_id": "adeu.cross_ir.quality_projection"
      }
    ],
    "valid": true
  },
  "bridge_mapping_summary": {
    "bridge_mapping_version": "adeu_to_concepts.v1",
    "bridge_pair_count": 1,
    "concept_only_count": 1,
    "core_ir_only_count": 11,
    "entries_count": 16,
    "mapped_count": 4,
    "mapping_hash": "5f2a9f84df19e1f8d43167f2d5190054f2cf07f4b0232f918f6e6f95be939eb3",
    "unmapped_concept_count": 1,
    "unmapped_core_ir_count": 11,
    "valid": true
  },
  "coherence_diagnostics_summary": {
    "bridge_manifest_hash": "3f0de140e2078c6f5492a3e6f9b06d0077d166da20c4c00da61152e85c51bb53",
    "coherence_counts_by_code": {
      "MISSING_CONCEPT_MAPPING": 1,
      "MISSING_CORE_IR_MAPPING": 1,
      "SOURCE_HASH_MISMATCH": 1
    },
    "coherence_counts_by_severity": {
      "error": 1,
      "warn": 2
    },
    "coherence_issue_count": 3,
    "required_non_empty_floor": {
      "passed": true,
      "required_codes_present": [
        "MISSING_CONCEPT_MAPPING",
        "MISSING_CORE_IR_MAPPING",
        "SOURCE_HASH_MISMATCH"
      ],
      "total_issues_gt_zero": true
    },
    "valid": true
  },
  "quality_projection_summary": {
    "bridge_pair_count": 1,
    "coherence_counts_by_code": {
      "MISSING_CONCEPT_MAPPING": 1,
      "MISSING_CORE_IR_MAPPING": 1,
      "SOURCE_HASH_MISMATCH": 1
    },
    "coherence_counts_by_severity": {
      "error": 1,
      "warn": 2
    },
    "coherence_issue_count": 3,
    "matches_coherence_summary": true,
    "valid": true
  },
  "replay_summary": {
    "all_passed": true,
    "determinism_pct": {
      "artifact_cross_ir_bridge_mapping_determinism_pct": 100.0,
      "artifact_cross_ir_coherence_diagnostics_determinism_pct": 100.0,
      "artifact_cross_ir_quality_projection_determinism_pct": 100.0
    },
    "fixture_counts": {
      "bridge_mapping": 1,
      "coherence_diagnostics": 1,
      "quality_projection": 1
    },
    "replay_count": 3,
    "replay_unit_counts": {
      "bridge_mapping": 3,
      "coherence_diagnostics": 3,
      "quality_projection": 3
    },
    "runtime_observability": {
      "elapsed_ms": 37,
      "total_fixtures": 6,
      "total_replays": 18
    },
    "valid": true
  }
}
```
