# Read Surface Transfer Report vNext+19

Deterministic R2 transfer summary generated from fixture-backed vNext+19 read-surface payloads.

```json
{
  "core_ir_read_surface_summary": {
    "artifact_count": 1,
    "total_edges": 8,
    "total_nodes": 7,
    "valid": true
  },
  "coverage_summary": {
    "coverage_pct": 100.0,
    "covered_surface_count": 3,
    "surface_count": 3,
    "surfaces": [
      {
        "artifact_count": 1,
        "surface_id": "adeu.read_surface.core_ir"
      },
      {
        "artifact_count": 1,
        "surface_id": "adeu.read_surface.lane"
      },
      {
        "artifact_count": 1,
        "surface_id": "adeu.read_surface.integrity"
      }
    ],
    "valid": true
  },
  "integrity_read_surface_summary": {
    "artifact_count": 1,
    "family_issue_totals": {
      "cycle_policy": 2,
      "cycle_policy_extended": 3,
      "dangling_reference": 2,
      "deontic_conflict": 1,
      "deontic_conflict_extended": 2,
      "reference_integrity_extended": 3
    },
    "family_missing_counts": {
      "cycle_policy": 0,
      "cycle_policy_extended": 0,
      "dangling_reference": 0,
      "deontic_conflict": 0,
      "deontic_conflict_extended": 0,
      "reference_integrity_extended": 0
    },
    "family_present_counts": {
      "cycle_policy": 1,
      "cycle_policy_extended": 1,
      "dangling_reference": 1,
      "deontic_conflict": 1,
      "deontic_conflict_extended": 1,
      "reference_integrity_extended": 1
    },
    "valid": true
  },
  "lane_read_surface_summary": {
    "artifact_count": 1,
    "lane_edge_totals": {
      "D": 1,
      "E": 7,
      "O": 0,
      "U": 0
    },
    "lane_node_totals": {
      "D": 1,
      "E": 4,
      "O": 1,
      "U": 1
    },
    "total_lane_projection_edges": 8,
    "valid": true
  },
  "replay_summary": {
    "fixture_counts": {
      "core_ir_read_surface": 1,
      "integrity_read_surface": 1,
      "lane_read_surface": 1
    },
    "replay_count": 1,
    "replay_unit_counts": {
      "core_ir_read_surface": 1,
      "integrity_read_surface": 6,
      "lane_read_surface": 1
    },
    "valid": true
  },
  "schema": "read_surface_transfer_report.vnext_plus19@1",
  "vnext_plus19_manifest_hash": "1091bbbfd92b5fd193dcc9022b4b0632c938c7d2fb3d91cf89129ee99e908caa"
}
```
