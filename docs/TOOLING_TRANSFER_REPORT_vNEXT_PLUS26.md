# Tooling Transfer Report vNext+26

Deterministic transfer summary generated from fixture-backed vNext+26 tooling parity artifacts.

```json
{
  "schema": "tooling_transfer_report.vnext_plus26@1",
  "vnext_plus26_manifest_hash": "b842bb583f951321178f228f017240c269f5d8259adc40004a2ff3294d2bc120",
  "coverage_summary": {
    "coverage_pct": 100.0,
    "covered_surface_count": 2,
    "surface_count": 2,
    "parity_projection": "stop_gate_parity.v1",
    "surfaces": [
      {
        "surface_id": "adeu.tooling.stop_gate_input_model_parity",
        "fixture_count": 1,
        "fixture_ids": [
          "tooling.stop_gate_input_model_parity.case_a"
        ]
      },
      {
        "surface_id": "adeu.tooling.transfer_report_builder_parity",
        "fixture_count": 2,
        "fixture_ids": [
          "tooling.transfer_report_builder_parity.v24.case_a",
          "tooling.transfer_report_builder_parity.v25.case_a"
        ]
      }
    ],
    "valid": true
  },
  "stop_gate_input_model_parity_summary": {
    "artifact_stop_gate_input_model_parity_pct": 100.0,
    "fixture_count": 1,
    "run_count": 3,
    "replay_count": 3,
    "parity_projection": "stop_gate_parity.v1",
    "valid": true
  },
  "transfer_report_builder_parity_summary": {
    "artifact_transfer_report_builder_parity_pct": 100.0,
    "fixture_count": 2,
    "run_count": 6,
    "replay_count": 3,
    "parity_projection": "stop_gate_parity.v1",
    "valid": true
  },
  "s9_trigger_check_summary": {
    "source_stop_gate_metrics_path": "artifacts/stop_gate/metrics_v25_closeout.json",
    "required_metrics": {
      "provider_route_contract_parity_pct": {
        "observed_pct": 100.0,
        "required_pct": 100.0,
        "passes": true
      },
      "codex_candidate_contract_valid_pct": {
        "observed_pct": 100.0,
        "required_pct": 100.0,
        "passes": true
      },
      "provider_parity_replay_determinism_pct": {
        "observed_pct": 100.0,
        "required_pct": 100.0,
        "passes": true
      }
    },
    "all_passed": true,
    "valid": true
  },
  "replay_summary": {
    "all_passed": true,
    "determinism_pct": {
      "artifact_stop_gate_input_model_parity_pct": 100.0,
      "artifact_transfer_report_builder_parity_pct": 100.0
    },
    "fixture_counts": {
      "stop_gate_input_model_parity": 1,
      "transfer_report_builder_parity": 2
    },
    "run_counts": {
      "stop_gate_input_model_parity": 3,
      "transfer_report_builder_parity": 6
    },
    "replay_count": 3,
    "runtime_observability": {
      "elapsed_ms": 69,
      "total_fixtures": 21,
      "total_replays": 75,
      "bytes_hashed_per_replay": 67236,
      "bytes_hashed_total": 201708
    },
    "valid": true
  }
}
```
