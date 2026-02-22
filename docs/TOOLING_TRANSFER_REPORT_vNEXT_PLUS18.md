# Tooling Transfer Report vNext+18

This report captures deterministic closeout evidence for vNext+18 tooling parity and CI budget sustainability.

## Evidence Inputs

- Stop-gate closeout JSON: `artifacts/stop_gate/metrics_v18_closeout.json`
- Stop-gate closeout markdown: `artifacts/stop_gate/report_v18_closeout.md`
- Canonical closeout command path:
  - `PYTHONPATH=apps/api/src:packages/urm_runtime/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v18_closeout.json --quality-baseline artifacts/quality_dashboard_v18_closeout.json --out-json artifacts/stop_gate/metrics_v18_closeout.json --out-md artifacts/stop_gate/report_v18_closeout.md`

## Machine-Checkable Payload

```json
{
  "schema": "tooling_transfer_report.vnext_plus18@1",
  "vnext_plus16_manifest_hash": "9696117b034d88b192b1c605da58f4806dcdc20f9c8f9e1bdd972b8ef57777ff",
  "vnext_plus17_manifest_hash": "566d1d0b7f1dd11d64f1aa28bd2ad783436c343d6f92ffe748c37e55e6fbe680",
  "vnext_plus18_manifest_hash": "de1f7fb75d0bc59307ff6de1da5afc4d15b85b2b958d79a35b74c3d5ed6f6da0",
  "validation_parity_summary": {
    "metric_key": "artifact_validation_consolidation_parity_pct",
    "pct": 100.0,
    "threshold": 100.0,
    "passed": true
  },
  "transfer_report_parity_summary": {
    "metric_key": "artifact_transfer_report_consolidation_parity_pct",
    "pct": 100.0,
    "threshold": 100.0,
    "passed": true
  },
  "ci_budget_summary": {
    "metric_key": "artifact_stop_gate_ci_budget_within_ceiling_pct",
    "pct": 100.0,
    "threshold": 100.0,
    "passed": true,
    "elapsed_ms": 45,
    "ceiling_ms": 120000,
    "runtime_observability": {
      "total_fixtures": 3,
      "total_replays": 7
    }
  },
  "replay_summary": {
    "replay_count": 3,
    "total_fixtures": 3,
    "total_replays": 7,
    "all_passed": true
  }
}
```
