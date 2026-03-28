# Stop-Gate Metrics

- Schema: `stop_gate_metrics@1`
- Valid: `True`
- All Passed: `True`
- Arc: `vNext+91`
- Path: `V42-C`
- Runtime elapsed ms: `90`
- Metric-key continuity: `exact_keyset_equality` vs `artifacts/stop_gate/metrics_v90_closeout.json`

## Notes

- v91 closeout preserves the frozen stop-gate schema family and metric keyset.
- v91 introduces the bounded `V42-C` action-proposal and rollout-trace baseline only.
- scorecard/replay/competition seams remain deferred.
