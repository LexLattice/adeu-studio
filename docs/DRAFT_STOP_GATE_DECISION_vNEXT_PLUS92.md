# Draft Stop-Gate Decision vNext+92

Status: proposed gate for `V42-D`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS92.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `adeu_arc_local_eval_record@1` schema validates and exports with
  authoritative/mirrored parity;
- local eval records bind to one released task/observation/hypothesis/action/rollout
  chain with deterministic replay;
- each local eval record carries explicit task-success metrics and explicit
  control-plane-adherence metrics as separate typed surfaces;
- each local eval record carries decomposed adherence submetrics rather than one opaque
  adherence blob;
- each local eval record carries explicit evaluation provenance anchors
  (`evaluation_rule_set_ref`, `evaluation_method_version`, basis refs);
- each local eval record carries explicit `model_id` and `run_id` fields for empirical
  model-sensitivity interpretation;
- each local eval record carries explicit settlement/ambiguity posture checks rather
  than certainty-only summary scoring;
- fixture ladder includes accepted orthogonality matrix coverage across task outcome and
  control-plane adherence:
  - task succeeds + control plane succeeds
  - task succeeds + control plane fails
  - task fails + control plane succeeds
  - task fails + control plane fails
- fixture ladder includes accepted deterministic replay and rejected
  adherence-omission/authority-leakage/overclaim cases;
- Python tests cover schema validation, deterministic replay, and fail-closed rules
  above.

## Do Not Accept If

- local eval records are authored against ambient state while claiming released lineage;
- local eval records collapse task-success and adherence scoring into one opaque metric;
- local eval records omit adherence submetric decomposition or provenance anchors;
- local eval records claim model comparison without explicit per-model identity surfaces;
- local eval records mint scorecard/replay/competition authority from local-only runs;
- local eval records claim leaderboard readiness from local-only evidence;
- local eval records are presented as benchmark aggregation authority despite single-run
  scope;
- local eval records promote one successful local trajectory to universal task-rule
  necessity.

## Local Gate

- run `make arc-start-check ARC=92`
