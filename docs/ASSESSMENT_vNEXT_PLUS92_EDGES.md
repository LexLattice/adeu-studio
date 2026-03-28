# Assessment vNext+92 Edges

Status: planning-edge assessment for `V42-D`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS92_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Lineage Collapse In Evaluation

- Risk:
  benchmark outputs could be authored against ambient state while claiming released
  `V42-A`/`V42-B`/`V42-C` lineage.
- Response:
  require full released-chain lineage refs and fail closed on any mismatch.

### Edge 2: Artifact Identity Drift (Eval Record vs Benchmark Aggregate)

- Risk:
  a single-run local evaluation record could be treated as benchmark aggregation
  authority.
- Response:
  keep `V42-D` artifact identity explicit as `local_eval_record`; defer true aggregate
  benchmark-manifest semantics to a later continuation arc.

### Edge 3: Task-vs-Adherence Surface Blending

- Risk:
  task success and control-plane adherence could be collapsed into one opaque score.
- Response:
  require separate typed metric surfaces for task success and adherence.

### Edge 4: Adherence-Metric Opaqueness

- Risk:
  control-plane adherence could be emitted as one high-level blob, masking failures.
- Response:
  require decomposed adherence submetric registers and explicit adherence-failure
  registers.

### Edge 5: Evaluation-Provenance Opacity

- Risk:
  evaluation judgments could appear as raw scores without rule-set or basis provenance.
- Response:
  require explicit `evaluation_rule_set_ref`, method-version, basis, and ground-truth
  references.

### Edge 6: Settlement Posture Erasure

- Risk:
  benchmark summaries could hide unresolved ambiguity/claim posture inherited from
  released decomposition/action artifacts.
- Response:
  require explicit settlement-posture checks in benchmark output and reject certainty-only
  laundering.

### Edge 7: Model-Sensitivity Drift

- Risk:
  results from different model classes could be compared without explicit model/run
  identity and profile posture.
- Response:
  require explicit `model_id`, `run_id`, and benchmark-profile identity fields.

### Edge 8: Orthogonality Under-Demonstrated

- Risk:
  doctrine may claim task-success and control-plane adherence are independent without
  explicit fixture evidence.
- Response:
  require explicit 2x2 orthogonality fixture coverage in the starter contract.

### Edge 9: Local-to-Scorecard Authority Leakage

- Risk:
  local benchmark artifacts could start carrying scorecard/replay semantics under neutral
  naming.
- Response:
  keep `V42-D` bounded to local evaluation surfaces and reject scorecard/replay authority
  leakage.

### Edge 10: Leaderboard-Readiness Overclaim

- Risk:
  local-only benchmark results could be laundered into challenge-readiness claims.
- Response:
  reject leaderboard-readiness or competition-readiness claims in `V42-D` artifacts.

### Edge 11: Retroactive Necessity Laundering

- Risk:
  one successful local run could be promoted to universal task-rule necessity.
- Response:
  reject post-hoc necessity overclaim without explicit entitlement evidence.

### Edge 12: Deterministic Replay Claim Inflation

- Risk:
  deterministic replay claims could be interpreted as deterministic model-behavior
  re-generation rather than deterministic evaluation over released artifacts.
- Response:
  explicitly scope replay guarantees to deterministic evaluation over released artifact
  chains and fail closed on replay drift.

## Current Judgment

- `V42-D` is the correct next slice because it evaluates released action/rollout posture
  without widening into scorecard or competition seams.
- The slice is safe only if single-run eval-record identity stays explicit, adherence and
  provenance surfaces are decomposed, orthogonality fixtures are explicit, and
  anti-overclaim posture remains machine-checkable and fail closed.
