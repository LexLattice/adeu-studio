# Draft Stop-Gate Decision vNext+279

Status: post-closeout decision for `BRL-0-B`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS279.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Closeout Decision

`BRL-0-B` is closed on `main`.

The merged slice implemented deterministic replay execution, canonical
observation capture, expected-vs-actual regression diffs, and suite-root hash
reports inside `packages/adeu_behavioral_replay_lock`. The slice remains
bounded to report-only replay evidence: it may execute already-locked
`BRL-0-A` probe contracts and compare observations, but it may not generate
probes, update expected hashes, select impact-cone sentinels, certify no
regression, claim product truth, or authorize official-eval readiness.

## Evidence Source

- implementation PR: `https://github.com/LexLattice/adeu-studio/pull/508`
- merge commit: `38c484f70344c296832b615698a8e5cea1834e81`
- merged at: `2026-05-29T15:47:34Z`
- implementation commits:
  - `beb7b4ad7b37b4b7373f9d970d02b74d1e1e0990`
  - `aa35b1f9641d08ecdea9acd6af0b430cf3ff1d99`
- post-merge fixture replay repair commit:
  - `8ac4e688`
- GitHub CI run after fixture repair: `26648924828`
- closeout evidence input:
  - `artifacts/agent_harness/v279/evidence_inputs/brl_0b_closeout_evidence_v279.json`

## Verification

```text
.venv/bin/python -m pytest packages/adeu_behavioral_replay_lock/tests -q
.venv/bin/python -m ruff check packages/adeu_behavioral_replay_lock
.venv/bin/python -m adeu_behavioral_replay_lock.export_schema
make check
make test
GitHub CI run 26648924828
make arc-closeout-check ARC=279
```

Focused local package verification passed with `50` behavioral replay lock
tests. The schema export completed with the existing Pydantic field-shadowing
warnings. The post-merge policy-source fixture repair restored full local and
remote gate parity: `make check`, `make test`, and GitHub CI all passed after
the fixture refresh.

## Exit Criteria

| Criterion | Status | Evidence |
| --- | --- | --- |
| Replay execution report implemented | passed | `repo_behavioral_replay_execution_report@1` schema and tests |
| Observation records implemented | passed | `repo_behavioral_observation_record@1` schema and tests |
| Regression diff rows implemented | passed | `repo_behavioral_regression_diff@1` schema and tests |
| Suite-root hash report implemented | passed | `repo_behavioral_suite_root_hash_report@1` schema and tests |
| A manifest validation blocks replay | passed | focused BRL-0-B tests |
| Expected hashes are never silently rewritten | passed | focused BRL-0-B tests |
| Diff rows preserve changed surfaces | passed | focused BRL-0-B tests |
| Suite-root report does not become certificate | passed | edge assessment and non-authority tests |
| Deterministic closeout artifacts exist | passed | v279 stop-gate and agent-harness artifacts |

## Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v278_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v279_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+278",
  "baseline_source": "artifacts/stop_gate/report_v278_closeout.md",
  "baseline_elapsed_ms": 90,
  "current_arc": "vNext+279",
  "current_source": "artifacts/stop_gate/report_v279_closeout.md",
  "current_elapsed_ms": 67,
  "delta_ms": -23
}
```

## Slice Evidence Input

```json
{
  "schema": "brl_0b_closeout_evidence@1",
  "evidence_input_path": "artifacts/agent_harness/v279/evidence_inputs/brl_0b_closeout_evidence_v279.json",
  "runtime_event_stream_path": "artifacts/agent_harness/v279/runtime/evidence/local/urm_events.ndjson",
  "metric_key_continuity_path": "artifacts/agent_harness/v279/evidence_inputs/metric_key_continuity_assertion_v279.json",
  "runtime_observability_comparison_path": "artifacts/agent_harness/v279/evidence_inputs/runtime_observability_comparison_v279.json"
}
```

## Boundary Confirmation

`BRL-0-B` remains a replay and diff slice only.

Deferred to `BRL-0-C`:

- impact-cone sentinel selection;
- bounded no-regression certificates;
- stale-lock invalidation;
- HOB/OTB integration handoff.

Still forbidden outside this family:

- HOB closure changes;
- OTB transition authorization;
- product correctness claims;
- official-eval readiness claims;
- worker dispatch or source patching authority.

## Recommendation

Proceed to `BRL-0-C` with the starter bundle in
`docs/LOCKED_CONTINUATION_vNEXT_PLUS280.md`.
