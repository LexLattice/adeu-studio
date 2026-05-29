# Draft Stop-Gate Decision vNext+280

Status: post-closeout decision for `BRL-0-C`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS280.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Closeout Decision

`BRL-0-C` is closed on `main`.

The merged slice implemented deterministic impact-cone sentinel selection,
stale-lock reporting, bounded no-regression certificates, and replay
integration handoff records inside `packages/adeu_behavioral_replay_lock`.
The slice consumes released `BRL-0-A` manifests and released `BRL-0-B` replay
execution/diff records. It does not execute replay, generate probes, update
expected hashes, claim product truth, authorize HOB closure, grant OTB
transition legality, claim official-eval readiness, dispatch workers, or select
future families.

## Evidence Source

- implementation PR: `https://github.com/LexLattice/adeu-studio/pull/509`
- merge commit: `c5dfc63541ad910401950bb620e54ed8d988ccfe`
- merged at: `2026-05-29T17:46:20Z`
- implementation commits:
  - `5d1ee8538ee5d439850461cecd7321017ccdf779`
  - `75c034767032c43466c4d58a0b830bdc87fdceb1`
- GitHub CI status:
  - `python`, `lean-formal`, and `web` passed
- closeout evidence input:
  - `artifacts/agent_harness/v280/evidence_inputs/brl_0c_closeout_evidence_v280.json`
- family closeout record:
  - `docs/DRAFT_ADEU_BEHAVIORAL_REPLAY_LOCK_BRL_0_FAMILY_CLOSEOUT_v0.md`

## Verification

```text
.venv/bin/python -m pytest packages/adeu_behavioral_replay_lock/tests -q
.venv/bin/python -m ruff check packages/adeu_behavioral_replay_lock
.venv/bin/python -m adeu_behavioral_replay_lock.export_schema
make check
GitHub CI: python, lean-formal, web
make arc-closeout-check ARC=280
```

Focused package verification on `main` passed with `67` behavioral replay lock
tests. Schema export completed with the existing Pydantic field-shadowing
warnings. The implementation PR ran `make check` before merge, and GitHub CI
passed for the merged PR head.

## Exit Criteria

| Criterion | Status | Evidence |
| --- | --- | --- |
| Impact-cone selection report implemented | passed | `repo_behavioral_impact_cone_selection_report@1` schema and tests |
| No-regression certificate implemented | passed | `repo_behavioral_no_regression_certificate@1` schema and tests |
| Lock staleness report implemented | passed | `repo_behavioral_lock_staleness_report@1` schema and tests |
| Replay integration handoff implemented | passed | `repo_behavioral_replay_integration_handoff@1` schema and tests |
| Selection does not generate probes | passed | impact-cone authority posture and tests |
| Missing sentinel coverage blocks certificate | passed | missing and mixed coverage tests |
| Missing-scope selection emits an explicit known gap | passed | `blocked_by_missing_scope` certificate test |
| Replay diffs block certificates | passed | diff blocker tests |
| Stale locks block certificates | passed | manifest, owner-map, profile, observation, and HOB/OTB staleness tests |
| Staleness report identity is checked | passed | mismatched manifest staleness report test |
| Handoff does not grant transition authority | passed | integration handoff guardrail tests |
| Product, official-eval, worker, and future-family authority remain denied | passed | edge assessment and evidence input |
| Deterministic closeout artifacts exist | passed | v280 stop-gate and agent-harness artifacts |

## Stop-Gate Summary

```json
{
  "schema": "v280_closeout_stop_gate_summary@1",
  "arc": "vNext+280",
  "target_path": "BRL-0-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v279": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 71,
  "runtime_observability_delta_ms": 4
}
```

## Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v279_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v280_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+279",
  "baseline_source": "artifacts/stop_gate/report_v279_closeout.md",
  "baseline_elapsed_ms": 67,
  "current_arc": "vNext+280",
  "current_source": "artifacts/stop_gate/report_v280_closeout.md",
  "current_elapsed_ms": 71,
  "delta_ms": 4
}
```

## Slice Evidence Input

```json
{
  "schema": "brl_0c_closeout_evidence@1",
  "evidence_input_path": "artifacts/agent_harness/v280/evidence_inputs/brl_0c_closeout_evidence_v280.json",
  "runtime_event_stream_path": "artifacts/agent_harness/v280/runtime/evidence/local/urm_events.ndjson",
  "metric_key_continuity_path": "artifacts/agent_harness/v280/evidence_inputs/metric_key_continuity_assertion_v280.json",
  "runtime_observability_comparison_path": "artifacts/agent_harness/v280/evidence_inputs/runtime_observability_comparison_v280.json",
  "family_closeout_record_path": "docs/DRAFT_ADEU_BEHAVIORAL_REPLAY_LOCK_BRL_0_FAMILY_CLOSEOUT_v0.md"
}
```

## Boundary Confirmation

`BRL-0-C` remains a deterministic replay-preservation handoff slice only.

It may:

- select existing sentinel probes from owner-surface scope;
- emit stale-lock rows and required refresh rows;
- emit bounded no-regression certificates over released replay evidence;
- emit integration handoff rows that constrain downstream use.

It may not:

- generate probes or replay commands;
- update expected hashes;
- execute replay;
- patch source code;
- certify product truth;
- authorize HOB closure;
- grant OTB transition legality;
- claim official-eval readiness;
- dispatch workers;
- select future families.

## Recommendation

- gate decision:
  - `BRL_0C_REPLAY_CERTIFICATE_HANDOFF_COMPLETE_ON_MAIN`
- family status:
  - `BRL-0` is closed on `main`.
