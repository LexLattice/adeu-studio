# Draft Stop-Gate Decision vNext+275

Status: pre-start scaffold for `OTB-0-A`.

Authority layer: planning scaffold.

This note records the planned closeout decision shape for the `vNext+275`
starter slice. It is not closeout evidence, does not claim the slice has shipped,
and must be updated after implementation and verification before it can become
post-closeout decision evidence.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS275.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This pre-start scaffold is scoped to `vNext+275` / `OTB-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS275.md`.
- It does not authorize semantic adjudication, domain ontology generation, HOB
  closure recomputation, probe generation, probe execution, command execution
  outside the implementation/test lane, worker dispatch, implementation
  batches, product behavior claims, official-eval authority, ProgramBench
  integration, future-family selection, release authority, or recursive policy
  amendment.
- This document must not be treated as post-closeout evidence until the
  implementation PR has merged and deterministic closeout artifacts exist.

## Planned Evidence Source

The post-closeout version of this decision should record:

- merged implementation PR;
- merge commit;
- implementation commits integrated by the merge;
- focused `OTB-0-A` pytest;
- transition-broker schema export pytest;
- `make lint`;
- `make check` or an explicitly justified narrower gate;
- docs/artifacts-only closeout verification with `make arc-closeout-check ARC=275`;
- deterministic closeout artifacts:
  - `artifacts/quality_dashboard_v275_closeout.json`;
  - `artifacts/stop_gate/metrics_v275_closeout.json`;
  - `artifacts/stop_gate/report_v275_closeout.md`;
  - metric-key continuity evidence input;
  - runtime observability evidence input;
  - `OTB-0-A` closeout evidence input;
  - committed runtime event-stream witness.

## Planned Exit-Criteria Check

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `OTB-0-A` merged on `main` | required | implementation PR and merge commit |
| Implementation stays in the transition-broker lane | required | package rooted at `packages/adeu_transition_broker` |
| Selected A surfaces ship | required | six record shapes from the lock |
| Transition claim is first-class | required | `repo_phase_transition_claim@1` models/tests |
| Artifact presence does not imply a transition claim | required | missing-claim fixture fails closed |
| Bridge consistency and completeness are separate | required | consistent-but-incomplete fixture |
| A validation avoids action-authority language | required | `valid_for_broker_frontier` posture only |
| Multi-hash artifact identity is enforced | required | file/canonical/semantic/evidence/obligation hash fixtures |
| Evidence contamination is transitive | required | ancestry fixture fails closed |
| Posture downgrade frontiers are emitted | required | unsupported requested posture fixture |
| Phase-local freshness is enforced | required | stale freshness-basis fixture |
| Silent obligation drops fail closed | required | D-bridge preservation fixture |
| Legal frontier rows deny execution authority | required | frontier authority posture fixture |
| Non-authority guardrail denies semantic/tool/product authority | required | guardrail fixture |
| A does not implement B/C surfaces | required | no closure/gate/baton/delta/handoff APIs |
| Canonical output hashing is stable | required | shuffled input fixture |
| Stop-gate schema-family continuity retained | required | closeout metrics |
| Stop-gate metric-key continuity retained | required | closeout evidence input |

## Pre-Start Recommendation

- gate decision:
  - `GO_OTB_0A_STARTER_IMPLEMENTATION_AFTER_BUNDLE_ACCEPTANCE`
- rationale:
  - `vNext+275` is scoped to one new deterministic package and six A-level
    record surfaces;
  - the slice validates transition claims across O/E/D/U bridges and emits
    legal frontiers;
  - B/C planning, worker dispatch, execution, product authority, and future
    family selection remain explicitly out of scope.

