# Draft Stop-Gate Decision vNext+105

Status: proposed gate for `V45-F`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS105.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the repo releases one canonical `repo_descriptive_normative_binding_frame@1` with
  authoritative and mirrored schema parity;
- the frame binds to one explicit repo snapshot and one explicit bounded source set
  with source-set hash, extraction posture, and extraction method;
- the frame binds consistently to released `V45-A` through `V45-E` descriptive
  artifacts over the same snapshot identity with explicit artifact-local
  source-scope compatibility;
- each binding row preserves explicit distinction between:
  - descriptive input;
  - consumer class;
  - binding posture;
  - authority source;
  - promotion-law posture;
- bounded starter consumer-class doctrine is explicit rather than implementation-soft;
- each binding row carries explicit derivation posture/method and source artifact refs;
- each `descriptive_input_ref` resolves against one of the bound `V45-A` through
  `V45-E` artifacts under the same snapshot identity and artifact-local source-scope
  compatibility posture;
- authority source is necessary but not sufficient for normative promotion;
- promotion-law posture is necessary but not sufficient for normative promotion;
- rows that name advisory-only authority sources cannot be elevated into execution use
  by promotion-law posture alone;
- fail-closed laws reject missing promotion-law posture, unresolved descriptive-input
  refs, source refs outside the declared source set, binding-frame collapse, authority
  laundering, and recursive-execution entitlement;
- the frame remains non-executive and non-approving by itself;
- scoped Python tests cover schema/model validation, deterministic fixture replay,
  cross-artifact binding, and fail-closed rejection.

## Do Not Accept If

- the frame lets descriptive artifacts authorize mutation, scheduling, release gating,
  or recursive execution by themselves;
- optimization findings are overread as amendment entitlement without separate
  authority source;
- rows collapse descriptive input, authority source, and promotion outcome into a
  direct normative shortcut;
- `authority_source_kind` and `promotion_law_posture` can jointly imply execution
  permission without a stronger separate authority source;
- cross-artifact binding to released `V45-A` through `V45-E` surfaces is missing or
  snapshot-inconsistent or source-scope-incompatible;
- `descriptive_input_ref` does not resolve against the bound `V45-A` through `V45-E`
  baseline;
- `source_artifact_refs` are not source-set-membership checked;
- the frame is treated as an execution plan, mutation request, or approval artifact by
  itself;
- the slice widens into automatic repo mutation or recursive execution.

## Local Gate

- run targeted repo-description checks for the changed Python surface once
  implementation begins;
- while the bundle is docs-only, run `make arc-start-check ARC=105`.
