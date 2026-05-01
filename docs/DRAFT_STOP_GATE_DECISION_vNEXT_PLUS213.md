# Draft Stop-Gate Decision vNext+213

Status: proposed gate for `V76-B`.

Authority layer: starter-bundle scaffold, not closeout evidence.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS213.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for `vNext+213` only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS213.md`.
- It must not use `V76-B` to authorize `V76-C`, relation settlement, claim
  truth, ratification, worker assignment, dispatch execution, command
  execution, runtime permission, product authorization, external branch
  activation, PR creation, commit, merge, release, benchmark truth, global
  model selection, living-memory authority, or recursive policy amendment.

## Accept When

- `repo_arbiter_authority_profile@1`,
  `repo_reconciliation_settlement_request@1`,
  `repo_adversarial_relation_review@1`, and
  `repo_reconciliation_gap_scan@1` schemas validate and export cleanly;
- the implementation stays in the repo-description lane unless a later lock
  explicitly selects a different package;
- reference fixtures consume released `V76-A` claim map, relation register,
  and dissent register material as concrete source rows;
- authority profiles separate actor kind from grant source kind;
- allowed actions are review-only and forbidden authority actions are explicit;
- settlement requests reference known `V76-A` rows and remain requests for
  later review, not settlement;
- requested settlement horizons are included in every referenced authority
  profile's allowed relation horizons;
- adversarial review rows require source-bound checked horizons or
  negative-control refs for no-counterevidence claims;
- gap rows preserve product, runtime, release, external branch,
  dispatch-execution, benchmark-truth, and recursive-policy gaps;
- majority agreement remains relation evidence only and cannot become
  correctness;
- reject fixtures prove truth, settlement, ratification, execution, runtime
  permission, product authority, external activation, release, benchmark truth,
  model selection, living-memory authority, and recursive policy amendment
  fail closed;
- focused tests for the new `V76-B` package surface and export-schema parity
  pass;
- `make check` passes before any Python implementation PR is opened.

## Do Not Accept If

- authority profiles treat model, tool, support-doc, or transcript sources as
  truth or settlement authority;
- a settlement request performs settlement, ratification, or truth declaration;
- a settlement request ignores blocking dissent or required adversarial review;
- adversarial no-counterevidence posture lacks checked horizon or
  negative-control refs;
- relation conflict / unclear posture is marked ready without adversarial
  review or carried gaps;
- product, runtime, release, external branch, dispatch-execution, or
  recursive-policy gaps are converted into settlement readiness;
- majority agreement is treated as correctness;
- gap scan rows become implementation priority;
- `V76-B` creates `V76-C` summary / handoff / closeout surfaces;
- any live worker assignment, command execution, dispatch execution, runtime
  action, PR creation, commit, merge, release, product authorization, external
  branch activation, benchmark truth, global model selection, living-memory
  authority, or recursive policy amendment lands in this slice.

## Local Gate

- for this docs-only starter bundle:
  - `make arc-start-check ARC=213`
- before any Python implementation PR:
  - `make check`
