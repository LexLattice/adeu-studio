# Draft Stop-Gate Decision vNext+212

Status: proposed gate for `V76-A`.

Authority layer: starter-bundle scaffold, not closeout evidence.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS212.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for `vNext+212` only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS212.md`.
- It must not use `V76-A` to authorize `V76-B`, `V76-C`, arbiter output as
  truth, worker output as truth, relation settlement, ratification, worker
  assignment, dispatch execution, command execution, runtime permission,
  product authorization, external contest participation, PR creation, commit,
  merge, release, benchmark truth, global model selection, living-memory
  authority, or recursive policy amendment.

## Accept When

- `repo_reconciliation_claim_map@1`,
  `repo_arbiter_relation_register@1`, and
  `repo_reconciliation_dissent_register@1` schemas validate and export cleanly;
- the implementation stays in the repo-description lane unless a later lock
  explicitly selects a different package;
- reference fixtures consume released `V75-C` reconciliation plan, relation
  row, contract, handoff, and family closeout material as concrete source rows;
- source absence is represented as row data, not prose memory;
- claim maps include `claim_kind` / output-claim structure so projected slots
  cannot become observed output-content claims;
- claim maps reference released `V75-C` relation rows as upstream relation
  refs, not newly created `V76-A` arbiter relation rows;
- projected output slots remain distinct from observed worker output refs;
- observed worker output refs require authorized prior-run or support-artifact
  source posture;
- relation register rows remain non-truth and cannot settle claims;
- dissent rows preserve dissent, unknown coverage, and searched absence as
  distinct postures;
- `searched_none_found` dissent rows carry search horizons and checked-source
  coverage;
- product, runtime, release, external branch, dispatch-execution, and
  recursive-policy blockers remain visible;
- reject fixtures prove that arbiter output as truth, worker output as truth,
  settlement, ratification, execution, runtime permission, product authority,
  release, benchmark truth, global model selection, living-memory authority,
  and recursive policy amendment fail closed;
- focused tests for the new `V76-A` package surface and export-schema parity
  pass;
- `make check` passes before any Python implementation PR is opened.

## Do Not Accept If

- the implementation reconstructs `V75-C` relation or handoff state from prose
  memory, model preference, operator vibe, or uncommitted transcript;
- a projected output slot is treated as observed worker output;
- a projected output slot is treated as an observed output-content claim;
- relation refs are ambiguous between upstream `V75-C` relations and new
  `V76-A` arbiter relation rows;
- worker output, model output, relation rows, or arbiter notes are treated as
  truth;
- majority agreement is treated as correctness;
- relation mapping becomes settlement, ratification, implementation priority,
  product authorization, runtime permission, or release truth;
- product / runtime / external branch blockers disappear from the mapped
  relation or dissent state;
- `no dissent recorded` is treated as proof of absence without a searched
  horizon;
- `V76-A` creates `V76-B` authority / settlement surfaces or `V76-C` handoff /
  closeout surfaces;
- any live worker assignment, command execution, runtime action, PR creation,
  commit, merge, release, product authorization, external contest
  participation, benchmark truth, global model selection, living-memory
  authority, or recursive policy amendment lands in this slice.

## Local Gate

- for this docs-only starter bundle:
  - `make arc-start-check ARC=212`
- before any Python implementation PR:
  - `make check`
