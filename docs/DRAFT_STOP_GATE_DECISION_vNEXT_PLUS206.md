# Draft Stop-Gate Decision vNext+206

Status: proposed gate for `V74-A`.

Authority layer: pre-start scaffold, not closeout evidence.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS206.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the `V74-A` implementation stays inside `packages/adeu_repo_description`;
- schema exports exist for:
  - `repo_operator_projection_case_view@1`
  - `repo_operator_projection_source_index@1`
  - `repo_operator_projection_non_authority_guardrail@1`
- mirror schemas exist under `spec/`;
- deterministic reference fixtures exist under
  `apps/api/fixtures/repo_description/vnext_plus206/`;
- projection source rows bind to concrete `V73-C` sources or explicit absence
  posture;
- case-view rows consume released `V73-C` ledger, operator-signal,
  recommendation, and family closeout substrate;
- visible blocker rows are machine-checkable and cannot be replaced by prose
  notes;
- visible decision state is separated from projection horizon and visible
  authority state;
- product-pressure cases carry product-authority-missing posture unless
  rejected or out of scope;
- model-output comparison cases cannot claim benchmark truth or model
  selection;
- guardrails forbid ratification, adoption, implementation, release, product
  authorization, runtime permission, dispatch, and external contest authority;
- focused tests and the repo Python gate appropriate for implementation changes
  pass before PR;
- closeout later records docs/artifacts evidence and runs the closeout gate.

## Do Not Accept If

- `V74-A` builds a live UI, product workbench, operator command surface, or
  dispatch loop;
- projection rows become ratification, adoption, implementation, release,
  product authorization, runtime permission, dispatch, or external contest
  authority;
- a case view is treated as source truth by itself;
- visual prominence, operator click, transcript text, or dashboard state is
  treated as authority;
- product-pressure cases are marked product-authorized;
- model-output comparison cases are marked benchmark truth or model-selected;
- known source gaps, regressions, dissent, blockers, or authority gaps are
  omitted from visible state or visible blocker rows;
- guardrails have empty forbidden authority lists;
- `V74-B`, `V74-C`, `V75`, or `V43` surfaces land in this slice.

## Local Gate

- for the docs-only starter bundle:
  - `make arc-start-check ARC=206`
- for the later implementation PR:
  - `make check`
