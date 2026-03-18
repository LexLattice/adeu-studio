# Draft Stop-Gate Decision vNext+71

Status: proposed gate for `V38-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS71.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new ADEU core schemas validate and export cleanly;
- the committed reference payload compiles deterministically into the same
  brokered execution plan on repeated runs;
- the payload and compiled plan both carry source-doc provenance that matches
  the committed source artifact;
- the active route for the reference fixture is `U -> D -> O -> E`;
- every brokered session packet carries only the approved model set and `xhigh`
  reasoning effort;
- `max_delegation_depth` is reflected in the compiled plan and delegated session
  limits;
- ADEU domain tools expose the new compile operation under the existing URM
  authorization model;
- the thin `/urm/reflex/compile` route returns the same compiled-plan shape as
  the core compiler and remains policy-gated;
- Python tests cover:
  - schema/model validation,
  - committed fixture replay,
  - deterministic canonicalization,
  - domain-tool integration,
  - policy registration for the new actions.

## Do Not Accept If

- any part of the compile path requires non-deterministic prose interpretation
  at runtime;
- model recommendations escape the approved trio;
- the implementation collapses sentinel guardrails into vague narrative without
  machine-readable fields;
- recursive honesty is stated but not represented in typed output;
- source-doc provenance is claimed in docs but missing from the typed artifacts;
- the direct route bypasses capability authorization;
- a parallel `reflexive_governance` family remains exported as if it were part
  of the same slice;
- the new tools bypass existing capability lattice wiring.

## Local Gate

- run `make check`
