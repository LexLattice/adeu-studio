# Draft Stop-Gate Decision vNext+139

Status: proposed gate for `V46-D`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS139.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the four new cross-subject comparison contracts validate and export cleanly;
- the committed starter subject pair remains bound to one released Procedural Depth
  stack only;
- subject records stay deterministic and rebind only to released `V46-A`, `V46-B`, and
  `V46-C` refs;
- subject-specific execution-context refs satisfy the frozen compatibility law rather
  than collapsing into one shared execution-context artifact;
- comparison reports and validation reports apply the frozen per-surface comparison law
  for `baseline_structural_fidelity`, `perturbation_non_regression`, and
  `perturbation_validation`;
- comparison reports remain descriptive and non-promotional;
- comparison-validation confirms deterministic comparison over the starter pair;
- targeted tests cover positive subject-pair fixtures and fail-closed incompatibility
  fixtures;
- root `spec/` mirrors match the authoritative package schema exports.

## Do Not Accept If

- the slice emits leaderboard, ranking, routing, role-fit, or training authority;
- the starter comparison jumps into additional benchmark projections;
- subject records or comparison cases silently mix projection spec, execution context,
  baseline instance, or perturbation-bundle refs;
- the implementation treats execution-context identity as stronger than the frozen
  compatibility law for subject-specific starter pairs;
- comparison artifacts collapse per-subject evidence into ambiguous parallel arrays;
- stochastic tolerance or confidence-floor doctrine appears in the starter lane;
- the implementation forks released `V46-B` / `V46-C` scorer law.

## Local Gate

- run `make arc-start-check ARC=139`
