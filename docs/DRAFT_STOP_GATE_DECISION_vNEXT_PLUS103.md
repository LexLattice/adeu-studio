# Draft Stop-Gate Decision vNext+103

Status: proposed gate for `V45-D`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS103.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `repo_test_intent_matrix@1` schema/model surfaces validate and export with
  authoritative/mirror parity;
- committed reference extraction replays deterministically over one bounded Python test
  source set and one repo-visible snapshot;
- the emitted matrix binds explicit `repo_snapshot_id`, `repo_snapshot_hash`,
  `test_source_set`, and `test_source_set_hash`;
- the emitted matrix binds one explicit `repo_symbol_catalog@1` and one explicit
  `repo_dependency_graph@1` baseline over the same snapshot/source posture;
- each emitted test-intent row is one test-claim/assertion unit and preserves distinct
  fields for:
  - one typed guarded-surface ref;
  - one typed claimed invariant binding;
  - observed assertion surface;
  - invariant domain;
  - gating posture;
  - confidence posture;
  - derivation posture/method;
- internal guarded-surface refs resolve against the bound `V45-B` symbol/dependency
  baseline or use valid typed boundary refs;
- every `source_artifact_ref` resolves inside the declared `test_source_set`;
- reject fixtures fail closed on:
  - unsupported claims without observed assertion support;
  - mismatched `V45-B` snapshot/source binding;
  - untyped guarded-surface refs;
  - authority laundering into release-gating, optimization, scheduling, or mutation
    entitlement;
- Python tests cover schema/model validation, deterministic fixture replay,
  cross-artifact consistency, and the reject-fixture ladder for the new matrix surface.

## Do Not Accept If

- claimed invariant intent is inferred from names or docstrings alone without explicit
  observed assertion support or adjudication;
- the emitted matrix can validate while drifting from the bound `V45-B` snapshot/source
  identity;
- guarded-surface refs are carried as untyped strings;
- one row tries to flatten several claims or assertion surfaces into one coarse record;
- confidence posture or gating posture is used as de facto release authority;
- the implementation silently widens into optimization-register or
  descriptive-to-normative binding surfaces;
- stale-snapshot posture is implied rather than explicit.

## Local Gate

- run `make arc-start-check ARC=103`
