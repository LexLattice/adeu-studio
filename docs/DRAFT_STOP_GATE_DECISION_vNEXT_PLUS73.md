# Draft Stop-Gate Decision vNext+73

Status: proposed gate for `V39-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS73.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `synthetic_pressure_mismatch_rule_registry@1` validates and exports
  cleanly from `packages/adeu_core_ir/schema/` and `spec/`;
- the committed reference registry fixture revalidates deterministically on repeated
  runs;
- `signal_kind`, `subject_kind`, `evidence_regime`, `allowed_action`,
  `resolution_route`, and `expected_utility_gain` all validate against bounded
  vocabularies rather than free prose;
- `counterexample_policy` is required on every rule entry;
- the implementation rejects authorship or origin as governed dimensions;
- the registry remains anti-score by construction and does not introduce a hidden
  drift scalar or merge-worthiness field;
- `safe_autofix` is blocked for ambiguous, meta-governance, and first-slice
  shape-regularity rules;
- package placement remains `adeu_core_ir` for the first implementation;
- the pressure-mismatch vocabulary remains registry-local and does not mutate or
  overload the `V36-A` same-context glossary;
- Python tests cover:
  - schema/model validation,
  - mirrored export parity,
  - deterministic fixture replay,
  - fail-closed invalid-combination rejection,
  - non-authorship boundary preservation.

## Do Not Accept If

- the implementation reintroduces "AI detector" rhetoric into field names, schema
  law, or tests;
- `expected_utility_gain` is left as open prose in the locked schema;
- the slice quietly ships observation packets, detectors, fix plans, or oracle
  execution under the `V39-B` label;
- the registry invents a free-form summary score or posture scalar;
- registry-local vocabulary is replaced by a new glossary artifact without explicit
  lock text;
- seed rules claim that `oracle_assisted` or `human_only` are already executable
  runtime surfaces instead of planned routing metadata;
- the implementation fragments into multiple overlapping schema families or new
  packages without necessity.

## Local Gate

- run `make check`
