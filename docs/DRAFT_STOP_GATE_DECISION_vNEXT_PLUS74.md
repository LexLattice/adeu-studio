# Draft Stop-Gate Decision vNext+74

Status: proposed gate for `V39-C`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS74.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `synthetic_pressure_mismatch_observation_packet@1` validates and exports
  cleanly from `packages/adeu_core_ir/schema/` and `spec/`;
- canonical `synthetic_pressure_mismatch_conformance_report@1` validates and exports
  cleanly from `packages/adeu_core_ir/schema/` and `spec/`;
- committed local subject fixtures deterministically replay into the accepted
  observation packet and accepted conformance report;
- observation packets bind back to the released
  `synthetic_pressure_mismatch_rule_registry@1` substrate without redefining its
  vocabularies;
- each accepted observation packet binds exactly one committed local subject;
- finding entries bind explicit `rule_id`, `signal_kind`, `evidence_regime`,
  `allowed_action`, and `resolution_route` values;
- any carried-through finding metadata matches the referenced released registry rule
  exactly rather than becoming a shadow registry;
- exact duplicate finding identities inside one packet are rejected;
- the implementation executes only the deterministic-local subset in this slice;
- unsupported non-deterministic rules fail closed rather than being silently emitted as
  observed findings;
- the report remains anti-score by construction and does not introduce a hidden scalar
  or merge-worthiness field;
- report aggregation remains count-based and list-based rather than weighted-rollup
  based;
- `safe_autofix_candidates` remain report-level candidates only and do not authorize
  mutation;
- `deterministic_high_severity_findings` remain conformance outputs, not direct merge
  or workflow authority;
- the implementation rejects authorship or origin as governed dimensions;
- subject inputs remain committed local fixtures rather than live network or repo-wide
  discovery surfaces;
- Python tests cover:
  - schema/model validation,
  - mirrored export parity,
  - deterministic packet/report replay,
  - valid no-finding packet/report replay,
  - fail-closed unsupported-regime rejection,
  - duplicate-finding rejection,
  - anti-authorship boundary preservation,
  - anti-score report preservation.

## Do Not Accept If

- the slice quietly ships fix-plan artifacts, repo mutation, or hybrid oracle
  execution under the `V39-C` label;
- the observation packet redefines the `V39-B` rule registry vocabulary locally;
- the detector lane claims contextual, ambiguous, or meta-governance execution as if
  it were already deterministic in this slice;
- a packet bundles multiple subjects or leaves the aggregated packet set implicit in
  the report;
- subject inputs depend on live GitHub state, network calls, or implicit repo-wide
  scans;
- the report introduces a hidden scalar posture or automatic merge-worthiness signal;
- the implementation reintroduces authorship rhetoric into field names, schema law, or
  tests.

## Local Gate

- run `make check`
