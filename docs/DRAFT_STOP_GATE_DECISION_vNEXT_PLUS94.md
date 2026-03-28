# Draft Stop-Gate Decision vNext+94

Status: proposed start gate for `V42-F`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS94.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `adeu_arc_submission_execution_record@1` schema/model surfaces are released
  in authoritative and mirrored form with parity checks;
- deterministic entrypoints consume one released
  task/observation/hypothesis/action/rollout/local-eval/scorecard lineage chain and
  emit one deterministic submission execution record;
- lifecycle stages are explicit and fail-closed:
  - authorization is distinct from execution and from result import;
  - status enums and transition matrix are explicit, machine-checkable, and enforced;
  - submitted execution states are rejected without valid authorization surfaces and
    basis refs;
  - submitted-acknowledged states are rejected without receipt refs/hashes;
  - official result-import states are rejected without valid official result authority
    refs/hashes;
- contradictory cross-stage combinations are rejected (for example official result import
  with `not_submitted` execution state);
- payload/request, receipt, and result-import surfaces are hash-bound and
  lineage-bound in accepted artifacts;
- request, receipt, and result import must bind to one external identity chain
  (`external_request_ref`, `environment_ref`, `session_ref`, `competition_scope_ref`);
- time fields are deterministic-evidence sourced only, with monotonic ordering enforced
  when request/receipt/import timestamps are present;
- settlement/ambiguity/claim posture carry is preserved through submission outputs;
- bounded orchestration constraints are explicit as a typed constraint register (not one
  mutually-exclusive enum) while tournament/API/web/operator widening remains deferred;
- committed fixture ladder under `apps/api/fixtures/arc_agi/vnext_plus94/` covers one
  accepted lifecycle ladder (authorized-not-submitted, submitted-acknowledged, official
  result-imported) plus required rejection cases;
- Python tests cover:
  - schema/model validation;
  - authoritative/mirror parity;
  - deterministic accepted fixture replay;
  - rejection of authority laundering;
  - rejection of payload/receipt/result lineage omission;
  - rejection of settlement-posture erasure;
  - rejection of tournament/API/web authority leakage.

## Do Not Accept If

- any submitted execution posture can be emitted without valid authorization surfaces;
- any submitted-acknowledged posture can be emitted without receipt binding;
- any official result-import posture can be emitted without valid official result
  authority refs;
- submission authority relies on prose-only narrative instead of typed authority fields
  and basis refs;
- lifecycle stages allow contradictory combinations or illegal transitions;
- payload, receipt, or result-import lineage/hash identity is missing while completion is
  claimed;
- request/receipt/result records bind to inconsistent external identity chains;
- timestamp fields are synthesized without fixed evidence sourcing or violate monotonic
  ordering;
- settlement carry is dropped when finality or success is asserted;
- one successful submission is used to mint universal necessity or blanket competitiveness
  claims;
- `V42-F` introduces benchmark tournament execution, API/web operator routes, or
  generalized orchestration widening.

## Local Gate

- run `make arc-start-check ARC=94`
