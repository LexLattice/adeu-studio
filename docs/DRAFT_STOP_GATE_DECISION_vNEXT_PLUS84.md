# Draft Stop-Gate Decision vNext+84

Status: proposed gate for `V41-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS84.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- `adeu_architecture_analysis_settlement_frame@1` validates and exports cleanly from
  `packages/adeu_architecture_ir` with byte-identical authoritative and mirrored
  schemas;
- the settlement frame consumes the released `V41-A` request boundary exactly through:
  - `analysis_request_id`
  - `analysis_request_ref`
  - `source_set_hash`
  - `authority_boundary_policy`;
- one explicit `interpretation_register` is present and `chosen_interpretation_id`
  resolves inside it;
- register entries remain explicitly addressable and grounded rather than typed only at
  the top level;
- every interpretation support ref, deontic target, affordance-decision target, claim
  ref, ambiguity ref, escalation support ref, and blocking-lineage ref resolves to
  the released request or to explicit artifacts named by that request;
- `deontic_typing_register` accepts only:
  - `required`
  - `forbidden`
  - `permitted`
  - `optional_hint`
  - `fallback_affordance`;
- `affordance_decisions` accept only:
  - `used`
  - `deferred`
  - `intentionally_declined`
  and any deferred / declined decision carries explicit rationale;
- any request-bound affordance typed as:
  - `permitted`
  - `optional_hint`
  - `fallback_affordance`
  has a corresponding explicit affordance-decision record;
- `claim_posture_register` accepts only:
  - `observed`
  - `inferred`
  - `conjectural`
  - `unentitled_negative_claim`;
- any `unentitled_negative_claim` carries both explicit rationale and bounded-support
  marker;
- `compile_entitlement` is classified as exactly:
  - `entitled`
  - `blocked`;
- `compile_entitlement` means settlement-entitled to proceed to downstream compile,
  not guaranteed downstream compile success;
- `compile_entitlement = entitled` is rejected when:
  - unresolved high-impact ambiguity remains;
  - any active escalation record remains; or
  - any claim posture remains `unentitled_negative_claim`;
- `compile_entitlement = blocked` carries explicit `blocking_lineage`;
- escalation-trigger policy is explicit and active escalation records resolve into it;
- `advisory_notes` remains non-authoritative and cannot introduce new load-bearing
  semantics by prose;
- the settlement lane rejects observation, intended-compile, alignment, remediation,
  and repo-mutation payload drift as out of scope;
- one committed fixture ladder proves deterministic settlement replay over the
  released v83 request boundary;
- Python tests cover:
  - schema/model validation,
  - schema export parity,
  - deterministic settlement replay,
  - request/source-set lineage drift rejection,
  - missing chosen interpretation rejection,
  - deontic / affordance / claim-posture vocabulary rejection,
  - missing rationale rejection,
  - fail-closed entitlement gating.

## Do Not Accept If

- settlement is inferred from free prose instead of an explicit chosen interpretation;
- the frame settles a different repo world than the released v83 request/source-set;
- permissions, optional hints, or fallback affordances are silently promoted into
  obligations;
- request-bound affordances disappear from settlement without an explicit
  affordance-decision record;
- bounded search absence is smuggled in as proved impossibility;
- compile entitlement can become `entitled` while high-impact ambiguity, active
  escalation, or unentitled negative claims remain;
- blocked settlement carries no explicit blocking lineage;
- observed extraction, intended compile, or alignment logic lands in the same slice;
- remediation or repo-mutation instructions appear under the cover of settlement;
- `advisory_notes` becomes the real home for interpretations, blocking reasons, or
  escalation support;
- escalation trigger policy exists only implicitly;
- the lock reopens or weakens the released `V41-A` request boundary.

## Local Gate

- run `make check`
