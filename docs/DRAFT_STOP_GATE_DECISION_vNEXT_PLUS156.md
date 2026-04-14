# Draft Stop-Gate Decision vNext+156

Status: proposed gate for `V57-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS156.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the existing `adeu_agentic_de` package remains the only active implementation
  package for the slice;
- the shipped `V56-A`, `V56-B`, `V56-C`, and `V57-A` packet / checkpoint / ticket /
  harvest / observation / conformance surfaces are consumed unchanged by default,
  unless one explicit `agentic_de_lane_drift_record@1` amendment says otherwise;
- one explicit `agentic_de_lane_drift_record@1` exists before `V57-B` restoration
  begins;
- typed models or schemas exist for:
  - `agentic_de_local_effect_restoration_record@1`
- the selected live action class remains exactly:
  - `local_write`
- the operative interpretation of `local_write` remains the shipped `V56-B`
  `bounded_local_artifact` semantics;
- the designated local-effect sandbox root remains exactly:
  - `artifacts/agentic_de/v57/local_effect/`
- replay is defined narrowly:
  - bounded recomputation and re-evaluation of the restoration event against the prior
    observed-effect lineage only
  - not general re-execution of arbitrary prior live actions
- the selected restoration exemplar is narrowed to:
  - compensating restore of the shipped `V57-A` `create_new` artifact only;
- reuse of the `V57-A` observation subset does not imply restoration eligibility for
  every observed subset member;
- append-only restoration remains outside the selected first restoration subset;
- general delete, overwrite, rename, truncate, and metadata-mutating write authority
  remain outside the selected live-class interpretation;
- one explicit anti-escape sandbox law exists:
  - no symlink escape
  - no parent traversal
  - no indirect alias or mount redirection
  - no write-through into authority-bearing surfaces through sandbox references
- restoration requires:
  - one prior `bounded_effect_observed` outcome
  - one prior observation ref
  - one prior conformance ref
  - one lawful ticket / proposal / checkpoint lineage reused from the observed path
  - one explicit bounded compensating scope derived and matched fail-closed from that
    lineage
- the original ticket does not act as ambient ongoing authority for later writes;
- the starter slice emits explicit:
  - observation ref
  - conformance ref
  - ticket ref
  - action proposal ref
  - checkpoint ref
  - restoration pre-state ref
  - restoration observed write set
  - restoration post-state ref
  - restoration effect
  - restoration boundedness verdict
- restoration pre-state and post-state remain scoped to the designated sandbox effect
  region only;
- the starter slice preserves explicit restoration outcomes including:
  - restoration effect observed
  - no restoration effect observed
  - restoration out-of-scope write observed
  - restoration mismatched effect observed
  - restoration boundedness verdict failed
- the new restoration outputs remain evidence-bearing only in `V57-B`;
- the new restoration outputs do not classify governance hardening by themselves in
  `V57-B`;
- the restoration record may not itself nominate policy, class, or entitlement
  changes;
- the restoration outputs do not change by default:
  - checkpoint semantics
  - ticket-issuance behavior
  - selected live action classes
  - observation/conformance semantics
  - diagnostics semantics
  - exit behavior
- hardening register is not selected in `V57-B`;
- Python tests cover:
  - mandatory lane-drift handoff
  - required prior evidence-surface consumption
  - designated sandbox-root reuse
  - sandbox anti-escape enforcement
  - rejection of restoration writes outside the designated sandbox
  - required prior observation/conformance lineage
  - preservation of frozen `local_write` semantics
  - rejection of append-only restoration in the first restoration slice
  - rejection of general delete/overwrite authority under cover of restore
  - explicit negative restoration outcomes
  - no hardening shipping in the starter slice
  - no delegated/external dispatch or stronger-execute widening.

## Do Not Accept If

- `V57-B` silently redefines shipped `V56` or `V57-A` packet/contract/checkpoint/ticket
  law;
- restoration escapes the designated sandbox root;
- `V57-B` semantically reinterprets `local_write` into broader repo authority;
- the designated sandbox boundary can be escaped through symlink, traversal, alias, or
  indirect redirection paths;
- restoration writes are not attributable to one lawful observed ticket/proposal/
  checkpoint scope;
- the original ticket is treated as ambient ongoing authority for arbitrary later
  writes;
- repo source, lock docs, CI config, secrets, dispatch surfaces, or external paths are
  writable through this slice;
- append-only restoration is accepted in the first selected restoration subset;
- general delete, overwrite, rename, or truncate authority is shipped as if it were
  ordinary `local_write` law;
- hardening is claimed without its own later lane;
- `local_reversible_execute`, stronger execute, or delegated/external dispatch are
  widened in this slice;
- one restoration effect is treated as immediate hardening authority;
- the restoration record itself is used to nominate policy, class, or entitlement
  changes;
- the slice claims to govern hidden cognition directly;
- speculative internal-state proxies are presented as authoritative
  restoration-governance inputs;
- `V57-B` bleeds into product rollout, multi-agent runtime surfaces, or `V48`
  delegated worker ownership.

## Local Gate

- run `make check`
