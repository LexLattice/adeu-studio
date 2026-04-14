# Draft Stop-Gate Decision vNext+155

Status: proposed gate for `V57-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS155.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the existing `adeu_agentic_de` package remains the only active implementation
  package for the slice;
- the shipped `V56-A`, `V56-B`, and `V56-C` packet / morph IR /
  interaction-contract / action-proposal / membrane-checkpoint / diagnostics /
  conformance / runtime-state / action-ticket / harvest surfaces are consumed
  unchanged by default, unless one explicit `agentic_de_lane_drift_record@1`
  amendment says otherwise;
- one explicit `agentic_de_lane_drift_record@1` exists before `V57-A` observation
  begins;
- typed models or schemas exist for:
  - `agentic_de_local_effect_observation_record@1`
  - `agentic_de_local_effect_conformance_report@1`
- the first slice selects exactly one actual live class:
  - `local_write`
- the operative interpretation of `local_write` remains the shipped `V56-B`
  `bounded_local_artifact` semantics;
- the first actual-effect subset of `local_write` is narrowed to:
  - `create_new`
  - `append_only`
- destructive, overwrite, rename, delete, and metadata-mutating write kinds remain
  outside the selected first subset;
- one designated local-effect sandbox root is explicit and bounded to:
  - `artifacts/agentic_de/v57/local_effect/`
- one explicit anti-escape sandbox law exists:
  - no symlink escape
  - no parent traversal
  - no indirect alias or mount redirection
  - no write-through into authority-bearing surfaces through sandbox references
- actual observed writes remain inside that designated sandbox root only;
- every observed write binds to:
  - one live ticket
  - one selected action proposal
  - one checkpoint-entitled bounded effect scope
- the starter slice emits explicit:
  - action proposal ref
  - checkpoint ref
  - pre-state ref
  - observed write set
  - post-state ref
  - observed effect
  - boundedness verdict
- the starter slice preserves explicit observation outcomes including:
  - bounded effect observed
  - no effect observed
  - out-of-scope write observed
  - mismatched effect observed
  - boundedness verdict failed
- the new effect-observation outputs remain evidence-bearing only in `V57-A`;
- the new effect-observation outputs do not classify governance hardening or
  restoration policy by themselves in `V57-A`;
- the effect-observation outputs do not change by default:
  - checkpoint semantics
  - ticket-issuance behavior
  - selected live action classes
  - diagnostics semantics
  - exit behavior
- restoration is not selected in `V57-A`;
- hardening register is not selected in `V57-A`;
- Python tests cover:
  - mandatory lane-drift handoff
  - required prior evidence-surface consumption
  - designated sandbox-root enforcement
  - sandbox anti-escape enforcement
  - rejection of writes outside the designated sandbox
  - ticket/proposal/checkpoint binding for every observed write
  - preservation of frozen `local_write` semantics
  - rejection of destructive or overwrite write kinds in the first subset
  - explicit negative observation outcomes
  - no restoration/hardening shipping in the starter slice
  - no delegated/external dispatch or stronger-execute widening.

## Do Not Accept If

- `V57-A` silently redefines shipped `V56` packet/contract/checkpoint/ticket law;
- actual effect escapes the designated sandbox root;
- `V57-A` semantically reinterprets `local_write` into broader repo authority;
- the designated sandbox boundary can be escaped through symlink, traversal, alias, or
  indirect redirection paths;
- observed writes are not attributable to one lawful ticket/proposal/checkpoint scope;
- repo source, lock docs, CI config, secrets, dispatch surfaces, or external paths are
  writable through this slice;
- destructive, overwrite, rename, delete, or metadata-mutating writes are accepted in
  the first selected subset;
- restoration or hardening is claimed without its own later lane;
- `local_reversible_execute`, stronger execute, or delegated/external dispatch are
  widened in this slice;
- one observed effect is treated as immediate hardening authority;
- the slice claims to govern hidden cognition directly;
- speculative internal-state proxies are presented as authoritative effect-governance
  inputs;
- `V57-A` bleeds into product rollout, multi-agent runtime surfaces, or `V48`
  delegated worker ownership.

## Local Gate

- run `make check`
