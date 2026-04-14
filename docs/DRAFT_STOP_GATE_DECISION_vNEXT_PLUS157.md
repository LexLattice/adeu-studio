# Draft Stop-Gate Decision vNext+157

Status: proposed gate for `V57-C`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS157.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the existing `adeu_agentic_de` package remains the only active implementation
  package for the slice;
- the shipped `V56-A`, `V56-B`, `V56-C`, `V57-A`, and `V57-B` packet / checkpoint /
  ticket / harvest / observation / conformance / restoration surfaces are consumed
  unchanged by default, unless one explicit `agentic_de_lane_drift_record@1`
  amendment says otherwise;
- one explicit `agentic_de_lane_drift_record@1` exists before `V57-C` hardening
  begins;
- typed models or schemas exist for:
  - `agentic_de_local_effect_hardening_register@1`
- the selected live action class remains exactly:
  - `local_write`
- the operative interpretation of `local_write` remains the shipped `V56-B`
  `bounded_local_artifact` semantics;
- the operative interpretation of the selected restoration exemplar remains exactly:
  - compensating restore of the shipped `V57-A` `create_new` artifact only;
- the designated local-effect sandbox root remains exactly:
  - `artifacts/agentic_de/v57/local_effect/`
- the selected hardening target is narrowed to:
  - the shipped observed and restored `create_new` exemplar only;
- exemplar evidence may not be generalized by default into:
  - class-level conclusions about `local_write`
  - restoration-family law conclusions;
- the starter slice emits explicit:
  - ticket ref
  - action proposal ref
  - checkpoint ref
  - observation ref
  - local-effect conformance ref
  - restoration ref
  - observation boundedness verdict
  - restoration boundedness verdict
  - selected hardening target surface
  - recommended outcome
  - evidence refs
  - reason codes
- committed observation / conformance / restoration fixtures, lane-drift record, and
  closeout evidence outrank narrative interpretation by default;
- hardening assessment depends on boundedness verdicts from both observation and
  restoration, not merely on artifact refs existing;
- the starter slice preserves explicit hardening outcomes including:
  - `keep_warning_only`
  - `needs_more_evidence`
  - `candidate_for_later_local_hardening`
  - `not_selected_for_escalation`
- `candidate_for_later_local_hardening` may nominate only a later bounded evaluation
  target and does not identify the scope of later hardening unless a later lock types
  and selects that scope explicitly;
- the starter slice rejects forbidden hardening outcomes including:
  - `gate_now`
  - `sandbox_widen_now`
  - `broader_write_now`
  - `restoration_generalize_now`
  - `dispatch_now`
  - `ci_required_now`
- the new hardening outputs remain advisory-only and candidate-only in `V57-C`;
- the hardening register remains a path-level advisory surface, not a family-wide
  migration surface;
- the new hardening outputs do not change by default:
  - checkpoint semantics
  - ticket-issuance behavior
  - selected live action classes
  - selected restoration exemplar semantics
  - observation/conformance semantics
  - restoration semantics
  - diagnostics semantics
  - exit behavior
- observation evidence and restoration evidence remain distinct from hardening
  suggestion in the starter slice;
- the hardening register records:
  - target path
  - evidence basis
  - boundedness/conformance summary
  - recommendation outcome
  but does not treat recommendation as an attribute of the evidence itself;
- one observed/restored effect does not by itself nominate:
  - checkpoint change
  - ticket change
  - class widening
  - sandbox widening
  - entitlement widening
- Python tests cover:
  - mandatory lane-drift handoff
  - required prior evidence-surface consumption
  - designated sandbox-root reuse
  - preservation of frozen `local_write` semantics
  - preservation of the frozen selected restoration exemplar
  - advisory-only and candidate-only hardening outputs
  - rejection of live-behavior mutation by default
  - committed lane artifacts outranking narrative docs
  - rejection of checkpoint/ticket mutation in the starter slice
  - rejection of restoration-law widening in the starter slice
  - rejection of stronger-execute or delegated/external-dispatch widening
  - no hidden-cognition proxy authority basis.

## Do Not Accept If

- `V57-C` silently redefines shipped `V56`, `V57-A`, or `V57-B`
  packet/contract/checkpoint/ticket/observation/restoration law;
- hardening is derived mainly from narrative docs instead of committed observation,
  conformance, restoration, lane-drift, and closeout evidence;
- `V57-C` semantically reinterprets `local_write` into broader repo authority;
- `V57-C` semantically reinterprets the shipped `V57-B` restoration exemplar into
  broader destructive or append-only restoration authority;
- the selected hardening target drifts from the shipped observed/restored
  `create_new` exemplar into a broader path set;
- one exemplar is used to justify class-level conclusions about `local_write` or
  restoration-family law without a later explicit lock;
- one observed or restored effect is treated as immediate hardening authority;
- the hardening register itself is used to nominate live checkpoint, ticket, class,
  sandbox, or entitlement changes;
- repo source, lock docs, CI config, secrets, dispatch surfaces, or external paths
  become writable through this slice;
- stronger execute, broader repo-write authority, restoration generalization, or
  delegated/external dispatch are widened in this slice;
- the slice claims to govern hidden cognition directly;
- speculative internal-state proxies are presented as authoritative hardening inputs;
- `V57-C` bleeds into product rollout, multi-agent runtime surfaces, or `V48`
  delegated worker ownership.

## Local Gate

- run `make check`
