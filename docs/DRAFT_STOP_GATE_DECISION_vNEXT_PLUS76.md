# Draft Stop-Gate Decision vNext+76

Status: proposed gate for `V39-E`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS76.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `synthetic_pressure_mismatch_oracle_request@1`,
  `synthetic_pressure_mismatch_oracle_resolution@1`, and
  `synthetic_pressure_mismatch_checkpoint_trace@1` validate and export cleanly from
  `packages/adeu_core_ir/schema/` and `spec/`;
- the checkpoint classifier is frozen to exactly:
  - `deterministic_pass`,
  - `deterministic_fail`,
  - `oracle_needed`,
  - `human_needed`;
- `final_adjudication` is frozen to exactly:
  - `resolved_pass`,
  - `resolved_fail`,
  - `escalated_human`;
- legal checkpoint transition law is frozen exactly as:
  - `deterministic_pass -> resolved_pass`
  - `deterministic_fail -> resolved_fail`
  - `oracle_needed -> resolved_pass | resolved_fail | escalated_human`
  - `human_needed -> escalated_human`;
- the deterministic harness remains the only authority over final checkpoint
  adjudication and trace materialization;
- oracle output remains advisory-only and never becomes repo mutation authority, an
  executable edit instruction, or a hidden urgency / merge-worthiness signal;
- `source_kind` is frozen to exactly:
  - `released_conformance_finding`,
  - `released_fix_plan_projection`,
  - `local_hybrid_fixture`;
- checkpoints that derive from released `V39-C` / `V39-D` artifacts bind back to
  those released artifacts exactly rather than only to rule-shaped areas;
- `V39-E` may bind either to released conformance findings or to released fix-plan
  projections depending on checkpoint source surface;
- any local hybrid fixtures used for `oracle_assisted` or `human_only` coverage bind
  back to released registry rule ids and local subject provenance without
  overclaiming themselves as released `V39-C` findings;
- carried-through rule/report/fix-plan metadata matches the referenced released
  upstream artifact exactly whenever such an artifact is referenced;
- `deterministic_only` checkpoints remain fully deterministic in this slice and do not
  emit oracle requests;
- `human_only` checkpoints route directly to `human_needed` and do not emit oracle
  requests;
- `oracle_assisted` checkpoints emit typed oracle request/resolution artifacts only
  under pinned replay identity;
- exact duplicate checkpoint identities, defined from source-kind plus exact source
  binding plus `rule_id` plus `subject_ref` plus local anchor, are rejected;
- oracle request identity pins:
  - source ids,
  - source hashes,
  - policy source hashes,
  - model id,
  - model version,
  - reasoning effort,
  - evaluator or request-template version;
- cache reuse is allowed only for exact replay-identity matches;
- contradictory, unstable, or replay-inconsistent oracle outputs fail closed into
  `human_needed`;
- oracle resolutions may interpret checkpoints but may not mint new rule metadata, new
  subject provenance, or new mutation authority;
- at most one oracle request / resolution cycle is allowed per checkpoint in the first
  baseline;
- committed local fixtures cover:
  - one deterministic checkpoint trace case,
  - one oracle-assisted request/resolution/trace case,
  - one human-only checkpoint trace case,
  - one rejected contradictory or replay-invalid case;
- Python tests cover:
  - schema/model validation,
  - mirrored export parity,
  - deterministic checkpoint replay,
  - oracle-assisted replay,
  - human-only direct escalation,
  - replay/cache identity exact-match enforcement,
  - fail-closed contradictory-resolution handling,
  - single-round oracle enforcement,
  - anti-authorship boundary preservation,
  - anti-score boundary preservation.

## Do Not Accept If

- the slice quietly ships patch generation, file-edit payloads, repo mutation, or
  generic resident-agent orchestration under the `V39-E` label;
- oracle outputs are treated as authoritative decisions rather than advisory inputs to
  deterministic adjudication;
- `final_adjudication` remains soft or unconstrained rather than obeying the frozen
  bounded vocabulary and transition law;
- the checkpoint classifier widens beyond the four frozen classes or adds a silent
  fallback state;
- `source_kind` remains open-ended or implicit rather than fixed to the starter
  vocabulary;
- the lane bypasses released `V39-B` / `V39-C` / `V39-D` artifacts when exact released
  source bindings exist;
- local hybrid fixtures are laundered into fake released observation coverage;
- oracle requests are emitted for checkpoint classes other than `oracle_needed`;
- cache reuse occurs without exact source / policy / model identity equality;
- more than one oracle round trip per checkpoint is permitted in the first baseline;
- contradictory or unstable oracle output is normalized into apparent success;
- oracle resolutions mint new rule metadata, new subject provenance, or new mutation
  authority;
- live GitHub state or live network responses become canonical evaluation evidence;
- the lane reintroduces authorship rhetoric, hidden scores, or merge-worthiness
  outputs.

## Local Gate

- run `make check`
