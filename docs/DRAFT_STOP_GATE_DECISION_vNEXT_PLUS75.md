# Draft Stop-Gate Decision vNext+75

Status: proposed gate for `V39-D`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS75.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `synthetic_pressure_mismatch_fix_plan@1` validates and exports cleanly
  from `packages/adeu_core_ir/schema/` and `spec/`;
- the fix plan consumes the released
  `synthetic_pressure_mismatch_conformance_report@1` substrate without bypassing it
  through raw-subject or repo-wide scanning inputs;
- plan-level source bindings back to the released registry fixture and released
  conformance report fixture are explicit and deterministic;
- forward-agent policy projection and post-optimizer policy projection are structurally
  separate in the artifact;
- projected plan items bind one exact released `source_finding_id` or equivalent exact
  source item identity rather than only a rule-shaped area;
- projected plan items use bounded `plan_posture` and bounded `projection_kind`
  vocabularies rather than fuzzy prose placeholders;
- carried-through rule metadata matches the referenced released registry rule exactly;
- carried-through finding refs match the referenced released conformance report
  exactly;
- projected role guidance may summarize or select from released role policy but may not
  invent contradictory policy;
- exact duplicate projected-item identities inside one fix plan are rejected;
- valid no-op fix plans are accepted for no-finding source reports and for
  findings-present-but-non-plannable source reports;
- safe-autofix plan items are emitted only from released `safe_autofix_candidates`
  rather than synthesized from broader findings;
- `safe_autofix` remains candidate-level only and never becomes an executable payload
  or edit instruction in this slice;
- all plan outputs remain advisory and do not authorize repo mutation;
- the implementation rejects authorship or origin as governed dimensions;
- the fix plan remains anti-score by construction and does not introduce a hidden
  scalar or merge-worthiness field;
- committed local fixtures cover:
  - one positive fix-plan case,
  - one no-op fix-plan case,
  - one rejected invalid plan-input case;
- Python tests cover:
  - schema/model validation,
  - mirrored export parity,
  - deterministic fix-plan replay,
  - no-op fix-plan replay,
  - fail-closed rejection for unauthorized planning routes,
  - duplicate projected-item rejection,
  - anti-authorship boundary preservation,
  - anti-score plan preservation.

## Do Not Accept If

- the slice quietly ships patch generation, file-edit payloads, repo mutation, or
  hybrid oracle execution under the `V39-D` label;
- the fix plan redefines the `V39-B` or `V39-C` vocabulary locally instead of
  consuming released artifacts;
- forward-agent and post-optimizer guidance collapse into one undifferentiated advice
  list;
- projected items carry only loose locator text without an exact released source
  finding identity;
- projected role guidance contradicts the released `forward_agent_policy` or
  `post_optimizer_policy` from the governing registry;
- safe-autofix planning is inferred from non-candidate findings or from findings
  outside the deterministic-local subset;
- the fix plan introduces a hidden priority score, urgency scalar, or automatic
  merge-worthiness signal;
- source inputs depend on live GitHub state, network calls, or implicit repo-wide
  scans.

## Local Gate

- run `make check`
