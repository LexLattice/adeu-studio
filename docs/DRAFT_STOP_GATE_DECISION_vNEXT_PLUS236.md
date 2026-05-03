# Draft Stop-Gate Decision vNext+236

Status: pre-start scaffold decision for `V84-A`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS236.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This pre-start decision is scoped to `vNext+236` / `V84-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS236.md`.
- It does not use `V84-A` to authorize `V84-B`, `V84-C`, scope contracts,
  target-surface boundary rows, validation evidence plans, exception
  registers, readiness summaries, handoffs, work-packet activation,
  work-packet execution, implementation, code edits, command execution, tool
  invocation, target mutation, worker dispatch, meta-orchestrator runtime
  transition, Morphic UX runtime change, direct OAI runtime behavior, PR
  creation, commit, merge, release, product authorization, graph-memory
  authority, recursive policy amendment, or `V85` selection.

## Pre-Start Evidence Basis

- selected family-level planning:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v74.md`
- architecture / decomposition:
  - `docs/ARCHITECTURE_ADEU_WORK_PACKET_ACTIVATION_REVIEW_FAMILY_v0.md`
- support implementation mapping:
  - `docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84A_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84B_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84C_IMPLEMENTATION_MAPPING_v0.md`
- released source substrate:
  - `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v235/evidence_inputs/v83_family_closeout_alignment_v235.json`
  - `artifacts/agent_harness/v235/evidence_inputs/v83c_semantic_projection_closeout_evidence_v235.json`
  - `apps/api/fixtures/repo_description/vnext_plus235/repo_implementation_spec_projection_packet_v235_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus235/repo_intent_to_work_packet_handoff_v235_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus235/repo_semantic_implementation_spec_family_closeout_alignment_v235_reference.json`
- support dogfood:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_COMBINED_DOGFOOD_TEST_v0.json`

## Starter Gate Criteria

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V84` selected by family selector | required | scaffolded | `docs/DRAFT_NEXT_ARC_OPTIONS_v74.md` |
| `V84-A` selected as first active slice | required | scaffolded | selector says select `V84-A` as the next default candidate |
| Starter scope limited to three `V84-A` surfaces | required | scaffolded | lock emits only request, source index, and guardrail shapes |
| Released `V83-C` substrate identified | required | scaffolded | projection packet, handoff, closeout fixture refs listed |
| Activation review separated from activation authority | required | scaffolded | lock requires non-granting activation authority posture |
| Stable activation-package identity required | required | scaffolded | `activation_package_ref` is required for eligible requests |
| Canonical later-lock requirement typed | required | scaffolded | lock requires canonical lock requirement refs |
| Generated work-packet candidates remain candidate-only | required | scaffolded | generated candidate rows are source/provenance-bound |
| Target and validation posture remain review-only | required | scaffolded | target and validation fields are posture only in `V84-A` |
| Deferred surfaces remain deferred | required | scaffolded | no `V84-B/C` record shapes selected |

## Recommendation

- gate decision:
  - `V84A_STARTER_SCAFFOLD_READY_FOR_REVIEW`
- rationale:
  - the starter lock selects only the bounded `V84-A` request / source-index /
    guardrail seam;
  - the lock consumes released `V83-C` projection, handoff, and closeout
    substrate as review input only;
  - activation review remains distinct from activation authority;
  - stable activation-package identity, typed later-lock requirement,
    generated-candidate provenance, target-family boundary posture, and
    non-execution guardrails are explicit;
  - no implementation work, work-packet execution, code edit, command
    execution, tool invocation, target mutation, PR creation, commit, merge,
    release, product authority, graph authority, recursive policy amendment,
    or `V85` selection is authorized by this starter bundle.
