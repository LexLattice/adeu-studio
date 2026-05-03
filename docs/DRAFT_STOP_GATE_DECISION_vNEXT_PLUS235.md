# Draft Stop-Gate Decision vNext+235

Status: pre-start scaffold decision for `V83-C`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS235.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This pre-start decision is scoped to `vNext+235` / `V83-C` only.
- It does not claim implementation has started or passed.
- It does not redefine the lock in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS235.md`.
- It does not authorize implementation, code edits, command execution, tool
  invocation, worker dispatch, work-packet execution, meta-orchestrator
  runtime, Morphic UX runtime changes, direct OAI runtime behavior, PR
  creation, commit, merge, release, product authorization, graph-memory
  authority, recursive policy amendment, or `V84` selection.

## Starter Decision

The starter bundle is acceptable for implementation drafting if it preserves
the following path:

```text
released V83-A intent / source / guardrail rows
  -> released V83-B semantic edge / obligation / drift rows
  -> implementation-spec projection packet
  -> review checklist and quality gate posture
  -> intent-to-work-packet handoff for later review only
  -> V83 family closeout alignment without V84 selection
```

The key starter decision is to select only the `V83-C` record shapes:

- `repo_implementation_spec_projection_packet@1`
- `repo_intent_to_work_packet_handoff@1`
- `repo_semantic_implementation_spec_family_closeout_alignment@1`

## Required Pre-Start Inputs

Required planning / support documents:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v73.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_SEMANTIC_IMPLEMENTATION_SPECIFICATION_V83_PLANNING_v0.md`

Required released substrate:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS233.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS233.md`
- `docs/ASSESSMENT_vNEXT_PLUS233_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS234.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS234.md`
- `docs/ASSESSMENT_vNEXT_PLUS234_EDGES.md`
- `artifacts/agent_harness/v233/evidence_inputs/v83a_semantic_intent_contract_closeout_evidence_v233.json`
- `artifacts/agent_harness/v234/evidence_inputs/v83b_semantic_edge_obligation_closeout_evidence_v234.json`
- released `V83-A` and `V83-B` reference fixtures and closeout evidence inputs
  cited by the lock.

## Exit Criteria For Future Closeout

The future `vNext+235` closeout decision should be allowed to pass only if:

| Criterion | Required State |
|---|---|
| `V83-C` implementation merged | one ready-for-review PR merged to `main` |
| Package scope | `adeu_repo_description` only unless explicitly justified by the lock |
| Selected surfaces | exactly `repo_implementation_spec_projection_packet@1`, `repo_intent_to_work_packet_handoff@1`, `repo_semantic_implementation_spec_family_closeout_alignment@1` |
| Released `V83-A/B` substrate | projection, handoff, and closeout rows reference known released intent, edge, obligation, drift, source, and guardrail rows |
| Projection packet provenance | model / agent / mixed projection rows remain candidate-only and provenance-bound |
| Checklist / quality gate | ready posture requires source binding, non-goal preservation, authority boundaries, bounded target surfaces, edge coverage, validation evidence, reject fixtures, generated-spec provenance, drift checks, and future-family boundary checks |
| Drift preservation | blocking drift cannot be hidden by ready posture |
| Implementation spec rows | rows reference known artifact obligations and bounded target surfaces |
| Work-packet handoff | handoff requires later lock authority and remains review-only |
| Deferred surfaces | no implementation, runtime transition, Morphic UX runtime change, direct OAI runtime behavior, product, graph, release, recursive policy, or `V84` selection ships in `V83-C` |
| Verification | focused `V83-C` tests plus export-schema parity pass, and `make check` passes before PR merge |
| Closeout docs/artifacts | docs/artifacts-only closeout bundle passes `make arc-closeout-check ARC=235` |

## Current Decision

- decision: `STARTER_SCAFFOLD_READY_FOR_V83C_IMPLEMENTATION_DRAFTING`
- current authority: pre-start scaffold only
- rationale:
  - `V83-A` and `V83-B` have closed on `main` with source-bound intent,
    semantic edge, artifact obligation, and drift substrate;
  - the `V83` selector already names `V83-C` as the next default candidate
    after `V83-B` closes;
  - the lock selects only projection packet, intent-to-work-packet handoff,
    and family closeout alignment posture;
  - projection packets, quality gates, and handoffs remain review artifacts,
    not implementation authority;
  - implementation, runtime behavior, product, release, graph memory,
    recursive policy amendment, and `V84` remain forbidden.

The decision remains non-authoritative until the implementation and closeout
evidence are produced.
