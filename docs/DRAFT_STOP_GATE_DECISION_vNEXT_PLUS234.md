# Draft Stop-Gate Decision vNext+234

Status: pre-start scaffold decision for `V83-B`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS234.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This pre-start decision is scoped to `vNext+234` / `V83-B` only.
- It does not claim implementation has started or passed.
- It does not redefine the lock in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS234.md`.
- It does not authorize `V83-C`, implementation-spec projection packets,
  intent-to-work-packet handoffs, implementation, code edits, command
  execution, tool invocation, worker dispatch, meta-orchestrator runtime,
  Morphic UX runtime changes, direct OAI runtime behavior, PR creation,
  commit, merge, release, product authorization, graph-memory authority,
  recursive policy amendment, or `V84` selection.

## Starter Decision

The starter bundle is acceptable for implementation drafting if it preserves
the following path:

```text
released V83-A intent / source / guardrail rows
  -> semantic objects and relation rows
  -> validation-need rows
  -> artifact obligation rows
  -> semantic drift / ambiguity rows
  -> later V83-C projection only after V83-B closes
```

The key starter decision is to select only the `V83-B` record shapes:

- `repo_intent_edge_decomposition@1`
- `repo_artifact_obligation_map@1`
- `repo_semantic_drift_ambiguity_register@1`

## Required Pre-Start Inputs

Required planning / support documents:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v73.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_SEMANTIC_IMPLEMENTATION_SPECIFICATION_V83_PLANNING_v0.md`

Required released substrate:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS233.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS233.md`
- `docs/ASSESSMENT_vNEXT_PLUS233_EDGES.md`
- `artifacts/agent_harness/v233/evidence_inputs/v83a_semantic_intent_contract_closeout_evidence_v233.json`
- released `V83-A` reference fixtures and closeout evidence inputs cited by
  the lock.

## Exit Criteria For Future Closeout

The future `vNext+234` closeout decision should be allowed to pass only if:

| Criterion | Required State |
|---|---|
| `V83-B` implementation merged | one ready-for-review PR merged to `main` |
| Package scope | `adeu_repo_description` only unless explicitly justified by the lock |
| Selected surfaces | exactly `repo_intent_edge_decomposition@1`, `repo_artifact_obligation_map@1`, `repo_semantic_drift_ambiguity_register@1` |
| Released `V83-A` substrate | all edge / obligation / drift rows reference known `V83-A` intent, source, and guardrail rows |
| Edge decomposition | semantic objects and relations are source-bound and cannot invent intent |
| Generated spec provenance | model/agent-generated edges remain candidate-only and provenance-bound |
| Validation needs | tests, fixtures, and tool runs are edge-bound evidence requirements, not semantic truth |
| Artifact obligations | obligations map semantic edges to bounded artifact horizons without implementing them |
| Non-goals and authority | non-goals cannot become required changes; authority boundaries cannot become permissions |
| Drift / ambiguity | blocking drift rows cannot be resolved by model prose or hidden behind ready posture |
| Deferred surfaces | no `V83-C` projection packet, handoff, or family closeout rows ship in `V83-B` |
| Verification | focused `V83-B` tests plus export-schema parity pass, and `make check` passes before PR merge |
| Closeout docs/artifacts | docs/artifacts-only closeout bundle passes `make arc-closeout-check ARC=234` |

## Current Decision

- decision: `STARTER_SCAFFOLD_READY_FOR_V83B_IMPLEMENTATION_DRAFTING`
- current authority: pre-start scaffold only
- rationale:
  - `V83-A` has closed on `main` with source-bound intent, source-index, and
    non-implementation guardrail substrate;
  - the `V83` selector already names `V83-B` as the next default candidate
    after `V83-A` closes;
  - the lock selects only edge decomposition, artifact obligation mapping, and
    semantic drift / ambiguity posture;
  - tests, fixtures, model output, support docs, Morphic UX examples, and
    direct OAI profile sources remain review evidence or context, not semantic
    truth or runtime authority;
  - projection packets, work-packet handoffs, implementation, runtime
    behavior, product, release, graph memory, recursive policy amendment, and
    `V84` remain forbidden.

The decision remains non-authoritative until the implementation and closeout
evidence are produced.
