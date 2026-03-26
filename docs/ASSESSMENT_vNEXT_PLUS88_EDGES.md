# Assessment vNext+88 Edges

Status: planning-edge assessment for `V41-F`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS88_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true,
  "notes": "This pre-lock assessment is a starter-bundle planning artifact and will be superseded by post-closeout edge disposition."
}
```

## Open Edges

### Edge 1: Runner as Hidden Reconciler

- Risk:
  the runner could silently collapse intended and observed lanes into one blended
  truth surface while claiming to be orchestration-only.
- Response:
  keep request plus settlement as the normative driver of intended truth, treat
  observation as constraining companion evidence only, and forbid merged-truth
  reconciliation inside the run manifest.

### Edge 2: Settlement-Blocked Stop Laundering

- Risk:
  a settlement-blocked world could still emit shadow intended or alignment artifacts
  that look almost authoritative.
- Response:
  freeze exact stop behavior: a blocked run stops after observation and emits no
  `semantic_ir_ref`, no `alignment_report_ref`, and no artifact-shaped shadows under
  the released family names.

### Edge 3: Runner Blocked vs Alignment Blocked Confusion

- Risk:
  later users could confuse a completed run whose alignment report is `blocked` with
  a runner-level blocked stop before intended/alignment emission.
- Response:
  keep `run_outcome` / `stop_reason_kind` first-class in the run manifest and require
  a fixture that proves a completed run may still carry an emitted alignment report
  whose posture is `blocked`.

### Edge 4: Non-Deterministic Output Placement

- Risk:
  the same practical run could emit the right artifacts into different paths or in
  different orders across reruns, weakening replay and closeout diffing.
- Response:
  freeze deterministic `output_root_ref`, `runtime_evidence_root_ref`, and canonical
  `emitted_artifact_refs` ordering, and derive `run_id` only from canonical run
  inputs plus frozen runner configuration.

### Edge 5: Stage-Ledger Drift

- Risk:
  blocked-stop replay could become prose-shaped if the manifest does not carry a
  typed execution ledger for which stages actually completed.
- Response:
  require canonical `stage_statuses` over request, settlement, observation, intended,
  alignment, and manifest, and force blocked runs to mark intended/alignment as
  `not_run`.

### Edge 6: Upstream Seam Drift Inside the Runner

- Risk:
  the runner could silently recompute settlement entitlement, reinterpret alignment,
  or reopen request/source-set scope while claiming to consume the released stack.
- Response:
  require exact reuse of the released `V41-A` through `V41-E` seams and reject local
  recomputation of settlement or alignment authority.

### Edge 7: Repo-Mutation or Remediation Creep

- Risk:
  practical orchestration could overreach into patch generation, remediation plans,
  or code-edit authority because it has all the upstream analysis artifacts in hand.
- Response:
  keep the run manifest lineage-only, forbid remediation and repo-mutation fields,
  and keep direct code-change authority out of the runner surface.

### Edge 8: Runtime Evidence Overclaim

- Risk:
  runtime evidence streams could start acting like the real source of truth for
  artifact validity instead of provenance-only continuity evidence.
- Response:
  keep runtime evidence required but informational-only and make the typed released
  artifacts plus fixture replay the gate-relevant truth.

### Edge 9: Orchestration Widening Beyond One Repo Scope

- Risk:
  the first runner baseline could widen into multi-repo or fleet orchestration before
  one bounded repo/subtree loop is actually frozen.
- Response:
  keep the first slice to one bounded repo scope only and defer any broader
  orchestration model to later arcs.

## Current Judgment

- `V41-F` is worth implementing now because it is the only remaining default seam in
  the practical-analysis family and it can habitualize the released `V41-A` through
  `V41-E` stack without reopening prior contracts.
- The starter bundle addresses the highest-risk edges directly:
  lane collapse, settlement-blocked shadow emission, runner-vs-alignment blocked
  confusion, run/stage identity drift, output non-determinism, and mutation creep
  are all explicitly frozen as fail-closed boundaries.
