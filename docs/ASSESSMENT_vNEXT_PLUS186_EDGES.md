# Assessment vNext+186 Edges

Status: planning-edge assessment for `V67-B`.

Authority layer: planning / starter assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS186_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Utility Ranking Could Quietly Reopen Hard-Law Decisions

- Risk:
  advisory ranking could be used to rescue candidates that were already blocked
  by hard visibility, trust-boundary, commit-gate, or floor violations.
- Response:
  keep the evaluation order explicit and require blocked candidates to remain
  blocked regardless of utility posture.

### Edge 2: `report_status` Could Collapse Into Ergonomic Outcome

- Risk:
  artifact validity, basis mismatch, and ergonomic failure could be flattened
  into one status field, obscuring whether a case failed structurally or
  ergonomically.
- Response:
  keep `report_status` artifact-validity-only and `overall_judgment`
  ergonomic-outcome-only.

### Edge 3: Feasible-Candidate Ties Could Smuggle In Hidden Weights

- Risk:
  tied top-tier candidates could be broken by untracked heuristic weights or
  prose-driven preferences.
- Response:
  keep deterministic ladder semantics explicit and surface unresolved top-tier
  ties as `needs_review`.

### Edge 4: Physical Or Visual Inadmissibility Could Over-Block CSS Cases

- Risk:
  incomplete physical / visual chains could invalidate cases that only depend on
  lawful CSS geometry floors.
- Response:
  block only dependent computations and keep CSS-only adjudication available when
  the dependent physical / visual reasoning is not required.

### Edge 5: Computed Results Could Drift From Shipped `V67-A` Lineage

- Risk:
  the engine could recompute over a candidate table, visibility contract, or
  request that is not exactly bound to the shipped source refs and hashes.
- Response:
  preserve exact replayable lineage checks in computed outputs and fail closed on
  basis mismatch.

### Edge 6: `V67-B` Could Quietly Mint A New Artifact Family

- Risk:
  implementation convenience could widen the slice into new schema ids or ad hoc
  result packets instead of using the shipped `ux_ergonomic_adjudication_result@1`
  surface.
- Response:
  keep `V67-B` on the existing result schema and defer new typed runtime bridge
  artifacts to `V67-C` only.

### Edge 7: Reason Codes Could Drift Into Unstable Narrative Strings

- Risk:
  blocked, review, or supporting posture could be emitted as prose fragments
  rather than a bounded starter reason family, making the slice non-replayable.
- Response:
  freeze stable blocking, review, and supporting reason-code families in the
  slice lock and tests.

## Current Judgment

- `V67-B` is the right active next slice because the ergonomic language now ships
  on `main` and the missing next step is bounded computation over that shipped
  language
- the slice should stay deliberately finite:
  - deterministic adjudication helpers
  - shipped-source lineage checks
  - blocked / feasible / ambiguity / obligation rows
  - ordinal tiers only
- `V67-B` should not attempt runtime bridge output, runtime evidence harvesting,
  or generic layout solving
- if `v186` ships cleanly, `V67-C` can later compare realized measurement
  evidence against adjudicated expectations without reopening `V67-B` law.
