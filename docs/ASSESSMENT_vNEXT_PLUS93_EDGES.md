# Assessment vNext+93 Edges

Status: planning-edge assessment for `V42-E`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS93_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Local-To-Scorecard Authority Leakage

- Risk:
  local evaluation success could be treated as scorecard authority without explicit
  source kind, posture, and basis refs.
- Response:
  require explicit `scorecard_source_kind`, decomposed authority posture fields, and
  `authority_basis_refs`; fail closed otherwise.

### Edge 2: Replay-Lineage Gaps

- Risk:
  scorecard outputs could claim replay authority while missing deterministic lineage, or
  conflating internal local replay with external replay authority.
- Response:
  require explicit local replay lineage refs, separate external replay authority refs,
  and deterministic replay validation.

### Edge 3: Competition-Mode Ambiguity

- Risk:
  competition posture could be implied by naming instead of explicit typed status.
- Response:
  require explicit enum-bounded `competition_mode_posture` values and separate deferred
  assertions.

### Edge 4: Summary-Only Authority Claims

- Risk:
  scorecard summaries could become hidden authority surfaces.
- Response:
  make summaries descriptive-only; authority must come from source-kind and typed
  authority registers.

### Edge 5: Settlement-Posture Erasure

- Risk:
  scorecard outputs could present finality while dropping ambiguity/claim posture carry.
- Response:
  require explicit `settlement_posture_carry` with fail-closed validation.

### Edge 6: Leaderboard Overclaim

- Risk:
  bounded local/scorecard artifacts could be over-promoted into leaderboard-readiness
  claims.
- Response:
  reject leaderboard-readiness or competition-success claims in `V42-E`.

### Edge 7: Retroactive Necessity Laundering

- Risk:
  one strong scorecard trajectory could be interpreted as universal task-rule necessity.
- Response:
  reject necessity overclaim without explicit entitlement evidence.

### Edge 8: Deployment Surface Creep

- Risk:
  direct online submission, API/web routes, or tournament orchestration could be mixed
  into the scorecard seam.
- Response:
  keep `V42-E` bounded to scorecard/replay and competition-posture surfaces only.

### Edge 9: Upstream Contract Drift

- Risk:
  scorecard implementation could silently reinterpret released `V42-A` through `V42-D`
  semantics.
- Response:
  require strict lineage consumption and prohibit upstream contract redefinition.

### Edge 10: Model-Sensitivity Collapse

- Risk:
  model/run identity might be dropped at scorecard level, obscuring empirical
  model-class behavior.
- Response:
  require explicit model/run identity carry-through in scorecard artifacts.

### Edge 11: Authority-Class Matrix Under-Specified

- Risk:
  the artifact could remain ambiguous if only one authority class is represented in
  fixtures.
- Response:
  require explicit authority-class fixture coverage:
  - `local_shadow_only`
  - `competition_posture_declared_no_official_scorecard`
  - `official_imported`

## Current Judgment

- `V42-E` is the correct next slice because `V42-D` is closed on `main` and the missing
  seam is now scorecard/replay authority plus competition-posture boundary control over
  released local-eval lineage.
