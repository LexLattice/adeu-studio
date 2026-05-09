# Assessment vNext+261 Edges

Status: pre-lock edge assessment for `PB-MATRIX-0-B`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS261_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Projection Could Bypass Released A Inclusion Law

- Risk:
  a result projection could cite a case that was not included by released
  `PB-MATRIX-0-A` controls.
- Required containment:
  B validators must consume released A request, inclusion manifest,
  eligibility review, control contract, and guardrail rows, and projection
  rows may reference only A-included cases.

### Edge 2: Projection Could Become New Outcome Truth

- Risk:
  a matrix projection could author a new local result posture instead of
  deriving from released local trial/retry rows.
- Required containment:
  projection rows must carry source result refs, source result hashes, source
  family closeout refs, projection rule refs, projection basis rows,
  projection currentness, and explicit not-new-truth posture.

### Edge 3: Projection Gaps Could Disappear

- Risk:
  an included case without a current released local result could be omitted
  from B, making the matrix look complete.
- Required containment:
  every A-included case must have exactly one current projection row or a
  declared projection gap.

### Edge 4: Observation Ledger Could Become Model Ranking

- Risk:
  local observations could include model superiority, cross-worker ranking,
  official score, leaderboard, pass-rate, solve-rate, or success-rate
  language.
- Required containment:
  observation ledger validators must reject ranking/scoring language and keep
  observations local-only and non-authoritative.

### Edge 5: Coverage Register Could Claim Hidden-Test Coverage

- Risk:
  local coverage rows could be read as hidden-test coverage, official
  evaluator equivalence, or ProgramBench denominator coverage.
- Required containment:
  coverage registers must carry local coverage basis refs, local denominator
  posture, hidden-test coverage exclusion posture, and explicit no hidden-test
  coverage posture.

### Edge 6: Contamination Register Could Leak Forbidden Details

- Risk:
  contamination details could reveal hidden or forbidden source names, paths,
  excerpts, semantic summaries, test names, hidden artifact identifiers, or
  original-source clues.
- Required containment:
  contamination rows must carry redaction policy and detail posture, and
  validators must reject content-bearing forbidden detail.

### Edge 7: B Could Prematurely Emit C Artifacts

- Risk:
  B could include matrix summary, post-matrix handoff, or family closeout rows.
- Required containment:
  B fixtures and bundle validation must reject `PB-MATRIX-0-C` artifact
  kinds. Summary and handoff remain deferred.

### Edge 8: B Could Become Execution Or Batch Authority

- Risk:
  projection or observation rows could be interpreted as permission to run
  cases, execute commands, materialize candidates, or contact official
  ProgramBench surfaces.
- Required containment:
  B guardrails must preserve A non-authority posture and reject command
  execution, batch execution, candidate materialization, official runner or
  evaluator access, hidden-test handling, official submission authority, and
  future-family selection.

## Residual Edges

- The implementation PR must add focused reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus261/`.
- The implementation PR must run the focused `PB-MATRIX-0-B` tests and
  `make check` before opening the PR.
- Later `PB-MATRIX-0-C` must summarize only released B projection/ledger/
  coverage/contamination rows, keep aggregate counts accounting-only, and
  prevent benchmark-score or model-ranking language.

## Current Judgment

The `PB-MATRIX-0-B` starter is bounded enough to proceed to implementation
after `make arc-start-check ARC=261` passes.
