# Assessment vNext+183 Edges

Status: post-closeout edge assessment for `V66-B` (April 21, 2026 UTC).

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS183_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Migration Binding Could Quietly Become Supersession Law

- Risk:
  the migration-binding slice could start treating registered host / companion
  relation as if it automatically supersedes current markdown authority.
- Response:
  keep migration binding explicit and fail-closed.
  - companion registration is not supersession by itself
  - explicit transition law remains required
- Closeout Evidence:
  shipped migration-binding builders and tests keep supersession
  transition-law-gated and fail-closed.

### Edge 2: Generated Reader Views Could Quietly Become Authority

- Risk:
  reader projections could be overread as controlling text merely because they
  are generated from governed ANM sources.
- Response:
  keep generated reader posture explicit and non-authoritative.
  - generated reader view is not authority by itself
  - stale or missing projection fails closed only when projection is explicitly
    required
- Closeout Evidence:
  shipped projection checks and tests preserve non-authoritative posture and
  governed-source exclusion.

### Edge 3: Semantic Diff Could Quietly Become Lock Or Runtime Law

- Risk:
  semantic diff output could be treated as if it authorizes implementation or
  proves lock-level change by itself.
- Response:
  keep semantic diff review-only and non-authoritative.
  - semantic diff records change visibility only
  - semantic diff is not authority by itself
- Closeout Evidence:
  shipped diff builder/tests preserve explicit-baseline review-only semantics
  and reject authority overread.

### Edge 4: `V66-B` Could Widen Beyond The Same Governed Source Set

- Risk:
  migration binding and reader projection could start widening discovery beyond
  the shipped `V66-A` governed source set.
- Response:
  keep the carried source set exact and fail-closed.
  - same shipped governed ANM source set only
  - no fresh source-set widening by default
- Closeout Evidence:
  shipped `V66-B` outputs remain explicitly downstream of exact `V66-A`
  manifest / profile / policy basis only.

### Edge 5: `V66-B` Could Reopen `V47` Language Or Compiler Ownership

- Risk:
  migration/projection work could start sneaking in new authority-block
  semantics or selector/predicate doctrine changes.
- Response:
  keep `V47` closed and authoritative.
  - no new `D@1` semantics
  - no selector or predicate ownership widening
  - no policy-consumer widening
- Closeout Evidence:
  shipped `V66-B` surfaces add migration/projection/diff posture only and do
  not widen released `V47` language or ownership doctrine.

### Edge 6: Reader-Projection Convenience Could Backdoor Repo-Wide Rename Pressure

- Risk:
  the existence of generated reader views could be overread as proof that all
  docs should be renamed or migrated immediately.
- Response:
  keep adoption path-local and authority-layered.
  - no repo-wide `.adeu.md` rename by default
  - current markdown remains controlling until explicit transition law says
    otherwise
- Closeout Evidence:
  shipped migration / projection posture remains path-local and transition-law
  gated, with no repo-wide rename or promotion doctrine.

### Edge 7: Semantic Diff Baseline Could Become Nondeterministic

- Risk:
  semantic diff could silently depend on implicit Git base, working-tree state,
  or reviewer-local baseline choice and stop being replayable.
- Response:
  keep baseline selection explicit and typed.
  - no implicit Git diff baseline
  - no working-tree diff baseline
  - explicit baseline artifact or initial-report posture only
- Closeout Evidence:
  shipped diff builder/tests preserve explicit initial or prior-artifact
  baseline posture only.

### Edge 8: Generated Reader Views Could Re-Enter Governed Source Discovery

- Risk:
  generated projections could contain rendered or copied authority text and then
  be rediscovered as if they were fresh ANM source inputs.
- Response:
  keep generated projections excluded from governed source by construction.
  - generated projection source posture remains explicit
  - generated projections may not be used as `D@1` lowering inputs
  - generated projections remain non-authoritative even when they render
    authority text
- Closeout Evidence:
  shipped compiler checks reject generated projections as governed ANM source
  and preserve non-authoritative rendering posture.

### Edge 9: Migration-Binding Cardinality Could Stay Ambiguous

- Risk:
  the slice could leave unclear whether migration binding is one record per pair
  or one repo-scale profile with many rows, leading to inconsistent
  implementations.
- Response:
  keep migration binding row-shaped and repo-scale.
  - one typed profile surface only
  - binding rows carry pair-local posture inside that profile
- Closeout Evidence:
  shipped schema/model/tests keep migration binding row-shaped and repo-scale,
  with fail-closed companion host ownership checks.

### Edge 10: Transition-Law References Could Resolve To Non-Lock Documents

- Risk:
  planning docs, support docs, generated reader views, or semantic-diff outputs
  could be overread as if they satisfied supersession transition law.
- Response:
  keep transition-law resolution lock-bound and fail-closed.
  - transition law must resolve to lock authority
  - it must match host, companion, and supersession scope
  - unresolved or non-lock refs fail closed
- Closeout Evidence:
  shipped transition-law resolution remains lock-bound, token-aware, and
  fail-closed.

## Current Judgment

- `V66-B` was the right next slice because `V66-A` already closed the bounded
  source discovery / authority-profile / class-policy starter on `main`, and
  `v183` needed the explicit migration-binding, generated reader-projection, and
  semantic-diff surfaces over that same governed source set.
- the shipped result remained properly bounded:
  - same shipped `V66-A` governed source set only
  - one migration-binding seam only
  - one generated reader-projection seam only
  - one semantic diff seam only
  - consumed `V66-A` basis remains distinct from emitted `V66-B` artifacts
  - explicit baseline-only semantic diff
  - generated projections remain non-source by construction
  - transition law remains lock-bound and fail-closed
  - no compile-report or prose-boundary widening yet
  - no generated-reader or semantic-diff authority by implication
- `V66-B` is now closed on `main`.
- any follow-on should start from a new planning decision, with expected next
  seam in `V66-C`, rather than widening this closed slice.
