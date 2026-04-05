# Assessment vNext+134 Edges

Status: post-closeout edge assessment for `V44-D` (April 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS134_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Probe-Library Widening Overclaims As Benchmark Readiness

- Risk:
  the widening slice could start acting like a benchmark-family or leaderboard release
  instead of a bounded assessment-library extension.
- Response:
  keep `V44-D` limited to released probe-suite widening only and forbid profile,
  ranking, and benchmark outputs in the starter slice.
- Closeout Evidence:
  the shipped schema/package surface carries only probe-suite widening law, with no
  profile, ranking, benchmark, or one-number summary fields.

### Edge 2: Invariance Becomes Answer-Equivalence Taste

- Risk:
  invariance probes could drift into “same answer under paraphrase” heuristics without
  preserving the explicit abstract procedure the family is supposed to assess.
- Response:
  require explicit procedure-preservation anchors and freeze surface variation to the
  starter vocabulary only.
- Closeout Evidence:
  the released helper/model law requires invariance anchors, both frozen invariance
  kinds are exercised positively, and the committed reject fixture fails closed when
  the anchor law is missing.

### Edge 2A: Suite Membership Semantics Stay Externalized

- Risk:
  the widened suite could claim four template classes at summary level while the real
  probe-to-class and probe-to-variation assignment remains only in fixture prose or
  side matrices.
- Response:
  make suite membership first-class in the released contract with per-member class,
  variation, repair-locality, and compatibility anchors.
- Closeout Evidence:
  the shipped `ReasoningProbeSuite` contract carries explicit `suite_members`, the
  suite matrix fixture now mirrors rather than substitutes for those member records,
  and deterministic suite-order/hash coverage exercises the same first-class member
  structure.

### Edge 3: Repair Locality Widens Into Global Rewrite

- Risk:
  local-repair suites could quietly accept large-scale rewrite, undermining the family
  claim that repair discipline is structurally assessable.
- Response:
  freeze `repair_locality_posture = local_only` and require reject coverage for
  non-local repair rewrite posture.
- Closeout Evidence:
  the released contract keeps repair locality bounded to `local_only`, the shipped
  suite summary may restate only that posture, and the committed non-local repair
  fixture fails closed.

### Edge 4: Recursive Depth Sneaks In Too Early

- Risk:
  widening the probe library could accidentally re-open nested-grandchild or
  recursive-depth structure before the reserved later seam is selected.
- Response:
  keep `V44-D` strictly prior to recursive depth and forbid nested-grandchild probes in
  the starter slice.
- Closeout Evidence:
  the released suite contract widens across decomposition, branching, local repair,
  and invariance only; no recursive-depth or nested-grandchild surface ships in the
  live package.

### Edge 5: `V44-C` Differential Law Is Quietly Rewritten

- Risk:
  widened-library compatibility replay could mutate paired-condition semantics rather
  than merely proving that the released differential surface still consumes the wider
  library lawfully.
- Response:
  require `V44-D` to consume released `V44-C` as-is and treat compatibility replay as
  evidence only, not as semantic redefinition.
- Closeout Evidence:
  the shipped compatibility replay fixtures point into released `V44-B` and released
  `V44-C` surfaces only, and no differential judgment or status vocabulary changed in
  the live implementation.

### Edge 5A: Consumer Compatibility Blurs At Suite Level

- Risk:
  a suite-wide compatibility claim could erase the distinction between members that
  are lawful only for released taxonomy consumption and members that are also lawful
  for released differential consumption.
- Response:
  keep consumer compatibility granular at member level and forbid blanket suite-level
  claims from substituting for that law.
- Closeout Evidence:
  suite members now carry explicit compatibility refs, differential compatibility
  remains lawful only where pair compatibility was already released, and review
  hardening preserved that fail-closed posture.

### Edge 6: Deterministic Suite Export Drifts On Ordering

- Risk:
  deterministic export could still vary subtly if member ordering, surface-variation
  ordering, or compatibility-ref ordering is left to implementation taste.
- Response:
  freeze explicit ordering for suite summaries, member records, member compatibility
  refs, and the `suite_hash` subject.
- Closeout Evidence:
  the released model/helper law now canonicalizes suite ordering and `suite_hash`
  computation, and the committed replay fixtures plus targeted tests validate that
  deterministic ordering end to end.

### Edge 7: External Bundle Becomes Silent Library Authority

- Risk:
  the imported reasoning-benchmark bundle could quietly determine which widened probe
  classes or invariance semantics are lawful.
- Response:
  keep the external bundle support-only and re-author the widened library law from
  released `V44-A` / `V44-B` / `V44-C` contracts plus committed fixtures.
- Closeout Evidence:
  live implementation ownership remains entirely under
  `packages/adeu_reasoning_assessment`, while the benchmarking bundle stays normalized
  under `examples/external_prototypes/...` and non-precedent.

## Current Judgment

- `V44-D` was the right next move because the family had the released assessment
  substrate, normalized failure vocabulary, and pair-level diagnosis seam needed
  before broader library coverage became safe.
- the shipped result remains properly bounded:
  - one repo-owned package
  - one probe-suite schema
  - one deterministic widening helper
  - first-class suite-membership semantics
  - explicit procedure-preserving invariance posture
  - explicit local-only repair posture
  - explicit member-level consumer compatibility posture
  - no profile aggregation
  - no benchmark projection
  - no recursive-depth release
- `V44-E` is now the right next path because the widened non-recursive library exists
  on `main` without overclaiming as profile, ranking, or benchmark scoring.
