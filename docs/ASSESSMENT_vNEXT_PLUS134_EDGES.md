# Assessment vNext+134 Edges

Status: planning-edge assessment for `V44-D`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS134_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
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

### Edge 2: Invariance Becomes Answer-Equivalence Taste

- Risk:
  invariance probes could drift into “same answer under paraphrase” heuristics without
  preserving the explicit abstract procedure the family is supposed to assess.
- Response:
  require explicit procedure-preservation anchors and freeze surface variation to the
  starter vocabulary only.

### Edge 2A: Suite Membership Semantics Stay Externalized

- Risk:
  the widened suite could claim four template classes at summary level while the real
  probe-to-class and probe-to-variation assignment remains only in fixture prose or
  side matrices.
- Response:
  make suite membership first-class in the released contract with per-member class,
  variation, repair-locality, and compatibility anchors.

### Edge 3: Repair Locality Widens Into Global Rewrite

- Risk:
  local-repair suites could quietly accept large-scale rewrite, undermining the family
  claim that repair discipline is structurally assessable.
- Response:
  freeze `repair_locality_posture = local_only` and require reject coverage for
  non-local repair rewrite posture.

### Edge 4: Recursive Depth Sneaks In Too Early

- Risk:
  widening the probe library could accidentally re-open nested-grandchild or
  recursive-depth structure before the reserved later seam is selected.
- Response:
  keep `V44-D` strictly prior to recursive depth and forbid nested-grandchild probes in
  the starter slice.

### Edge 5: `V44-C` Differential Law Is Quietly Rewritten

- Risk:
  widened-library compatibility replay could mutate paired-condition semantics rather
  than merely proving that the released differential surface still consumes the wider
  library lawfully.
- Response:
  require `V44-D` to consume released `V44-C` as-is and treat compatibility replay as
  evidence only, not as semantic redefinition.

### Edge 5A: Consumer Compatibility Blurs At Suite Level

- Risk:
  a suite-wide compatibility claim could erase the distinction between members that
  are lawful only for released taxonomy consumption and members that are also lawful
  for released differential consumption.
- Response:
  keep consumer compatibility granular at member level and forbid blanket suite-level
  claims from substituting for that law.

### Edge 6A: Deterministic Suite Export Drifts On Ordering

- Risk:
  deterministic export could still vary subtly if member ordering, surface-variation
  ordering, or compatibility-ref ordering is left to implementation taste.
- Response:
  freeze explicit ordering for suite summaries, member records, member compatibility
  refs, and the `suite_hash` subject.

### Edge 6: External Bundle Becomes Silent Library Authority

- Risk:
  the imported reasoning-benchmark bundle could quietly determine which widened probe
  classes or invariance semantics are lawful.
- Response:
  keep the external bundle support-only and re-author the widened library law from
  released `V44-A` / `V44-B` / `V44-C` contracts plus committed fixtures.

## Current Judgment

- `V44-D` is the right next move because the family now has a released substrate,
  taxonomy lane, and pair-level differential lane, but still lacks broader bounded
  library coverage across the selected template classes.
- the slice should remain narrow and library-first:
  - one suite schema
  - one deterministic library helper
  - first-class suite-membership semantics
  - widened but still bounded template coverage
  - explicit invariance anchors
  - explicit repair-locality posture
  - explicit member-level compatibility posture
  - no profile aggregation
  - no benchmark projection
- if the implementation stays that narrow, it should prepare later profile and
  recursive-depth work without letting the library lane overclaim as scoring or
  ranking.
