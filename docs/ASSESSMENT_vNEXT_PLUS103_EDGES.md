# Assessment vNext+103 Edges

Status: planning-edge assessment for `V45-D`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS103_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Aspirational Invariant Overclaim

- Risk:
  tests could be labeled as defending strong invariants even when the observed
  assertion surface is too thin to support the claim.
- Response:
  keep claimed invariant binding separate from observed assertion surface and fail
  closed on unsupported claims.

### Edge 2: Claimed-Vs-Observed Collapse

- Risk:
  the matrix could reduce into one prose field that blurs what the test is intended to
  defend with what the test actually checks.
- Response:
  require explicit row granularity at one test-claim/assertion unit and keep claimed
  invariant binding distinct from observed assertion surface.

### Edge 3: Cross-Artifact Drift Relative To `V45-B`

- Risk:
  the emitted matrix could drift away from the released symbol/dependency baseline,
  leaving guarded-surface refs that no longer resolve against the bound code graph.
- Response:
  require shared snapshot/source binding and fail closed on unresolved internal
  guarded-surface refs.

### Edge 4: Boundary-Ref Ambiguity

- Risk:
  out-of-scope or external guarded surfaces could be accepted as dangling strings
  instead of explicit typed boundary refs.
- Response:
  freeze a bounded guarded-surface ref-kind model and reject untyped boundary refs.

### Edge 5: Helper-Indirection Opacity

- Risk:
  tests often defend invariants through helper calls or fixtures, which can make the
  observed assertion surface harder to capture than direct `assert` statements.
- Response:
  allow bounded derivation methods such as `fixture_or_helper_binding`, but keep
  confidence posture explicit, use the bound dependency graph to explain helper and
  fixture reachability, and fail closed on overclaim.

### Edge 6: Release-Gating Laundering

- Risk:
  a descriptive test-intent row could be overread as automatic release-gating or
  merge-blocking authority.
- Response:
  keep gating posture descriptive-only and forbid automatic promotion into release
  authority.

### Edge 7: Snapshot Overread

- Risk:
  one snapshot-bound test-intent matrix could be overread as current repo truth after
  repo drift.
- Response:
  keep snapshot validity posture explicit and treat stale outputs as historical.

### Edge 8: Confidence Inflation

- Risk:
  confidence posture could be emitted as if it were proof or settlement rather than a
  bounded support-strength judgment.
- Response:
  keep confidence posture explicitly descriptive and require stronger postures to carry
  stronger evidence or adjudication.

### Edge 9: Provenance Membership Drift

- Risk:
  source artifact refs could be present textually but point outside the declared test
  source set, weakening the matrix's provenance claims.
- Response:
  require every `source_artifact_ref` to resolve inside the declared `test_source_set`
  and reject rows that violate that membership law.

### Edge 10: Scope Creep Into `V45-E` Or `V45-F`

- Risk:
  the test-intent lane could widen early into optimization registers or
  descriptive-to-normative binding.
- Response:
  keep `v103` bounded to `repo_test_intent_matrix@1` only.

### Edge 11: Python-Only Boundary Drift

- Risk:
  the first test-intent release could silently widen into whole-repo or multi-language
  test inventory before the bounded Python seam is stable.
- Response:
  keep the first release bounded to one explicit Python test source set only.

## Current Judgment

- `V45-D` is worth implementing now because the repo already has released descriptive
  baselines for schema-visible entities (`V45-A`), code symbols/dependencies (`V45-B`),
  and open arc/slice planning dependencies (`V45-C`).
- the next missing descriptive layer is typed test-intent visibility, not another
  code-structure or planning-register surface.
