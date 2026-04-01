# Assessment vNext+104 Edges

Status: post-closeout edge assessment for `V45-E` (April 1, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS104_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Hotspot-To-Mutation Laundering

- Risk:
  surfaced hotspots or consolidation candidates could be overread as authorization to
  split, merge, or refactor code immediately.
- Response:
  keep descriptive findings, optimization candidates, and amendment entitlement as
  distinct typed fields and freeze starter entitlement to a negative posture only.
- Closeout Evidence:
  `RepoOptimizationEntry` structure in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixture
  `apps/api/fixtures/repo_description/vnext_plus104/repo_optimization_register_v104_reject_amendment_entitlement_laundering.json`,
  and rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45e.py`.

### Edge 2: Priority Inflation

- Risk:
  priority posture could be interpreted as scheduling, release-gating, or merge-order
  authority instead of descriptive planning input.
- Response:
  keep `priority_posture` descriptive-only and explicitly non-authorizing in the first
  release.
- Closeout Evidence:
  bounded `priority_posture` vocabulary in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`
  and accepted fixture replay under
  `apps/api/fixtures/repo_description/vnext_plus104/`.

### Edge 3: Support-Basis Thinness

- Risk:
  optimization rows could become elegant summaries with weak actual support, especially
  when driven by file length, naming repetition, or vague concentration signals alone.
- Response:
  require explicit `support_basis`, explicit source artifact refs, and fail-closed
  rejection of unsupported optimization claims.
- Closeout Evidence:
  `support_basis` requirement in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixture
  `apps/api/fixtures/repo_description/vnext_plus104/repo_optimization_register_v104_reject_missing_support_basis.json`,
  and rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45e.py`.

### Edge 4: Cross-Artifact Drift Relative To `V45-A` Through `V45-D`

- Risk:
  the register could cite entity, schema, symbol, dependency, or test-intent surfaces
  that do not actually match the same snapshot identity or artifact-local source-scope
  posture.
- Response:
  require shared snapshot identity, explicit source-scope compatibility, and fail
  closed on unresolved or mismatched bound references.
- Closeout Evidence:
  `validate_repo_optimization_register_against_v45_baseline` in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  accepted fixture replay in
  `packages/adeu_repo_description/tests/test_repo_description_v45e.py`,
  and reject bundle fixture
  `apps/api/fixtures/repo_description/vnext_plus104/repo_optimization_register_bundle_v104_reject_bound_artifact_snapshot_scope_mismatch.json`.

### Edge 5: Scope-Ref Ambiguity

- Risk:
  optimization entries could point at vague prose scopes or dangling identifiers rather
  than resolvable bounded surfaces.
- Response:
  require typed finding scopes, explicit carrier semantics for
  `cross_surface_cluster`, and reject unresolved internal scope refs.
- Closeout Evidence:
  `RepoOptimizationFindingScope` validation in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixtures
  `apps/api/fixtures/repo_description/vnext_plus104/repo_optimization_register_v104_reject_cross_surface_cluster_without_member_carrier.json`
  and
  `apps/api/fixtures/repo_description/vnext_plus104/repo_optimization_register_v104_reject_unresolved_finding_scope.json`,
  plus rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45e.py`.

### Edge 6: Mixed-Finding Flattening

- Risk:
  structural, semantic, governance, and surface compression signals could collapse into
  one primary label and discard the mixed character of the finding.
- Response:
  freeze a bounded starter compression-axis vocabulary, keep one primary axis explicit
  per row, and allow bounded secondary tags for mixed findings.
- Closeout Evidence:
  bounded secondary-tag fields in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`
  and accepted fixture assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45e.py`.

### Edge 7: Descriptive Plane Drift Into `V45-F`

- Risk:
  the optimization register could widen early into descriptive-to-normative binding,
  recursive governance, or amendment-routing logic.
- Response:
  keep `v104` bounded to `repo_optimization_register@1` only and defer `V45-F`.
- Closeout Evidence:
  lock boundary in `docs/LOCKED_CONTINUATION_vNEXT_PLUS104.md`
  plus absence of `V45-F` runtime or schema artifacts in the shipped v104 surface set.

### Edge 8: Snapshot Overread

- Risk:
  one snapshot-bound optimization register could be treated as current repo truth after
  the repo changes.
- Response:
  keep snapshot validity posture explicit and treat stale outputs as historical
  evidence only.
- Closeout Evidence:
  snapshot identity/hash and validity posture fields in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`
  plus accepted fixture replay under
  `apps/api/fixtures/repo_description/vnext_plus104/`.

### Edge 9: Source-Set Provenance Drift

- Risk:
  source artifact refs could be present textually while pointing outside the declared
  optimization source set, weakening the register's descriptive support claims.
- Response:
  require every `source_artifact_ref` to resolve inside the declared `source_set` and
  reject rows that violate membership.
- Closeout Evidence:
  source-set membership validation in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixture
  `apps/api/fixtures/repo_description/vnext_plus104/repo_optimization_register_v104_reject_source_artifact_ref_outside_source_set.json`,
  and rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45e.py`.

### Edge 10: Historical `V45-C` Baseline Drift

- Risk:
  `V45-E` derivation could silently pick up current planning-sensitive `V45-C` state
  instead of the released corrective baseline it is supposed to consume as historical
  context.
- Response:
  centralize historical `v102` fixture loading behind one explicit helper and keep
  that seam inspectable.
- Closeout Evidence:
  `_load_historical_v45c_v102_reference` in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`
  and accepted fixture replay in
  `packages/adeu_repo_description/tests/test_repo_description_v45e.py`.

## Current Judgment

- `V45-E` is worth implementing now because `V45-A` through `V45-D` already provide
  the descriptive substrate needed for a bounded optimization-register seam.
- `V45-E` on `main` now resolves the bounded optimization-register gap by shipping a
  deterministic `repo_optimization_register@1` surface with explicit descriptive
  finding versus optimization candidate separation, explicit negative
  amendment-entitlement posture, explicit support/provenance fields, and explicit
  binding back to the released `V45-A` through `V45-D` descriptive baseline.
- the shipped baseline remains strictly diagnostic-first and non-promotional so later
  normative or amendment lanes can consume it without being silently authorized by it.
