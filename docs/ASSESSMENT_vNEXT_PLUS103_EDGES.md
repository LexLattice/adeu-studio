# Assessment vNext+103 Edges

Status: post-closeout edge assessment for `V45-D` (April 1, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS103_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
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
- Closeout Evidence:
  distinct row-model anchors in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixture
  `apps/api/fixtures/repo_description/vnext_plus103/repo_test_intent_matrix_v103_reject_claim_without_observed_assertion_surface.json`,
  and rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45d.py`.

### Edge 2: Claimed-Vs-Observed Collapse

- Risk:
  the matrix could reduce into one prose field that blurs what the test is intended to
  defend with what the test actually checks.
- Response:
  require explicit row granularity at one test-claim/assertion unit and keep claimed
  invariant binding distinct from observed assertion surface.
- Closeout Evidence:
  `RepoTestIntentEntry` structure in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`
  and row-granularity coverage in
  `packages/adeu_repo_description/tests/test_repo_description_v45d.py`.

### Edge 3: Cross-Artifact Drift Relative To `V45-B`

- Risk:
  the emitted matrix could drift away from the released symbol/dependency baseline,
  leaving guarded-surface refs that no longer resolve against the bound code graph.
- Response:
  require shared snapshot/source binding and fail closed on unresolved internal
  guarded-surface refs.
- Closeout Evidence:
  `validate_repo_test_intent_matrix_against_v45b` in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  accepted fixture replay in
  `packages/adeu_repo_description/tests/test_repo_description_v45d.py`,
  and reject pair fixture
  `apps/api/fixtures/repo_description/vnext_plus103/repo_test_intent_matrix_pair_v103_reject_mismatched_v45b_snapshot_binding.json`.

### Edge 4: Boundary-Ref Ambiguity

- Risk:
  out-of-scope or external guarded surfaces could be accepted as dangling strings
  instead of explicit typed boundary refs.
- Response:
  freeze a bounded guarded-surface ref-kind model and reject untyped boundary refs.
- Closeout Evidence:
  guarded-surface-ref validation in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixture
  `apps/api/fixtures/repo_description/vnext_plus103/repo_test_intent_matrix_v103_reject_guarded_surface_ref_without_boundary_typing.json`,
  and rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45d.py`.

### Edge 5: Helper-Indirection Opacity

- Risk:
  tests often defend invariants through helper calls or fixtures, which can make the
  observed assertion surface harder to capture than direct `assert` statements.
- Response:
  allow bounded derivation methods such as `fixture_or_helper_binding`, but keep
  confidence posture explicit, use the bound dependency graph to explain helper and
  fixture reachability, and fail closed on overclaim.
- Closeout Evidence:
  bounded derivation posture/method fields in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  helper-aware extraction in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`,
  and accepted fixture replay in
  `packages/adeu_repo_description/tests/test_repo_description_v45d.py`.

### Edge 6: Release-Gating Laundering

- Risk:
  a descriptive test-intent row could be overread as automatic release-gating or
  merge-blocking authority.
- Response:
  keep gating posture descriptive-only and forbid automatic promotion into release
  authority.
- Closeout Evidence:
  `matrix_scope` authority checks in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixture
  `apps/api/fixtures/repo_description/vnext_plus103/repo_test_intent_matrix_v103_reject_authority_laundering_release_gating.json`,
  and rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45d.py`.

### Edge 7: Snapshot Overread

- Risk:
  one snapshot-bound test-intent matrix could be overread as current repo truth after
  repo drift.
- Response:
  keep snapshot validity posture explicit and treat stale outputs as historical.
- Closeout Evidence:
  snapshot identity/hash and validity posture fields in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`
  plus accepted fixture replay under
  `apps/api/fixtures/repo_description/vnext_plus103/`.

### Edge 8: Confidence Inflation

- Risk:
  confidence posture could be emitted as if it were proof or settlement rather than a
  bounded support-strength judgment.
- Response:
  keep confidence posture explicitly descriptive and require stronger postures to carry
  stronger evidence or adjudication.
- Closeout Evidence:
  confidence/derivation consistency validation in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`
  and accepted fixture replay in
  `packages/adeu_repo_description/tests/test_repo_description_v45d.py`.

### Edge 9: Provenance Membership Drift

- Risk:
  source artifact refs could be present textually but point outside the declared test
  source set, weakening the matrix's provenance claims.
- Response:
  require every `source_artifact_ref` to resolve inside the declared `test_source_set`
  and reject rows that violate that membership law.
- Closeout Evidence:
  test-source-set membership validation in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixture
  `apps/api/fixtures/repo_description/vnext_plus103/repo_test_intent_matrix_v103_reject_source_artifact_ref_outside_test_source_set.json`,
  and rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45d.py`.

### Edge 10: Scope Creep Into `V45-E` Or `V45-F`

- Risk:
  the test-intent lane could widen early into optimization registers or
  descriptive-to-normative binding.
- Response:
  keep `v103` bounded to `repo_test_intent_matrix@1` only.
- Closeout Evidence:
  lock boundary in `docs/LOCKED_CONTINUATION_vNEXT_PLUS103.md`
  plus absence of optimization-register or normative-binding artifacts in the shipped
  v103 surface set.

### Edge 11: Python-Only Boundary Drift

- Risk:
  the first test-intent release could silently widen into whole-repo or multi-language
  test inventory before the bounded Python seam is stable.
- Response:
  keep the first release bounded to one explicit Python test source set only.
- Closeout Evidence:
  bounded source-set extraction in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`
  via `default_v45d_source_paths()`
  and accepted fixture source-set bindings in
  `apps/api/fixtures/repo_description/vnext_plus103/`.

### Edge 12: Annotation-Only Assignment Breakage

- Risk:
  annotation-only `AnnAssign` nodes could raise during provenance extraction and abort
  matrix derivation for valid Python test files.
- Response:
  treat `AnnAssign(value=None)` as a no-value assignment and leave provenance unchanged.
- Closeout Evidence:
  `_update_test_provenance_for_assignment` in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`
  and test
  `test_v45d_accepts_annotation_only_annassign_in_test_body`.

### Edge 13: Relative Import Alias Loss

- Risk:
  relative `ImportFrom` aliases such as `from . import helper` could be dropped,
  weakening guarded-surface inference and causing fallback or external classifications.
- Response:
  resolve relative import bindings against the current source path before alias-map
  construction.
- Closeout Evidence:
  `_extract_test_import_aliases` and `_resolve_import_from_module` in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`
  and test
  `test_v45d_resolves_relative_import_from_aliases_to_internal_module_boundaries`.

### Edge 14: Branch-Local Provenance Leakage

- Risk:
  mutually exclusive branches could share one mutable provenance map and let
  assignments from one branch bleed into the other during static analysis.
- Response:
  recurse into nested branch bodies with branch-local provenance copies.
- Closeout Evidence:
  `_derive_entries_for_test_function` in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`
  and test
  `test_v45d_branch_local_provenance_does_not_leak_between_if_branches`.

## Current Judgment

- `V45-D` on `main` resolves the bounded test-intent gap by shipping a deterministic
  `repo_test_intent_matrix@1` surface with explicit claimed-vs-observed row structure,
  explicit test-source provenance, and explicit binding back to the released `V45-B`
  symbol/dependency baseline.
- the shipped baseline remains descriptive-first and non-promotional, preserving
  deferral of `V45-E`, `V45-F`, scheduler automation, mutation entitlement, and
  recursive-governance binding.
