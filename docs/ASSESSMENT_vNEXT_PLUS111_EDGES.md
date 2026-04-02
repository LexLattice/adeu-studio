# Assessment vNext+111 Edges

Status: post-closeout edge assessment for `V47-F` (April 2, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS111_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Benchmark-World Scope Drift

- Risk:
  `V47-F` could have quietly widened from a bounded benchmark-world consumer seam into
  a vague “any benchmark family” doctrine.
- Response:
  freeze the starter benchmark-world vocabulary to already released `V42` benchmark
  artifacts on `main` and keep `V46` benchmark-family release out of this slice.
- Closeout Evidence:
  `BenchmarkConsumerWorldKind` typing in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  committed profile fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47f/reference_anm_benchmark_policy_consumer_binding_profile.json`,
  and tests `test_v47f_vocabularies_are_exact` plus
  `test_v47f_accepts_all_three_benchmark_worlds`.

### Edge 2: Policy-Source Collapse

- Risk:
  benchmark consumer rows could treat result or ledger refs as if they were the
  authoritative policy source while leaving clause binding semantically vague.
- Response:
  require exactly one bound released `D-IR` clause source per benchmark row and make
  results or ledger refs supporting evidence only.
- Closeout Evidence:
  `AnmBenchmarkPolicyConsumerRow` in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  compile-time clause resolution in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  accepted spec
  `packages/adeu_semantic_source/tests/fixtures/v47f/reference_benchmark_policy_consumer_spec.json`,
  and deterministic replay in
  `test_v47f_reference_profile_replays_deterministically`.

### Edge 3: Result/Ledger Authority Laundering

- Risk:
  because result and ledger artifacts were already released, they could be overread as
  independent policy authority in benchmark consumer bindings.
- Response:
  freeze an explicit support-only doctrine for result-set and ledger refs and reject
  result-or-ledger-only benchmark rows, plus fail closed when support surfaces
  contradict each other, contradict the bound policy source, or attach to the wrong
  benchmark target lineage.
- Closeout Evidence:
  support-surface validation in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  reject spec
  `packages/adeu_semantic_source/tests/fixtures/v47f/reject_support_only_authority_spec.json`,
  and tests `test_v47f_rejects_support_only_authority_claim`,
  `test_v47f_rejects_contradictory_supporting_surfaces`, and
  `test_v47f_rejects_supporting_surface_with_wrong_target`.

### Edge 4: Local-Eval Authority Overread

- Risk:
  released `adeu_arc_local_eval_record@1` artifacts could be reinterpreted as official
  scorecard, leaderboard, or competition authority.
- Response:
  require local-eval benchmark consumers to preserve released `V42-D` local-only
  posture and fail closed on any stronger authority claim.
- Closeout Evidence:
  local-eval world/ref typing in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  local-eval accepted row in
  `packages/adeu_semantic_source/tests/fixtures/v47f/reference_benchmark_policy_consumer_spec.json`,
  and the constrain-only authority relation carried by the committed reference profile.

### Edge 5: Scorecard Source-Kind Overread

- Risk:
  released `adeu_arc_scorecard_manifest@1` artifacts could be consumed as if typed
  source-kind and authority-limitations posture did not matter.
- Response:
  require benchmark consumers to respect released `V42-E` scorecard source-kind,
  authority, and limitation posture exactly rather than bypassing it through raw ref
  binding.
- Closeout Evidence:
  scorecard world/ref typing in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  scorecard accepted row in
  `packages/adeu_semantic_source/tests/fixtures/v47f/reference_benchmark_policy_consumer_spec.json`,
  and test `test_v47f_accepts_all_three_benchmark_worlds`.

### Edge 6: Behavior-Evidence Narrative Laundering

- Risk:
  released `adeu_arc_behavior_evidence_bundle@1` artifacts could be consumed as if
  descriptive narrative or inferred claim-posture entries were execution or approval
  authority.
- Response:
  preserve released `V42-G4` authority-boundary and claim-posture doctrine and fail
  closed on stronger interpretation.
- Closeout Evidence:
  behavior-evidence world/ref typing in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  behavior-evidence accepted row in
  `packages/adeu_semantic_source/tests/fixtures/v47f/reference_benchmark_policy_consumer_spec.json`,
  and test `test_v47f_accepts_all_three_benchmark_worlds`.

### Edge 7: Benchmark World / Ref Invariant Drift

- Risk:
  typed benchmark rows could still carry contradictory posture if world kind and ref
  kind are not frozen together.
- Response:
  require exact invariants between local-eval world and local-eval ref, scorecard
  world and scorecard ref, and behavior-evidence world and behavior-evidence ref.
- Closeout Evidence:
  row invariants in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  reject spec
  `packages/adeu_semantic_source/tests/fixtures/v47f/reject_world_ref_kind_mismatch_spec.json`,
  and tests `test_v47f_rejects_world_ref_kind_mismatch` plus
  `test_v47f_rejects_world_ref_kind_mismatch` in the model lane.

### Edge 8: Upstream Profile Bypass

- Risk:
  benchmark consumer rows could bind directly to raw refs in a way that ignores
  already released `V47-C`, `V47-D`, and `V47-E` profile doctrine where those
  surfaces remain relevant.
- Response:
  require benchmark consumer binding to respect released upstream ANM profiles rather
  than bypassing them through raw ref resolution alone, and fail closed when the
  required upstream doctrine joins are dangling, stale, or unresolved against the
  declared snapshot/source scope.
- Closeout Evidence:
  required coexistence / ownership / downstream consumer profile inputs in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  reject spec
  `packages/adeu_semantic_source/tests/fixtures/v47f/reject_bypass_upstream_profile_spec.json`,
  and test `test_v47f_rejects_bypass_upstream_profile`.

### Edge 9: Action-Vocabulary Creep

- Risk:
  benchmark consumer rows could claim vague downstream “effects” without freezing
  which constrain-only actions are actually allowed in this bounded slice.
- Response:
  enumerate benchmark consumer actions exactly and require all row action fields to
  draw from the same frozen vocabulary, remain pairwise disjoint, and stay consistent
  with the row's explicit authority relation.
- Closeout Evidence:
  `AllowedBenchmarkConsumerAction` typing and action-list validation in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  committed profile fixture,
  and tests `test_v47f_vocabularies_are_exact` and
  `test_v47f_rejects_overlapping_action_lists`.

### Edge 10: Benchmark-Family Overreach

- Risk:
  the benchmark-world consumer seam could have quietly acted like a partial `V46`
  benchmark-family release.
- Response:
  keep `V47-F` bounded to consumer doctrine over already released benchmark artifacts,
  not family-level benchmark specs, projections, execution contexts, or diagnostics as
  a new released substrate.
- Closeout Evidence:
  frozen `V47-F` lock scope in `docs/LOCKED_CONTINUATION_vNEXT_PLUS111.md`,
  bounded world vocabulary in `anm_models.py`, and absence of any `V46` benchmark
  family schema or package ownership widening in the committed `v47f` surfaces.

### Edge 11: Snapshot / Source-Scope Drift

- Risk:
  benchmark consumer rows could bind together incompatible snapshots or source scopes
  across the released ANM stack and benchmark artifact worlds.
- Response:
  require same snapshot identity and explicit artifact-local source-scope compatibility
  checks, including fail-closed rejection for unresolved benchmark refs, repo-root
  escapes, and unreadable files.
- Closeout Evidence:
  same-snapshot/source-scope and benchmark-ref validation in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  reject spec
  `packages/adeu_semantic_source/tests/fixtures/v47f/reject_unresolved_local_eval_ref_spec.json`,
  and tests `test_v47f_rejects_unresolved_local_eval_ref`,
  `test_v47f_rejects_benchmark_ref_outside_repo_root`, and
  `test_v47f_wraps_unreadable_benchmark_ref_as_compile_error`.

### Edge 12: Package-Boundary Sprawl

- Risk:
  a benchmark-consumer lane could sprawl into benchmark-domain packages or operator
  systems before the bounded profile surface is stable.
- Response:
  keep `V47-F` bounded to `adeu_semantic_source` plus `adeu_commitments_ir` and treat
  released benchmark artifacts as consumed inputs, not new owning implementation
  domains in this slice.
- Closeout Evidence:
  shipped implementation footprint in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  and bounded package selection in `docs/LOCKED_CONTINUATION_vNEXT_PLUS111.md`.

## Current Judgment

- `V47-F` was the right next move because `V47-A` through `V47-E` had already released
  the bounded ANM substrate, hardening layer, coexistence/adoption doctrine,
  ownership-transition doctrine, and descriptive/runtime consumer seams on `main`,
  while typed benchmark-world consumer posture remained the last unclosed internal gap
  in this family.
- `V47-F` on `main` now resolves that gap by shipping one typed benchmark consumer
  profile with explicit local-eval, scorecard, and behavior-evidence worlds, exactly
  one bound released `D-IR` clause source per row, support-only result/ledger posture,
  explicit world/ref-kind invariants, and fail-closed upstream-profile respect.
- the shipped seam remains doctrine-first and non-authorizing, so `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`
  can now record the bounded `V47` ladder as complete on `main` without silently
  granting `V46` benchmark-family release, official benchmark authority, execution,
  approval, migration, waiver, or deferral power.
