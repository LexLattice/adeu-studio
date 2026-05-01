# Draft ADEU Reconciliation Arbiter V76A Implementation Mapping v0

Status: support note for the planned `V76-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V76-A`
should add reconciliation claim maps, arbiter relation registers, and
reconciliation dissent registers after `V75` has closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v66.md`
- `docs/ARCHITECTURE_ADEU_RECONCILIATION_ARBITER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RECONCILIATION_ARBITER_V76_PLANNING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_COMBINED_DOGFOOD_TEST_v0.md`

## Workflow Posture

This `V76-A` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V76-A` becomes active, it should receive its own canonical starter trio
after review patches are integrated. The already drafted `vNext+212` trio is
the intended scaffold for that later activation.

The active `V76-A` implementation may add its own schema, model, validator,
fixture, and test files under the future lock. That is distinct from arbiter
settlement, runtime permission, dispatch execution, product authorization,
release, or external contest implementation.

## Candidate New Surfaces

`V76-A` should select:

- `repo_reconciliation_claim_map@1`
- `repo_arbiter_relation_register@1`
- `repo_reconciliation_dissent_register@1`

These surfaces should translate released `V75-C` reconciliation / relation /
handoff substrate into bounded reconciliation-review posture without settling
truth.

## Source Binding

`V76-A` should define explicit reconciliation source rows over:

- `artifacts/agent_harness/v211/evidence_inputs/v75_family_closeout_alignment_v211.json`
- `artifacts/agent_harness/v211/evidence_inputs/v75c_dispatch_review_closeout_evidence_v211.json`
- `apps/api/fixtures/repo_description/vnext_plus211/repo_worker_output_reconciliation_plan_v211_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus211/repo_dispatch_reconciliation_contract_v211_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus211/repo_post_dispatch_review_handoff_v211_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus211/repo_dispatch_review_family_closeout_alignment_v211_reference.json`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_COMBINED_DOGFOOD_TEST_v0.json`

Absence should be represented as source posture, not as prose memory.

## Reconciliation Claim Map

The claim map should record:

- `claim_map_ref`
- `candidate_ref`
- `output_claim_ref`
- `claim_kind`
- `claim_label`
- `reconciliation_plan_refs`
- `projected_output_slot_refs`
- `observed_worker_output_refs`
- `v75_source_relation_refs`
- `handoff_refs`
- `claim_horizon`
- `claim_source_refs`
- `claim_presence_posture`
- `output_presence_posture`
- `claim_map_posture`
- `source_refs`
- `truth_status_forbidden`
- `non_truth_guardrail`
- `limitation_note`

Conditional validation:

- if `output_presence_posture = projected_not_observed`, then
  `observed_worker_output_refs` must be empty;
- if `output_presence_posture = projected_not_observed`, then `claim_kind`
  must be `projected_output_slot_existence`,
  `projected_relation_review_need`, or `relation_placeholder_claim`;
- `projected_not_observed` rows must not imply content review of an observed
  output;
- observed worker output refs require authorized prior-run or support-artifact
  source posture;
- claim maps must reference released `V75-C` reconciliation plan rows or
  explicit absence markers;
- claim maps reference released `V75-C` relation rows through
  `v75_source_relation_refs`; they must not point to new `V76-A` arbiter
  relation rows;
- claim maps must not claim truth, settlement, ratification, runtime
  permission, dispatch execution, product authorization, release, or external
  participation.
- if source or handoff material carries product, runtime, release, external
  branch, dispatch-execution, or recursive-policy authority blockers,
  `claim_map_posture` must remain blocked or future-family-only unless the
  required next review surface preserves the blocker for that later family.

## Arbiter Relation Register

The relation register should record:

- `arbiter_relation_ref`
- `claim_map_refs`
- `source_relation_refs`
- `relation_kind`
- `relation_review_posture`
- `arbiter_need_posture`
- `required_next_review_surface`
- `source_refs`
- `non_truth_guardrail`
- `limitation_note`

Relation rows may preserve conflict, complementarity, duplication,
orthogonality, unclear relation, or single-output/no-relation posture. They
must not settle the relation.

If `output_presence_posture = projected_not_observed`, relation review posture
must not imply an observed-output conflict. It may record placeholder,
single-output, missing-source, or later-review need posture only.

`source_relation_refs` point to released `V75-C` relation rows under review.
`claim_map_refs` point to `V76-A` claim map rows. This avoids circular claim
maps that reference arbiter relation rows before those rows exist.

## Reconciliation Dissent Register

The dissent register should record:

- `dissent_ref`
- `claim_map_refs`
- `relation_refs`
- `dissent_kind`
- `dissent_presence_posture`
- `dissent_search_horizon_refs`
- `dissent_search_coverage_posture`
- `checked_source_refs`
- `unchecked_source_refs`
- `dissent_source_refs`
- `dissent_carry_forward_posture`
- `limitation_note`

`searched_none_found`, `not_searched`, `unknown`, and `not_applicable` must
remain distinct. `no dissent recorded` cannot be treated as proof of absence
without a source-bound searched horizon.

`searched_none_found` rows require explicit `dissent_search_horizon_refs`,
non-empty `checked_source_refs`, and a coverage posture that states what was
actually searched.

## Mandatory Reject Cases

- claim map with unknown reconciliation plan refs;
- claim map with no source refs;
- missing source without explicit absence posture;
- projected output slot treated as observed worker output;
- projected output slot mapped as observed output-content claim;
- observed worker output without authorized source posture;
- relation register row without claim map refs;
- relation register row claiming truth or settlement;
- dissent row with unknown relation refs;
- no-dissent claim without searched horizon;
- product / runtime / external authority blockers converted into arbiter
  readiness;
- majority agreement converted into correctness or settlement readiness;
- model-output comparison converted into benchmark truth;
- `V76-A` fixture emitting `V76-B` authority / settlement surfaces;
- `V76-A` fixture emitting `V76-C` summary / handoff / closeout surfaces.

## Reference Fixture Intent

The first fixture should include:

- one self-evidencing workflow-type emergence candidate mapped from the
  `V75-C` projected output slot and single-output/no-relation row;
- one typed-adjudication product wedge candidate kept blocked by product
  authority requirements;
- one dissent row that demonstrates searched absence versus unknown coverage;
- non-truth guardrails on every claim and relation row;
- zero arbiter settlement, ratification, runtime permission, dispatch
  execution, product authorization, release, external contest participation, or
  recursive policy amendment.
