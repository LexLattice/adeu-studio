# Draft ADEU Reconciliation Arbiter V76B Implementation Mapping v0

Status: support note for the planned `V76-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V76-B`
should harden arbiter authority, settlement requests, adversarial relation
review, and gap scanning after `V76-A` has shipped.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v66.md`
- `docs/ARCHITECTURE_ADEU_RECONCILIATION_ARBITER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RECONCILIATION_ARBITER_V76_PLANNING_v0.md`

## Workflow Posture

This `V76-B` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V76-B` becomes active, it should receive its own canonical starter trio
after `V76-A` merges and receives lean closeout. `V76-B` must consume released
`V76-A` claim map, relation register, and dissent register rows rather than
creating a parallel reconciliation universe.

## Candidate New Surfaces

`V76-B` should select:

- `repo_arbiter_authority_profile@1`
- `repo_reconciliation_settlement_request@1`
- `repo_adversarial_relation_review@1`
- `repo_reconciliation_gap_scan@1`

These surfaces should make later arbiter / settlement review governable
without performing settlement, ratification, runtime execution, product
authorization, release, or external branch activation.

## Arbiter Authority Profile

Authority profile rows should record:

- `authority_profile_ref`
- `authority_actor_kind`
- `authority_grant_source_kind`
- `authority_source_refs`
- `allowed_relation_horizons`
- `allowed_review_actions`
- `forbidden_authority_kinds`
- `authority_gap_posture`
- `limitation_note`

Actor and grant source should remain separate. A model, tool, support doc, or
transcript may provide evidence or review context; it does not become truth or
settlement authority by itself.

Minimum allowed review action:

- `inspect_relation`
- `request_adversarial_review`
- `preserve_dissent`
- `classify_gap`
- `request_later_settlement_review`
- `request_future_family_review`

Forbidden authority action:

- `settle_relation_now`
- `ratify_claim_now`
- `declare_truth_now`
- `authorize_runtime_now`
- `authorize_product_now`
- `authorize_release_now`

## Settlement Request

Settlement request rows should record:

- `settlement_request_ref`
- `claim_map_refs`
- `relation_refs`
- `dissent_refs`
- `authority_profile_refs`
- `requested_settlement_horizon`
- `settlement_request_posture`
- `required_adversarial_review_refs`
- `carried_gap_refs`
- `non_settlement_guardrail`
- `limitation_note`

Minimum posture:

- `request_ready_for_later_review`
- `blocked_by_authority_gap`
- `blocked_by_unreviewed_relation`
- `blocked_by_dissent`
- `blocked_by_missing_source`
- `future_family_only`
- `rejected_out_of_scope`

The request may ask for later settlement review. It must not perform
settlement or ratification.

For each settlement request, `requested_settlement_horizon` must be included in
every referenced authority profile's `allowed_relation_horizons`.

## Adversarial Relation Review

Adversarial review rows should record:

- `adversarial_review_ref`
- `claim_map_refs`
- `relation_refs`
- `review_perspective`
- `counterclaim_horizon`
- `negative_control_refs`
- `review_result_posture`
- `source_refs`
- `limitation_note`

Minimum posture:

- `counterevidence_found`
- `complementarity_found`
- `no_counterevidence_in_checked_horizon`
- `inconclusive`
- `blocked_by_missing_source`

No-counterevidence claims require a checked horizon or negative control refs.

## Gap Scan

Gap rows should record:

- `gap_ref`
- `claim_map_refs`
- `relation_refs`
- `gap_kind`
- `gap_severity`
- `blocking_posture`
- `required_next_surface`
- `source_refs`
- `limitation_note`

Minimum gap kind:

- `missing_claim_map_source`
- `missing_relation_source`
- `unreviewed_dissent`
- `authority_profile_missing`
- `adversarial_review_missing`
- `product_authority_gap`
- `runtime_authority_gap`
- `external_branch_gap`
- `projected_slot_not_observed_for_content_claim`
- `observed_output_source_authority_missing`
- `benchmark_truth_guardrail_missing`
- `unknown_needs_review`

Gaps must not become implementation priority or downstream authority.

## Mandatory Reject Cases

- authority profile treating model, tool, support doc, or transcript as truth
  authority;
- settlement request with unknown `V76-A` claim map refs;
- settlement request that performs settlement or ratification;
- settlement request that ignores blocking dissent;
- adversarial review claiming no counterevidence without checked horizon;
- relation with conflict or unclear posture marked ready without adversarial
  review or carried gap;
- product, runtime, release, external branch, or recursive-policy authority
  gap converted into settlement readiness;
- majority agreement converted into correctness or settlement readiness without
  source-bound relation review and authority profile coverage;
- gap scan row converted into implementation priority;
- any row authorizing worker assignment, command execution, dispatch, runtime
  permission, product authorization, PR creation, commit, merge, release,
  benchmark truth, global model selection, living-memory authority, or
  recursive policy amendment.

## Reference Fixture Intent

The reference fixture should extend released `V76-A` rows with:

- one review-only arbiter authority profile;
- one settlement request for the self-evidencing workflow-type emergence
  candidate that remains review-only;
- one blocked product-wedge settlement request carrying product authority gap;
- one adversarial relation review over the self-evidencing relation horizon;
- one gap scan row that keeps authority gaps visible.
