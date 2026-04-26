# Architecture ADEU Candidate Ratification Review Family v0

Status: architecture / decomposition record for planned `V71`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V71` downstream of closed `V68` cartography, closed `V69`
candidate intake, and closed `V70` candidate review classification.

## 1. Family Thesis

`V71` is the candidate ratification-review family.

It should make the repo able to turn classified candidate review state into a
typed ratification, rejection, deferral, settlement, or future-family routing
record without confusing ratification with implementation or release authority.

`V71` may say:

- this `V70-C` handoff is eligible for ratification review;
- this candidate is ratified for a bounded later review surface;
- this candidate is rejected for this horizon;
- this candidate is deferred pending evidence, settlement, or future-family
  review;
- this conflict is settled for the bounded candidate horizon;
- this dissent or unresolved blocker remains carried forward;
- this ratified candidate has a specific amendment-scope boundary.

`V71` must not say:

- implementation should begin;
- files may be edited;
- a PR may be opened;
- release or merge authority is granted;
- a product surface is selected;
- runtime permission or dispatch is authorized.

## 2. Relationship To `V68`, `V69`, And `V70`

`V68` provides the map substrate:

- source rows and authority layers;
- family / slice / arc namespace disambiguation;
- support lineage;
- evidence surface indexing;
- tool applicability boundaries;
- coordinate posture.

`V69` provides candidate substrate:

- source-bound candidate rows;
- source registers and source absence posture;
- non-adoption guardrails;
- derivation manifests and gap scans;
- operator-ingress bindings;
- recursive workflow residue reports.

`V70` provides review substrate:

- evidence source index;
- claim and classification rows;
- adversarial review matrix;
- conflict / complementarity register;
- review gap scan;
- classification summary;
- pre-ratification handoff rows.

`V71` consumes those substrates. It should not weaken them by treating
cartography as authority, intake as adoption, or review classification as a
ratified decision.

## 3. Core Separations

| Lane | Question | Forbidden collapse |
|---|---|---|
| Handoff input | Which `V70-C` handoff is under ratification review? | Inventing a ratification candidate outside released `V70-C` rows |
| Authority profile | Who or what can ratify this horizon? | Treating a model review, tool pass, transcript, or support doc as ratification authority |
| Ratification request | What is being asked for? | Treating a request as a decision |
| Settlement | Which conflict or dissent is resolved or carried forward? | Treating unresolved review gaps as settled because a row exists |
| Ratification record | What decision posture is recorded? | Treating ratification as implementation, merge, release, or product authority |
| Amendment scope | What may a later family consider? | Treating scope as permission to edit files or release |
| Handoff posture | What later family should evaluate next? | Jumping to `V72`, `V74`, or `V75` without a bounded handoff record |

## 4. ODEU Ratification Posture

Ratification should preserve ODEU lane information with an `odeu_lanes` field.
The field should be a sorted, non-empty list even when the row is single-lane.

Minimum lane values:

- `ontological`
- `deontic`
- `epistemic`
- `utility`

The same candidate may be ratified for one horizon and deferred or rejected for
another. Epistemic ratification cannot become deontic permission. Utility
ratification cannot become product selection.

## 5. Authority Profile Binding

Ratification authority should be represented explicitly, not implied by
conversation or tool success.

Minimum authority actor kinds:

- `human_operator`
- `maintainer`
- `model_reviewer`
- `tool_validator`
- `external_reviewer`

Minimum authority grant source kinds:

- `repo_lock`
- `closeout_decision`
- `maintainer_record`
- `policy_doc`
- `support_doc`
- `transcript`
- `tool_output`

Minimum authority postures:

- `ratification_authority`
- `settlement_authority`
- `review_only`
- `advisory_only`
- `tool_evidence_only`
- `not_authorized`

Model reviewers, tool validators, support docs, and transcript content should
default to non-ratifying roles unless an explicit lock-level or maintainer-grant
source creates a narrower authority posture.

## 6. Ratification Outcome Vocabulary

Minimum decision posture:

- `ratified`
- `rejected`
- `deferred`
- `out_of_scope`

Minimum ratification horizon:

- `source_bound_candidate_validity`
- `review_conflict_settlement`
- `authority_boundary_acceptance`
- `future_family_routing`
- `integration_review_readiness`
- `utility_projection_acceptance`

Minimum allowed next review surface:

- `v72_contained_integration_review`
- `future_family_review`
- `deferred_no_selection`

`decision_posture = ratified` with
`ratification_horizon = integration_review_readiness` means the candidate may be
considered by `V72`. It does not authorize implementation, merge, release,
rollback, or runtime action.

## 7. Settlement Vocabulary

Minimum settlement posture:

- `settled_for_candidate_horizon`
- `partially_settled_with_dissent`
- `blocked_by_unresolved_conflict`
- `blocked_by_unresolved_gap`
- `requires_more_evidence`
- `requires_human_review`
- `future_family_only`

Minimum dissent posture:

- `no_dissent_recorded`
- `dissent_carried_forward`
- `minority_review_preserved`
- `unresolved_blocker`
- `not_applicable`

Minimum dissent search posture:

- `searched_none_found`
- `not_searched`
- `not_applicable`
- `dissent_present`
- `unknown`

`no_dissent_recorded` is not proof that dissent is absent unless the row also
records a searched horizon.

Minimum review signal posture:

- `warning_only`
- `gating_blocker`
- `settlement_required`
- `evidence_required`
- `human_review_required`
- `future_family_only`

## 8. Family Surfaces

Expected surfaces:

| Surface | Likely slice | Role |
|---|---|---|
| `repo_candidate_ratification_request@1` | `V71-A` | source-bound request rows over released `V70-C` handoffs |
| `repo_ratification_authority_profile@1` | `V71-A` | explicit actor / source / authority posture rows for ratification review |
| `repo_ratification_request_scope_boundary@1` | `V71-A` | bounds what the ratification request may ask for and forbids downstream roles |
| `repo_candidate_ratification_record@1` | `V71-B` | ratification / rejection / deferral outcome rows |
| `repo_review_settlement_record@1` | `V71-B` | settlement rows over V70 conflicts, gaps, dissent, and carry-forward blockers |
| `repo_ratification_dissent_register@1` | `V71-B` | dissent or unresolved minority-review rows preserved after settlement |
| `repo_ratification_amendment_scope_boundary@1` | `V71-C` | bounded amendment-scope rows for later families |
| `repo_post_ratification_handoff@1` | `V71-C` | handoff rows to `V72`, future-family review, or deferral without integration |

Names may be standardized before lock. If the `repo_*` namespace is retained,
the lock should say these are repo-description ratification-review surfaces, not
runtime, release, product, or ARC challenge artifacts.

## 9. Family Slices

### 9.1 `V71-A`

Ratification request and authority-profile starter.

Owns:

- ratification request rows seeded from released `V70-C` handoff rows;
- ratification source rows with source presence posture;
- authority profile rows;
- request-scope boundary rows;
- eligibility classification for `ready_for_v71_review`,
  `blocked_by_conflict`, `deferred_to_future_family`, and out-of-scope rows;
- reject fixtures for source-free ratification requests, model self-ratification,
  support doc as ratification authority, and product wedge promoted to `V71`.

Does not own:

- final ratification outcomes;
- settlement records;
- amendment scope;
- implementation scheduling;
- product projection;
- release authority;
- dispatch widening.

### 9.2 `V71-B`

Settlement and ratification records.

Owns:

- ratification outcome rows;
- settlement records over V70 conflicts, gaps, and handoff blockers;
- dissent register rows;
- rejection / deferral / ratification posture validation;
- negative controls preventing unresolved blockers from being ratified.

Does not own:

- contained integration;
- implementation tickets;
- product workbench selection;
- outcome review;
- dispatch.

### 9.3 `V71-C`

Amendment-scope hardening and post-ratification handoff.

Owns:

- amendment-scope boundary rows over ratified or deferred candidates;
- post-ratification handoff rows to `V72` or future-family review;
- family closeout evidence proving ratification remains non-implementation;
- carry-forward of rejected, deferred, and dissent rows.

Does not own:

- `V72` integration or release posture;
- `V73` outcome review;
- `V74` product projection;
- `V75` dispatch.

## 10. Negative Laws

`V71` must reject or refuse to represent as ratified:

- candidate absent from released `V70-C` summary / handoff substrate;
- ratification request with no source refs;
- support doc as ratification authority;
- model output as self-ratification;
- tool pass as ratification proof;
- transcript content as truth or ratification authority;
- unresolved blocking conflict ratified without settlement;
- unresolved blocking evidence gap ratified without deferral or explicit
  carry-forward;
- product wedge routed to `V71` instead of future-family review;
- ratification outcome that creates implementation, release, product, runtime,
  or dispatch authority;
- post-ratification handoff that performs `V72` integration.

## 11. Source Rows

`V71-A` should define explicit ratification source rows so source absence remains
data rather than prose memory.

Minimum ratification source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `source_horizon`
- `limitation_note`

Every request row, authority profile row, summary ref, handoff ref, and
request-scope boundary row should resolve through concrete source rows or
explicit absence rows.

## 12. Expected Family Closeout

`V71` should close with a typed ratification substrate ready for `V72`
contained-integration review where applicable. It should not claim that any
ratified candidate has been implemented, merged, released, productized, or
dispatched.
