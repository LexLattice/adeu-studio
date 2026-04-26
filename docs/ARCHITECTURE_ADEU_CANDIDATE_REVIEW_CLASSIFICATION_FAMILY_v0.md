# Architecture ADEU Candidate Review Classification Family v0

Status: architecture / decomposition record for planned `V70`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V70` downstream of closed `V68` cartography and closed `V69`
candidate intake.

## 1. Family Thesis

`V70` is the candidate review-classification family.

It should make the repo able to classify candidate evidence, adversarial-review
needs, conflicts, and pre-ratification readiness without confusing review
classification with ratification or adoption.

`V70` may say:

- this source exists and is bound to this candidate;
- this source is evidence for this claim horizon;
- this source is not evidence for this claim horizon;
- this claim requires adversarial review;
- these reviews conflict or complement each other;
- this candidate is ready to be handed to a later ratification review surface.

`V70` must not say:

- the candidate is true;
- the candidate is adopted;
- the candidate is ratified;
- implementation should begin;
- product projection is selected;
- release or dispatch is authorized.

## 2. Relationship To `V68` And `V69`

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
- recursive workflow residue reports;
- pre-`V70` handoff rows.

`V70` consumes both. It should not weaken either by turning cartography into
candidate adoption or candidate intake into evidence settlement.

## 3. Core Separations

| Lane | Question | Forbidden collapse |
|---|---|---|
| Candidate input | Which `V69` candidate is under review? | Inventing an unadmitted candidate inside `V70` |
| Evidence source | Which concrete source supports review? | Treating a glob, absent source, or support prose memory as evidence |
| Claim identity | Which candidate claim is being classified? | Letting dangling `claim_ref` values acquire meaning by implication |
| Claim horizon | What kind of claim is being classified? | Treating source existence as truth of the candidate |
| Evidence classification | How does the source bear on the claim horizon? | Treating classification as ratification |
| Adversarial review | What counter-review or opposing frame is required? | Treating one model output as settled truth |
| Review relation | What conflicts or complementarities shape later review? | Silently resolving conflict or dropping complementarity inside `V70` |
| Handoff posture | What later surface should evaluate the classified candidate? | Selecting implementation, product, release, or dispatch |

## 4. ODEU Classification Posture

Every review classification should preserve ODEU lane information with an
`odeu_lanes` field. The field should be a sorted, non-empty list even when the
row is single-lane.

Minimum lane values:

- `ontological`
- `deontic`
- `epistemic`
- `utility`

The same candidate may produce multiple classification rows, one per lane or
claim horizon. A utility classification cannot become ontological proof. A
deontic boundary classification cannot become product selection.

## 5. Evidence Source Binding

Evidence-source rows should use one concrete `source_ref` per row. Claim
classification rows should reference those rows through `evidence_source_refs`.

Missing or stale evidence is represented by an explicit evidence-source row with
source absence or staleness posture, not by a source-free classification row.
That preserves the `V69` rule that absence is recorded as data rather than
floating memory.

## 6. Evidence Classification Vocabulary

Minimum evidence classification values:

- `source_bound_for_review`
- `supports_review_claim`
- `contradicts_review_claim`
- `insufficient_evidence`
- `not_evidence_for_claim`
- `requires_adversarial_review`
- `authority_boundary_blocked`
- `tool_applicability_unknown`
- `source_missing_or_stale`

These are review classifications. They are not truth verdicts and are not
ratification outcomes.

## 7. Claim Horizon Vocabulary

Minimum claim horizons:

- `source_existence`
- `candidate_well_formedness`
- `evidence_support`
- `authority_boundary`
- `adversarial_review_need`
- `conflict_presence`
- `pre_ratification_readiness`
- `utility_projection`

`pre_ratification_readiness` means ready for a later review surface to consider.
It does not mean ratified, and it should mainly appear after adversarial review
and gap scan context exists rather than as a broad positive `V70-A` starter
claim.

## 8. Adversarial Review Vocabulary

Minimum adversarial review posture:

- `not_required_for_this_claim`
- `required_not_started`
- `required_present`
- `required_inconclusive`
- `conflict_detected`
- `blocked_missing_counterevidence`
- `deferred_to_future_family_review`

Model-output comparison candidates should default to requiring adversarial review
unless a later lock says otherwise. If a row uses
`evidence_classification = requires_adversarial_review`, its
`adversarial_review_posture` must not be `not_required_for_this_claim`.

## 9. Family Surfaces

Expected surfaces:

| Surface | Likely slice | Role |
|---|---|---|
| `repo_candidate_evidence_classification_record@1` | `V70-A` | candidate claim registry and evidence classification rows over `V69` handoff inputs |
| `repo_candidate_evidence_source_index@1` | `V70-A` | evidence-source rows with source, authority, evidence kind, claim horizon, and limitation posture |
| `repo_candidate_review_boundary_guardrail@1` | `V70-A` | negative-law guardrails preventing classification from becoming adoption, ratification, release, product, or dispatch |
| `repo_candidate_adversarial_review_matrix@1` | `V70-B` | adversarial review rows across candidate, claim, perspective, source, and reviewer posture |
| `repo_candidate_review_conflict_register@1` | `V70-B` | conflict and complementarity rows that block or shape later review |
| `repo_candidate_review_gap_scan@1` | `V70-B` | missing evidence, missing counterevidence, stale source, single-source overclaim, and authority-boundary gaps |
| `repo_candidate_review_classification_summary@1` | `V70-C` | bounded summary of classified candidates and unresolved review gaps |
| `repo_candidate_pre_ratification_handoff@1` | `V70-C` | handoff rows to `V71` or future-family review without ratification |

Names may be standardized before lock. If the `repo_*` namespace is retained,
the lock should say these are repo-description review-classification surfaces,
not ARC challenge artifacts.

## 10. Family Slices

### 10.1 `V70-A`

Evidence classification starter.

Owns:

- evidence source index;
- claim registry rows;
- candidate claim classification rows;
- claim horizon and evidence classification enums;
- review-boundary guardrails;
- reference fixture seeded from the `V69-C` pre-`V70` handoff;
- reject fixtures for source-free evidence, embedded ratification, and authority
  laundering;
- reject fixtures for dangling `claim_ref` values and source-free
  missing-evidence rows.

Does not own:

- adversarial review matrix;
- conflict settlement;
- ratification;
- implementation scheduling;
- product projection;
- release authority;
- dispatch widening.

### 10.2 `V70-B`

Adversarial review and conflict classification.

Owns:

- adversarial review matrix;
- review perspective rows;
- conflict and complementarity register;
- review gap scan;
- negative controls for model-output comparison and single-source overclaim.

Does not own:

- ratification or final settlement;
- implementation priority;
- product workbench selection;
- outcome review.

The relation register should be able to represent at least:

- `conflict`
- `complementarity`
- `orthogonal`
- `duplicate`
- `unclear_relation`

### 10.3 `V70-C`

Classification synthesis and pre-ratification handoff.

Owns:

- review classification summary;
- unresolved gap carry-forward;
- pre-`V71` handoff rows;
- handoff posture rows that distinguish readiness from blocked or deferred
  carry-forward;
- family closeout evidence proving classification remains non-ratifying.

Does not own:

- `V71` ratification;
- `V72` contained integration;
- `V73` outcome review;
- `V74` product projection;
- `V75` dispatch.

Minimum handoff posture:

- `ready_for_v71_review`
- `blocked_by_conflict`
- `blocked_by_evidence_gap`
- `blocked_by_authority_boundary`
- `deferred_to_future_family`
- `rejected_out_of_scope`

## 11. Negative Laws

`V70` must reject or refuse to represent as review-classified:

- candidate not admitted by `V69` unless explicitly represented as a rejected
  unknown candidate input;
- classification row whose `claim_ref` does not point to a claim registry row;
- evidence-source row whose singular `source_ref` does not point to a known
  source row or explicit source absence posture;
- source-missing or stale classification that has no explicit absence-posture
  evidence-source row;
- glob promoted to evidence source;
- support doc treated as lock authority;
- candidate intake row treated as evidence of truth;
- evidence classification treated as ratification;
- adversarial review treated as settlement;
- conflict register row silently resolved without later review;
- product pressure treated as `V74` selection;
- pre-ratification handoff treated as `V71` ratification;
- handoff with unresolved blocking conflicts or gaps treated as ready without a
  blocked or deferred posture;
- implementation ticket emitted from review classification;
- commit/release or dispatch authority emitted from review classification.

## 12. Closeout Expectation

A closed `V70` family should leave the repo with a typed review-classification
substrate ready for `V71` ratification review. It should not claim that any
candidate has been ratified, adopted, implemented, released, productized, or
dispatched.
