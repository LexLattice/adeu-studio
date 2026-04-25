# Architecture ADEU Recursive Candidate Intake Family v0

Status: architecture / decomposition record for planned `V69`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V69` downstream of the closed `V68` cartography family and the
support-layer `V69` preflight dogfood test.

The GPTPro review captured in
`docs/support/arc_series_mapping/REVIEW_GPTPRO_RECURSIVE_CANDIDATE_INTAKE_V69_PLANNING_v0.md`
is integrated as support-layer shaping evidence, not as lock authority.

## 1. Family Thesis

`V69` is the recursive candidate intake family.

It should make the repo able to admit candidate pressure into typed records without
confusing admission with adoption. A candidate may come from an internal reasoning
loop, support doc, operator turn, model output, review artifact, repo observation,
or external artifact. `V69` records that the candidate exists, where it came from,
which ODEU lane it pressures, what role it may play next, and what it is forbidden
to become without later review.

The family must remain pre-adjudicative. It does not itself classify evidence,
settle adversarial reviews, ratify candidates, integrate implementation work,
authorize release, project product surfaces, or widen execution.

## 2. Relationship To `V68`

`V68` provides the map substrate:

- source rows and authority layers;
- family / slice / arc namespace disambiguation;
- support lineage;
- evidence surface indexing;
- tool applicability boundaries;
- coordinate posture.

`V69` consumes that substrate and adds candidate-intake records over it. `V69`
should not weaken `V68` by treating a mapped source as an adopted candidate or a
candidate as future-family authority.

## 3. Core Separations

The family must keep these lanes distinct.

| Lane | Question | Forbidden collapse |
|---|---|---|
| Candidate identity | What candidate is being admitted? | Treating a similar phrase in another doc as the same candidate without equivalence posture |
| Source binding | Which concrete source artifacts or turns produced the candidate? | Treating a glob, memory, or uncommitted conversation as an integrated source |
| Origin class | What kind of origin produced the candidate? | Treating internal reasoning residue like external evidence, or review feedback like a lock |
| ODEU lane | Which O/E/D/U pressures does the candidate express, and which is primary? | Letting utility pressure masquerade as ontological or deontic proof, or flattening multi-lane pressure into opaque `mixed` |
| Admissible role | What may this candidate be used for next? | Treating intake as adoption |
| Forbidden role | What must this candidate not become yet? | Letting candidate records schedule, ratify, release, or implement |
| Review handoff | What later surface must evaluate the candidate? | Running evidence classification or ratification inside `V69` |

## 4. Candidate Origin Vocabulary

Minimum origin classes:

- `internal_reasoning_residue`
- `external_artifact`
- `operator_turn`
- `model_output`
- `support_doc`
- `review_feedback`
- `repo_observation`
- `planning_pressure`

The origin class is descriptive. It does not imply trust, priority, proof, or
authority.

## 4.1 ODEU Lane Posture

The starter should support both a primary lane and a multi-lane pressure profile:

- `primary_odeu_lane`
- `odeu_lanes`

Allowed lane values:

- `ontological`
- `deontic`
- `epistemic`
- `utility`

`mixed` may remain as a compatibility value for `primary_odeu_lane`, but it should
be rejected when `odeu_lanes` is absent. A product wedge, for example, can carry
ontology, epistemology, deontic boundary, and utility pressure at once.

## 5. Intake Posture

Minimum intake posture:

- `intake_candidate`
- `intake_duplicate`
- `intake_rejected_out_of_scope`
- `intake_deferred_to_later_family`
- `intake_requires_v70_review`
- `intake_superseded`
- `intake_unknown_needs_review`

An intake record with `intake_candidate` is merely admitted for tracking. It is not
adopted, selected, ratified, integrated, or released.

## 6. Candidate Role Vocabulary

Minimum admissible role examples:

- `support_input`
- `schema_candidate`
- `planning_pressure`
- `review_input`
- `evidence_review_request`
- `future_family_candidate`
- `product_projection_candidate`
- `operator_ingress_binding`

Minimum forbidden role examples:

- `lock_authority`
- `released_schema`
- `ratified_decision`
- `implementation_task`
- `commit_release_authority`
- `product_authorization`
- `dispatch_authority`
- `self_validation`
- `transcript_truth`

Every candidate record must carry risk-aware forbidden roles and a non-adoption
guardrail. The family should fail closed when the guardrail is absent.

Minimum risk-aware requirements:

| Condition | Required forbidden roles |
|---|---|
| `admissible_roles` includes `schema_candidate` | `released_schema` |
| `admissible_roles` includes `product_projection_candidate` | `product_authorization` |
| `admissible_roles` includes `future_family_candidate` | `lock_authority`, `implementation_task` |
| `origin_class` is `model_output` | `ratified_decision`, `self_validation` |
| `origin_class` is `operator_turn` | `transcript_truth`, `lock_authority` |

## 6.1 Review Target Split

`V69` must separate the immediate review surface from any eventual family hint.

Minimum `required_next_review_surface` values:

- `v70_evidence_classification`
- `v70_adversarial_review`
- `future_family_review`
- `none_yet_deferred`

Minimum `eventual_family_hint` values:

- `v71_ratification`
- `v72_integration_review`
- `v73_outcome_review`
- `v74_operator_projection_review`
- `v75_dispatch_review`
- `v43_external_contest_branch`
- `none`

This lets a product wedge point toward `V74` without `V69` selecting `V74`, and it
lets integration pressure point toward `V72` without creating implementation
authority.

## 7. Operator-Ingress Boundary

`V69` may include operator ingress only in the narrow sense of binding an
operator-originated turn to a candidate record.

Allowed:

- source ref to an operator turn or committed transcript artifact;
- candidate extraction with explicit source binding;
- ODEU lane assignment;
- admissible and forbidden role assignment;
- required next review surface.

Explicit source absence is represented through a source row with source absence
posture, not by allowing a candidate row to float without `source_refs`.

Forbidden:

- live turn compiler;
- standing operator profile;
- runtime permission surface;
- hidden candidate invention;
- autonomous task scheduling;
- release, merge, or product authorization.

If operator ingress needs those wider capabilities, they belong to later families,
not `V69`.

## 8. Family Surfaces

Expected starter surfaces:

| Surface | Likely slice | Role |
|---|---|---|
| `repo_recursive_candidate_intake_record@1` | `V69-A` | top-level candidate intake record with source, origin, lane, role, and guardrail rows |
| `repo_candidate_source_register@1` | `V69-A` | concrete source references, source presence, authority layer, and source-status posture for candidate inputs |
| `repo_candidate_non_adoption_guardrail@1` | `V69-A` | explicit forbidden-role and next-review requirements |
| `repo_candidate_intake_derivation_manifest@1` | `V69-B` | deterministic observed-input manifest for candidate derivation |
| `repo_candidate_intake_gap_scan@1` | `V69-B` | missing, stale, duplicate, ambiguous, or overclaiming candidate-source gaps |
| `repo_operator_ingress_candidate_binding@1` | `V69-C` | narrow operator-turn-to-candidate binding surface |
| `repo_recursive_workflow_residue_intake_report@1` | `V69-C` | self-evidencing workflow residue captured as candidate intake evidence |
| `repo_candidate_intake_pre_v70_handoff@1` | `V69-C` | handoff register for candidates that require evidence or adversarial review in `V70` |

Names may be standardized before lock. If the `repo_*` namespace is retained, the
lock should say these are repo-description candidate-intake surfaces, not ARC-AGI
task artifacts.

## 9. Family Slices

### 9.1 `V69-A`

Bounded schema-and-validator starter.

Owns:

- candidate intake row shapes;
- source register row shapes;
- origin, posture, role, and guardrail enums;
- reference fixture seeded by the `V69` preflight dogfood candidates;
- reject fixtures for authority laundering and missing guardrails.

Does not own:

- automatic candidate derivation;
- evidence classification;
- adversarial review;
- ratification;
- adoption;
- integration;
- product projection;
- dispatch.

### 9.2 `V69-B`

Deterministic candidate derivation and gap-scan support.

Owns:

- concrete observed-input manifest;
- derivation rows from selected repo/support/planning artifacts;
- candidate equivalence posture;
- missing expected support artifact reporting;
- ambiguous origin or authority-layer reporting;
- gap severity and recommended next review surface.

Does not own:

- adoption or evidence settlement;
- implementation scheduling;
- recursive self-improvement decisioning.

### 9.3 `V69-C`

Operator-ingress and recursive-residue hardening.

Owns:

- source-bound operator-turn candidate bindings;
- recursive workflow residue intake;
- pre-`V70` handoff posture;
- family closeout evidence that candidate intake remains non-adoptive.

Does not own:

- live operator runtime;
- standing operator authority;
- product workbench selection;
- review settlement;
- dispatch widening.

## 10. Negative Laws

`V69` must reject or refuse to represent as admitted:

- candidate whose `source_refs` is empty;
- candidate whose `source_refs` do not point to source rows;
- missing or unavailable source represented outside the source register;
- support doc treated as released schema;
- planning selector treated as lock authority;
- review feedback treated as ratified decision;
- transcript treated as truth;
- model output treated as adoption;
- operator turn that silently invents an unsourced candidate;
- duplicate candidate without equivalence posture;
- candidate record without non-adoption guardrail;
- `V70` evidence classification embedded inside intake;
- `V71` ratification embedded inside intake;
- `V72` integration or commit/release authority embedded inside intake;
- `V74` product projection selected by intake;
- `V43` external-world contest branch selected by intake.

## 11. Closeout Expectation

A closed `V69` family should leave the repo with a typed, reproducible, and
non-adoptive candidate-intake substrate ready for `V70` evidence classification and
adversarial review. It should not claim that any admitted candidate is true,
optimal, selected, or implemented.
