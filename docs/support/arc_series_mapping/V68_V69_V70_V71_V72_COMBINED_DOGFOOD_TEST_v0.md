# V68 / V69 / V70 / V71 / V72 Combined Dogfood Test v0

Status: support evidence captured after `V72` family closeout.

Authority layer: support.

This note records a local dogfood probe over the closed `V68` cartography
family, closed `V69` recursive candidate-intake family, closed `V70` candidate
review-classification family, closed `V71` candidate ratification-review
family, and closed `V72` contained integration-review family. It is not lock
authority and does not authorize `V73`.

## Test Surface

The probe exercised three layers:

- focused repo-description tests for all `V68`, `V69`, `V70`, `V71`, and `V72`
  family surfaces;
- terminal family closeout checks for `vNext+190`, `vNext+193`,
  `vNext+196`, `vNext+199`, and `vNext+202`;
- a direct cross-family continuity probe over the shipped reference fixtures and
  family closeout alignment artifacts.

## Commands Run

- `.venv/bin/python -m pytest packages/adeu_repo_description/tests/test_arc_series_cartography_v68a.py packages/adeu_repo_description/tests/test_arc_series_cartography_v68b.py packages/adeu_repo_description/tests/test_arc_series_cartography_v68c.py packages/adeu_repo_description/tests/test_recursive_candidate_intake_v69a.py packages/adeu_repo_description/tests/test_recursive_candidate_intake_v69b.py packages/adeu_repo_description/tests/test_recursive_candidate_intake_v69c.py packages/adeu_repo_description/tests/test_candidate_review_classification_v70a.py packages/adeu_repo_description/tests/test_candidate_review_classification_v70b.py packages/adeu_repo_description/tests/test_candidate_review_classification_v70c.py packages/adeu_repo_description/tests/test_candidate_ratification_review_v71a.py packages/adeu_repo_description/tests/test_candidate_ratification_review_v71b.py packages/adeu_repo_description/tests/test_candidate_ratification_review_v71c.py packages/adeu_repo_description/tests/test_contained_integration_review_v72a.py packages/adeu_repo_description/tests/test_contained_integration_review_v72b.py packages/adeu_repo_description/tests/test_contained_integration_review_v72c.py packages/adeu_repo_description/tests/test_repo_description_export_schema.py`
- `make arc-closeout-check ARC=190`
- `make arc-closeout-check ARC=193`
- `make arc-closeout-check ARC=196`
- `make arc-closeout-check ARC=199`
- `make arc-closeout-check ARC=202`
- local JSON continuity probe over:
  - `artifacts/agent_harness/v190/evidence_inputs/v68_family_closeout_alignment_v190.json`
  - `artifacts/agent_harness/v193/evidence_inputs/v69_family_closeout_alignment_v193.json`
  - `artifacts/agent_harness/v196/evidence_inputs/v70_family_closeout_alignment_v196.json`
  - `artifacts/agent_harness/v199/evidence_inputs/v71_family_closeout_alignment_v199.json`
  - `artifacts/agent_harness/v202/evidence_inputs/v72_family_closeout_alignment_v202.json`
  - `apps/api/fixtures/repo_description/vnext_plus193/repo_candidate_intake_pre_v70_handoff_v193_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus194/repo_candidate_evidence_classification_v194_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus195/repo_candidate_adversarial_review_matrix_v195_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus195/repo_candidate_review_conflict_register_v195_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus195/repo_candidate_review_gap_scan_v195_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_review_classification_summary_v196_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_pre_ratification_handoff_v196_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus197/repo_candidate_ratification_request_v197_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus198/repo_candidate_ratification_record_v198_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus199/repo_post_ratification_handoff_v199_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus200/repo_contained_integration_candidate_plan_v200_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus201/repo_contained_integration_trial_record_v201_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_effect_surface_register_v201_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_rollback_readiness_v201_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus202/repo_commit_release_authority_posture_v202_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus202/repo_post_integration_outcome_review_handoff_v202_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus202/repo_contained_integration_family_closeout_alignment_v202_reference.json`

## Result

The combined probe passed.

Observed results:

- focused repo-description test set: `262 passed`, `75 warnings`;
- terminal family closeout checks passed for `vNext+190`, `vNext+193`,
  `vNext+196`, `vNext+199`, and `vNext+202`;
- candidate set preserved from `V69-C` pre-`V70` handoff through `V72-B`
  contained trial records: `3`;
- V70-B review rows: `3`;
- V70-B relation rows: `3`;
- V70-B gap rows: `4`;
- V71-A request rows: `3`;
- V71-B ratification rows: `3`;
- V71-C handoff rows: `3`;
- V72-A plan rows: `3`;
- V72-B trial rows: `3`;
- V72-C authority posture rows: `1`;
- V72-C post-integration handoff rows: `1`.

The probe confirmed:

- family closeout artifacts exist for `V68`, `V69`, `V70`, `V71`, and `V72`;
- deferred future-family boundaries remain preserved;
- candidate identity is preserved from `V69-C` through `V72-B`;
- `V72-C` narrows to the single eligible self-evidencing workflow-type
  emergence candidate;
- the conceptual-diff candidate remains blocked by conflict / dissent and is
  trial-blocked in `V72`;
- the typed-adjudication product wedge remains future-family-only and
  trial-blocked in `V72`;
- V70-B references only known V70-A claims and classifications;
- V70-C preserves V70-B review, relation, and gap refs;
- V72-B trial, effect, and rollback rows feed V72-C authority and handoff rows;
- V72-C authority posture does not claim released truth, merge authority, PR
  update authority, or release authority;
- V72-C handoff requests `V73` outcome review without performing outcome
  judgment;
- V72 family closeout preserves future-family boundaries for `V73` and `V74`.

## Empirical Findings

The first local continuity attempts failed on harness assumptions, not on the
family substance:

- the probe initially used stale V70-A / V70-B row-key names instead of the
  shipped `claim_classification_rows` and `adversarial_review_rows` keys;
- the probe initially expected forbidden-action names without the shipped
  `automatic_*` prefix used by `V72-C`.

The adjusted probe uses the released fixture schemas and passes.

One carry-forward drift note remains from the earlier dogfood pass: `V68` and
`V69` family alignment artifacts use older closeout vocabulary without explicit
`future_family_authority`, while `V70`, `V71`, and `V72` include that explicit
field. This remains useful support evidence for a later normalization pass, but
it is not a failure of the `V68` through `V72` family chain.

## Interpretation

The result is good enough to use as support input for `V73` planning.

It shows that the five families compose in the intended direction:

```text
V68 map substrate
  -> V69 source-bound candidate pressure
  -> V70 evidence / adversarial / gap classification
  -> V70 pre-ratification handoff
  -> V71 request / settlement / ratification-review / handoff
  -> V72 containment plan / trial / effect / rollback / authority posture
  -> V73 outcome-review pressure
```

It does not prove that any candidate is outcome-successful, release-ready,
product-selected, runtime-permitted, or dispatchable. Those remain later
authority questions.
