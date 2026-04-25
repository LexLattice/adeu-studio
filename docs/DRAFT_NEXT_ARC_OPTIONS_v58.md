# Draft Next Arc Options v58

Status: planning handoff after `vNext+191` / `V69-A` merged on `main` and after
the lean `V69-A` closeout pass.

Authority layer: planning.

This draft records the post-`V69-A` frontier. It does not authorize
implementation, candidate adoption, evidence classification, adversarial review
settlement, ratification, integration, product projection, commit / merge /
release authority, or dispatch widening by itself.

## Current Frontier

- `V67` is closed on `main`.
- `V68` is closed on `main` as the ARC series cartography family.
- `vNext+191` / `V69-A` shipped the bounded recursive candidate-intake schema,
  model, validator, schema-export, and reference/reject-fixture backbone.
- The shipped `V69-A` surfaces are:
  - `repo_recursive_candidate_intake_record@1`
  - `repo_candidate_source_register@1`
  - `repo_candidate_non_adoption_guardrail@1`
- `V69-A` is closed on `main` as source-bound candidate admission only.
- `V69-B` and `V69-C` remain reviewed support specs until their own starter locks
  select them.

## Next Planning Question

Now that candidate intake rows can be represented in typed, source-bound,
non-adoptive form, should the next slice be `V69-B`: deterministic candidate
derivation and gap scanning over concrete repo sources?

## Recommended Next Pressure

- family: `V69`
- slice candidate: `V69-B`
- proposed slice name:
  - `V69-B: deterministic candidate derivation manifest and candidate-intake gap
    scan`
- recommended planning posture:
  - select `V69-B` as the next default candidate
  - consume the released `V69-A` intake/source/guardrail schemas
  - derive candidate pressure only from concrete observed source refs
  - record derivation accountability separately from the intake record
  - emit gap rows rather than silently repairing malformed or missing candidate
    pressure
  - keep candidate adoption, evidence classification, ratification, product
    selection, release authority, and dispatch out of scope

## Why `V69-B` Now

`V69-A` made candidate intake representable, but it intentionally used a
hand-curated seed fixture. The next robustness gap is reproducibility: the repo
needs to say which concrete sources were scanned, which candidates were emitted or
suppressed, which duplicates were grouped, and which expected candidate pressures
or source bindings are missing.

That work belongs in `V69-B`, not `V70`, because it is still descriptive candidate
intake. It does not decide whether candidates are true, useful, ratified, or ready
to implement.

## Selected Surfaces For Starter Drafting

`V69-B` should add two helper surfaces:

- `repo_candidate_intake_derivation_manifest@1`
- `repo_candidate_intake_gap_scan@1`

These surfaces should remain separate from
`repo_recursive_candidate_intake_record@1` so derivation accountability and gap
severity can be validated without changing candidate-admission semantics.

## Non-Selection

This selector handoff does not select:

- `V69-C` operator-ingress binding or recursive workflow-residue hardening;
- `V70` evidence classification or adversarial review settlement;
- `V71` ratification;
- `V72` contained integration or commit/release posture;
- `V73` outcome review;
- `V74` operator/product projection;
- `V75` dispatch or multi-worker orchestration;
- `V43` external-world contest participation.

Those remain mapped future seams only until their own planning and lock surfaces
select them.

## Inputs For Starter Drafting

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v57.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS191.md`
- `docs/ASSESSMENT_vNEXT_PLUS191_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS191.md`
- `docs/ARCHITECTURE_ADEU_RECURSIVE_CANDIDATE_INTAKE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.json`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RECURSIVE_CANDIDATE_INTAKE_V69_PLANNING_v0.md`
- `artifacts/agent_harness/v191/evidence_inputs/v69a_recursive_candidate_intake_evidence_v191.json`

## Recommended Next Drafting Move

Draft the canonical `vNext+192` starter bundle for `V69-B` only:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS192.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS192.md`
- `docs/ASSESSMENT_vNEXT_PLUS192_EDGES.md`

The `vNext+192` lock should select deterministic derivation-manifest and gap-scan
schema / validator / fixture work only. It should not select `V69-C`, `V70`, or
any downstream adoption workflow.
