# Draft ADEU Recursive Candidate Intake V69 Implementation Mapping v0

Status: support / implementation mapping record for planned `V69`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned `V69`
family into likely package, schema, validator, fixture, and evidence work so the
family can be reviewed before the first active slice lock is drafted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v57.md`
- `docs/ARCHITECTURE_ADEU_RECURSIVE_CANDIDATE_INTAKE_FAMILY_v0.md`
- `docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RECURSIVE_CANDIDATE_INTAKE_V69_PLANNING_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69C_IMPLEMENTATION_MAPPING_v0.md`

## 1. Family Intent

`V69` should add recursive candidate intake without turning intake into:

- evidence classification;
- adversarial review settlement;
- ratification;
- implementation scheduling;
- contained integration;
- release authority;
- product projection;
- dispatch or execution widening.

The implementation target is a typed candidate-intake family that can represent:

- candidate identity;
- concrete source binding;
- source authority layer and source-status posture;
- origin class;
- primary ODEU lane and multi-lane ODEU profile;
- admissible role;
- forbidden role;
- required next review surface;
- eventual family hint;
- duplicate / equivalence posture;
- non-adoption guardrails.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded candidate intake
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus191/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative: `V69` describes repo/corpus candidate
metadata. If a later slice tries to become a live operator-turn compiler or runtime
permission surface, that work should be split away instead of expanding
`adeu_repo_description` by implication.

The proposed `repo_*` schemas are repo-description candidate-intake surfaces, not
ARC challenge artifacts.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/recursive_candidate_intake.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_recursive_candidate_intake_v69a.py`
- `packages/adeu_repo_description/tests/test_recursive_candidate_intake_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_recursive_candidate_intake_record.v1.json`
- `packages/adeu_repo_description/schema/repo_candidate_source_register.v1.json`
- `packages/adeu_repo_description/schema/repo_candidate_non_adoption_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_candidate_intake_derivation_manifest.v1.json`
- `packages/adeu_repo_description/schema/repo_candidate_intake_gap_scan.v1.json`
- `packages/adeu_repo_description/schema/repo_operator_ingress_candidate_binding.v1.json`
- `packages/adeu_repo_description/schema/repo_recursive_workflow_residue_intake_report.v1.json`
- `packages/adeu_repo_description/schema/repo_candidate_intake_pre_v70_handoff.v1.json`

Expected mirror schema files:

- `spec/repo_recursive_candidate_intake_record.schema.json`
- `spec/repo_candidate_source_register.schema.json`
- `spec/repo_candidate_non_adoption_guardrail.schema.json`
- `spec/repo_candidate_intake_derivation_manifest.schema.json`
- `spec/repo_candidate_intake_gap_scan.schema.json`
- `spec/repo_operator_ingress_candidate_binding.schema.json`
- `spec/repo_recursive_workflow_residue_intake_report.schema.json`
- `spec/repo_candidate_intake_pre_v70_handoff.schema.json`

## 3. Candidate `V69` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_recursive_candidate_intake_record@1` | `V69-A` | top-level candidate-intake record with candidate, source, lane, role, and guardrail rows |
| `repo_candidate_source_register@1` | `V69-A` | concrete candidate-source refs with source presence, authority layer, and source-status posture |
| `repo_candidate_non_adoption_guardrail@1` | `V69-A` | forbidden-role and required-next-review guardrail surface |
| `repo_candidate_intake_derivation_manifest@1` | `V69-B` | deterministic observed-input manifest for candidate derivation |
| `repo_candidate_intake_gap_scan@1` | `V69-B` | gap report for missing, stale, duplicate, ambiguous, or overclaiming candidate rows |
| `repo_operator_ingress_candidate_binding@1` | `V69-C` | narrow operator-turn-to-candidate source binding |
| `repo_recursive_workflow_residue_intake_report@1` | `V69-C` | recursive residue captured as candidate pressure without self-validation |
| `repo_candidate_intake_pre_v70_handoff@1` | `V69-C` | explicit handoff to later evidence / adversarial review surfaces |

`V69-A` should ship only the starter shapes and validators. It should not need to
derive all candidates automatically.

## 4. Starter Source Classes

The starter should recognize, but not automatically authorize, candidate sources
from:

- planning docs:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v*.md`
- architecture / decomposition docs:
  - `docs/ARCHITECTURE_*.md`
  - `docs/DRAFT_*_DECOMPOSITION_*.md`
- support docs:
  - `docs/support/**`
- prior mapping and review artifacts:
  - `docs/support/arc_series_mapping/**`
- closeout docs and artifacts:
  - `docs/DRAFT_*_CLOSEOUT_*.md`
  - `artifacts/agent_harness/**`
  - `artifacts/stop_gate/**`
- schemas and fixtures:
  - `packages/*/schema/*.json`
  - `spec/*.json`
  - `apps/api/fixtures/**`
- operator-turn or transcript artifacts, only when represented as concrete source
  rows. If the underlying turn is unavailable or uncommitted, the source row should
  carry an explicit source absence posture.

Globs are discovery instructions, not sources. A derivation manifest may say it
scanned `docs/support/arc_series_mapping/**`, but only observed concrete files may
become source rows.

## 5. Required Starter Enumerations

Candidate source status:

- `integrated_shaping_source`
- `available_but_not_integrated`
- `review_pending_input`
- `rejected_or_superseded_source`

Source presence posture:

- `present`
- `missing_expected_support_artifact`
- `not_uploaded_in_review_snapshot`
- `generated_later`
- `external_unavailable`
- `operator_turn_not_committed`

Candidate origin class:

- `internal_reasoning_residue`
- `external_artifact`
- `operator_turn`
- `model_output`
- `support_doc`
- `review_feedback`
- `repo_observation`
- `planning_pressure`

Candidate intake posture:

- `intake_candidate`
- `intake_duplicate`
- `intake_rejected_out_of_scope`
- `intake_deferred_to_later_family`
- `intake_requires_v70_review`
- `intake_superseded`
- `intake_unknown_needs_review`

ODEU lane:

- `ontological`
- `deontic`
- `epistemic`
- `utility`
- `mixed`

Required next review surface:

- `v70_evidence_classification`
- `v70_adversarial_review`
- `future_family_review`
- `none_yet_deferred`

Eventual family hint:

- `v71_ratification`
- `v72_integration_review`
- `v73_outcome_review`
- `v74_operator_projection_review`
- `v75_dispatch_review`
- `v43_external_contest_branch`
- `none`

Forbidden role:

- `lock_authority`
- `released_schema`
- `ratified_decision`
- `implementation_task`
- `commit_release_authority`
- `product_authorization`
- `dispatch_authority`
- `self_validation`
- `transcript_truth`

## 6. Shared Row Vocabulary

`V69-A` should define one shared internal row vocabulary and expose starter schema
surfaces as bounded views over that vocabulary.

Minimum source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `integration_note`

Minimum candidate row fields:

- `candidate_ref`
- `candidate_label`
- `origin_class`
- `intake_posture`
- `primary_odeu_lane`
- `odeu_lanes`
- `source_refs` (non-empty)
- `equivalence_posture`
- `intake_note`

Minimum role row fields:

- `candidate_ref`
- `admissible_roles`
- `forbidden_roles`
- `required_next_review_surface`
- `eventual_family_hint`
- `non_adoption_guardrail`

Minimum gap row fields:

- `gap_ref`
- `gap_kind`
- `target_candidate_ref`
- `source_refs`
- `severity`
- `limitation_note`

Minimum handoff row fields:

- `handoff_ref`
- `candidate_ref`
- `handoff_target`
- `handoff_reason`
- `non_authority_guardrail`

## 7. Slice Boundaries

`V69-A` owns shape, validation, constants, schemas, export, and reference / reject
fixtures.

`V69-B` owns deterministic candidate derivation and gap scanning from concrete repo
sources.

`V69-C` owns operator-ingress binding, recursive workflow residue intake, and
pre-`V70` handoff hardening.

No `V69` slice owns adoption, ratification, release authority, product
authorization, or execution widening.

## 8. Integrated Review Decisions

- Keep the starter schema names as `repo_*` names and document them as
  repo-description candidate-intake surfaces.
- Allow `operator_turn_not_committed` in `V69-A` only as a source presence posture,
  not as operator-ingress behavior.
- Keep `required_next_review_surface` to `V70`, `future_family_review`, or
  deferral values. Put `V71` through `V75` and `V43` into `eventual_family_hint`.
- Support `primary_odeu_lane` plus sorted unique `odeu_lanes`. Reject
  `primary_odeu_lane=mixed` when `odeu_lanes` is absent.
- Represent source absence through source rows. Candidate `source_refs` must be
  non-empty and must point to source rows.
- Apply risk-aware forbidden-role checks based on `origin_class` and
  `admissible_roles`.
