# Draft ADEU UX Ergonomic Instantiation Adjudication V67B Implementation Mapping v0

Status: support note for the planned `V67-B` bounded adjudication implementation
pass after the `V67-A` schema-and-validator backbone is expected to ship on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a bounded
`V67-B` slice should compute over the shipped `V67-A` ergonomic artifact language
without reopening the released UX governance substrate, introducing a general
layout solver, allowing arbitrary candidate generation, or laundering heuristic
utility into constitutional law.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v52.md`
- `docs/ARCHITECTURE_ADEU_UX_ERGONOMIC_INSTANTIATION_ADJUDICATION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_UX_ERGONOMIC_INSTANTIATION_ADJUDICATION_V67_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_UX_ERGONOMIC_INSTANTIATION_ADJUDICATION_V67A_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- the shipped `V67-A` schemas, enums, canonicalizers, and validators only:
  - `ux_ergonomic_rule_authority_stack@1`
  - `ux_component_ergonomic_registry@1`
  - `ux_component_visibility_contract@1`
  - `ux_ergonomic_candidate_projection_profile_table@1`
  - `ux_ergonomic_case_envelope@1`
  - `ux_ergonomic_adjudication_request@1`
  - `ux_ergonomic_adjudication_result@1`
- the released UX governance basis consumed by `V67-A`
- the rule that deontic constraints are hard and utility ranks only after hard
  checks pass
- the rule that finite candidate sets are predeclared and repo-native
- the rule that scalar exported scores remain forbidden.

## Re-Author With Repo Alignment

`V67-B` should not add a new ergonomic schema family by default.

Instead, it should implement the bounded adjudication engine that:

- consumes a valid shipped `ux_ergonomic_adjudication_request@1`;
- evaluates only the finite candidate rows in the shipped
  `ux_ergonomic_candidate_projection_profile_table@1`;
- emits a valid computed `ux_ergonomic_adjudication_result@1` with:
  - blocked candidates and reason codes
  - feasible candidates
  - ordinal preference tiers
  - ambiguity markers
  - measurement obligations.

The slice should decide only:

- which candidates are blocked by hard law;
- which candidates are feasible under the admissible case envelope;
- which feasible candidates are:
  - `discouraged`
  - `marginal`
  - `acceptable`
  - `preferred`
- which missing or inadmissible measurements force:
  - blocked posture
  - ambiguity rows
  - measurement-obligation rows.

It should keep:

- no arbitrary candidate generation
- no CSS/layout optimization engine
- no continuous geometry solver over unconstrained spaces
- no hidden policy weights
- no decimal ergonomic scores
- no screenshot-led override of shipped source artifacts.

## Bounded Evaluation Posture

Expected evaluation order:

1. validate request lineage and consumed-basis hashes
2. validate candidate-table binding and visibility-contract completeness
3. derive admissibility from the case envelope
4. apply hard rule authority stack
5. reject blocked candidates with reason codes
6. rank only remaining feasible candidates by bounded ordinal tier
7. emit ambiguity and measurement-obligation rows where required.

Hard-law examples:

- candidate hides required evidence before commit without lawful same-context reveal
- candidate uses lane refs not present in released projection
- candidate lowers targetability below a repo-adopted or external hard floor
- candidate depends on physical-size reasoning from inadmissible measurement chains
- candidate omits required commit-gate visibility or targetability posture.

Inadmissible physical-size or visual-angle chains should block only dependent
computations. They should not automatically block CSS-geometry adjudication when
CSS-px floors are sufficient and the dependent physical / visual reasoning is not
required for pass/fail.

Utility ranking examples:

- same candidate family under two lawful narrow-width shapes
- same candidate family under maximized vs half-screen posture
- touch / coarse-pointer inflation favoring one already feasible candidate over
  another.

Rule composition should remain explicit:

- any triggered `hard_block` blocks the candidate;
- effective hard floor is the max of all applicable hard floors plus any lawful
  upward user preference inflation;
- utility ranking applies only after hard checks pass;
- utility never converts a blocked candidate into a feasible candidate.

## Result-Shape Direction

Computed `ux_ergonomic_adjudication_result@1` should remain bounded to:

- consumed request ref and hash
- source artifact refs and hashes
- `report_status`
- `overall_judgment`
- blocked candidate rows with:
  - `candidate_profile_id`
  - `blocking_reason_codes`
  - `authority_layers_triggered`
- feasible candidate rows with:
  - `candidate_profile_id`
  - `preference_tier`
  - `supporting_reason_codes`
  - `residual_ambiguity_or_none`
- `ambiguity_rows`
- `measurement_obligation_rows`

Recommended `report_status` starter direction:

- `valid`
- `invalid_request_basis_mismatch`
- `invalid_candidate_table_basis_mismatch`
- `invalid_visibility_contract_basis_mismatch`
- `invalid_case_envelope_admissibility`
- `invalid_unknown_candidate_ref`

Recommended `overall_judgment` starter direction:

- `pass`
- `needs_review`
- `fail`

Recommended blocking reason-code starter set:

- `erg_block_basis_hash_mismatch`
- `erg_block_unknown_projection_ref`
- `erg_block_unknown_approved_profile_id`
- `erg_block_unknown_same_context_reveal_term`
- `erg_block_missing_visibility_contract_row`
- `erg_block_missing_required_evidence_visibility`
- `erg_block_required_evidence_not_same_context_reachable`
- `erg_block_trust_boundary_not_visible`
- `erg_block_commit_gate_not_targetable`
- `erg_block_user_preference_lowers_hard_floor`
- `erg_block_platform_preset_claimed_as_hard_without_repo_adoption`
- `erg_block_target_floor_violation`
- `erg_block_text_floor_violation`
- `erg_block_physical_chain_required_but_inadmissible`
- `erg_block_visual_angle_required_but_inadmissible`
- `erg_block_scalar_preference_score_present`

Recommended review / ambiguity starter set:

- `erg_review_declared_geometry_not_runtime_measured`
- `erg_review_unknown_input_mode_with_high_risk_action`
- `erg_review_unknown_task_posture`
- `erg_review_user_acuity_reduced_but_unscaled`
- `erg_review_physical_size_inadmissible_but_not_required`
- `erg_review_visual_angle_inadmissible_but_not_required`
- `erg_review_top_tier_candidate_tie`

Recommended supporting-code starter set:

- `erg_support_preserves_required_evidence_visibility`
- `erg_support_preserves_trust_boundary_visibility`
- `erg_support_commit_gate_gated_and_targetable`
- `erg_support_same_context_reveal_validated`
- `erg_support_css_geometry_admissible`

Tier semantics should stay deterministic:

- `blocked`: a hard block triggered
- `discouraged`: feasible, but review-grade ambiguity or poor task fit remains
- `marginal`: feasible, but only with notable collapse or degradation
- `acceptable`: feasible and adequate for the declared case
- `preferred`: feasible and top-tier under the declared task / input / window posture

Tie semantics:

- multiple top-tier candidates may remain `preferred`
- if a single preferred projection is required and deterministic ladder rules
  cannot distinguish them, `overall_judgment` should become `needs_review` with
  `erg_review_top_tier_candidate_tie`

## Do Not Import

- a generic constraint optimizer over open geometry spaces
- responsive-design sovereignty
- free-form model-authored candidate proposals
- runtime adaptive morph switching
- screenshot witness scoring
- advisory runtime notice families that belong to `V67-C`.

## Likely Implementation Surfaces

- deterministic adjudication helpers should remain explicit rather than buried in
  the schema module only:
  - `packages/adeu_core_ir/src/adeu_core_ir/ux_ergonomics.py`
    - models, enums, canonicalizers, local validators, bundle validators
  - `packages/adeu_core_ir/src/adeu_core_ir/ux_ergonomic_adjudication.py`
    - bounded finite-candidate adjudication helpers for `V67-B`
- extensions to:
  - `packages/adeu_core_ir/tests/test_ux_ergonomics.py`
  - `packages/adeu_core_ir/tests/test_ux_ergonomics_admissibility.py`
- additional engine-focused tests, likely under:
  - `packages/adeu_core_ir/tests/test_ux_ergonomic_adjudication.py`
    or equivalent repo-chosen naming
- computed fixture outputs under:
  - `apps/api/fixtures/ux_ergonomics/vnext_plus186/`
    if the repo keeps the next global fixture/event number convention.

Fixture numbering note:

- `apps/api/fixtures/ux_ergonomics/vnext_plus186/` should follow the global
  next-arc / agent-harness event number, not the highest existing `apps/api`
  fixture directory number.

Recommended helper names:

- `evaluate_ux_ergonomic_adjudication_request(...)`
- `derive_ux_ergonomic_measurement_admissibility(...)`
- `evaluate_ux_ergonomic_candidate_row(...)`
- `derive_ux_ergonomic_overall_judgment(...)`
- `canonicalize_computed_ux_ergonomic_adjudication_result_payload(...)`

## Planned Acceptance Shape

`V67-B` should be read as successful only when:

- adjudication is finite-candidate only
- `report_status` remains artifact-validity-only
- `overall_judgment` remains ergonomic-outcome-only
- blocked candidates carry stable reason-code families
- feasible candidates never bypass hard-law blocking
- preference tiers remain ordinal only
- ambiguity rows remain explicit where admissibility is partial
- measurement-obligation rows remain explicit where planning geometry must later
  become runtime-measured
- source-artifact refs and hashes remain exact and replayable.
