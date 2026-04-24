# Draft ADEU ARC Series Cartography V68 Implementation Mapping v0

Status: support / implementation mapping record for planned `V68`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned `V68`
family into likely package, schema, validator, fixture, and evidence work so the
family is concrete before implementation begins.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v53.md`
- `docs/ARCHITECTURE_ADEU_ARC_SERIES_CARTOGRAPHY_FAMILY_v0.md`
- `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68C_IMPLEMENTATION_MAPPING_v0.md`

## 1. Family Intent

`V68` should add whole-series ARC cartography without turning cartography into:

- future-family selection;
- recursive candidate admission;
- quality classification;
- ratification;
- implementation scheduling;
- product projection;
- release authority.

The implementation target is a typed map family that can represent:

- namespace disambiguation;
- source-status posture;
- family and slice closure;
- branch posture;
- support lineage;
- evidence surface indexing;
- tool-applicability limits;
- recursive-coordinate emission planning.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for the
    cartography family
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus188/`
  - reference fixtures and reject fixtures for the first bounded slice

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/arc_series_cartography.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_arc_series_cartography_v68a.py`
- `packages/adeu_repo_description/tests/test_arc_series_cartography_export_schema.py`

Expected authoritative schema files:

- `packages/adeu_repo_description/schema/repo_arc_series_cartography.v1.json`
- `packages/adeu_repo_description/schema/repo_arc_namespace_map.v1.json`
- `packages/adeu_repo_description/schema/repo_family_closure_register.v1.json`
- `packages/adeu_repo_description/schema/repo_branch_posture_register.v1.json`
- `packages/adeu_repo_description/schema/repo_support_lineage_register.v1.json`
- `packages/adeu_repo_description/schema/repo_evidence_surface_index.v1.json`
- `packages/adeu_repo_description/schema/repo_arc_mapping_tool_applicability_report.v1.json`
- `packages/adeu_repo_description/schema/repo_recursive_coordinate_emission_plan.v1.json`

Expected mirror schema files:

- `spec/repo_arc_series_cartography.schema.json`
- `spec/repo_arc_namespace_map.schema.json`
- `spec/repo_family_closure_register.schema.json`
- `spec/repo_branch_posture_register.schema.json`
- `spec/repo_support_lineage_register.schema.json`
- `spec/repo_evidence_surface_index.schema.json`
- `spec/repo_arc_mapping_tool_applicability_report.schema.json`
- `spec/repo_recursive_coordinate_emission_plan.schema.json`

## 3. Candidate `V68` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_arc_series_cartography@1` | `V68-A` | top-level unitary map over source set, namespace rows, family rows, evidence joins, and future seams |
| `repo_arc_namespace_map@1` | `V68-A` | disambiguates family, slice, implementation arc, closeout arc, branch target, fixture, schema, and evidence identities |
| `repo_family_closure_register@1` | `V68-A` | represents closure and selection posture for family/slice rows |
| `repo_branch_posture_register@1` | `V68-A` | represents connected, deferred, conditional, superseded, and not-selected branch posture |
| `repo_support_lineage_register@1` | `V68-A` | records support docs, review inputs, and shaping sources with source-status posture |
| `repo_evidence_surface_index@1` | `V68-A` | records closeout, fixture, test, support, and tool evidence surfaces with claim horizons |
| `repo_arc_mapping_tool_applicability_report@1` | `V68-A` | records which tools apply to which cartography claims and where they are namespace-limited |
| `repo_recursive_coordinate_emission_plan@1` | `V68-A` | plans how later families can consume coordinates without treating map rows as authority |

`V68-A` should ship these as starter shapes and validators. It should not need to
derive the final complete map automatically in the first slice.

## 4. Starter Source Classes

The starter should recognize, but not automatically authorize, these source classes:

- planning docs:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v*.md`
- lock docs:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS*.md`
- decision docs:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS*.md`
- assessment docs:
  - `docs/ASSESSMENT_vNEXT_PLUS*_EDGES.md`
- architecture / decomposition docs:
  - `docs/ARCHITECTURE_*.md`
  - `docs/DRAFT_*_DECOMPOSITION_*.md`
- support docs:
  - `docs/support/**`
- support lineage for the current map:
  - `docs/support/arc_series_mapping/**`
- schema locations:
  - `packages/*/schema/*.json`
  - `spec/*.json`
- fixture locations:
  - `apps/api/fixtures/**`
- closeout artifacts:
  - `artifacts/stop_gate/**`
  - `artifacts/agent_harness/**`
- generated views:
  - `docs/generated/**`

Every source row should carry source kind, authority layer, source-status posture,
and source-presence posture.

Globs are discovery instructions, not sources. A derivation or reference fixture may
record that it scanned `docs/LOCKED_CONTINUATION_vNEXT_PLUS*.md`, but only observed
concrete files may become source rows.

## 5. Required Starter Enumerations

Source status:

- `integrated_shaping_source`
- `available_but_not_integrated`
- `review_pending_input`
- `rejected_or_superseded_source`

Namespace kind:

- `selector_version`
- `family_id`
- `family_slice_id`
- `implementation_arc_id`
- `closeout_arc_id`
- `evidence_arc_id`
- `branch_local_execution_target`
- `planning_doc_ref`
- `lock_doc_ref`
- `decision_doc_ref`
- `assessment_doc_ref`
- `architecture_doc_ref`
- `support_doc_ref`
- `schema_id`
- `fixture_dir_ref`
- `evidence_input_ref`
- `stop_gate_ref`

Source kind and authority layer are fields on source rows, not namespace kinds.

Closure posture:

- `closed_on_main`
- `open_in_progress`
- `planned_not_started`
- `deferred_to_later_family`
- `superseded_by_alternate_surface`
- `not_selected_yet`
- `unknown_needs_review`

Branch posture:

- `connected_conditional_branch`
- `deferred_branch`
- `selected_branch`
- `superseded_branch`
- `not_selected_branch`
- `review_required_branch`

Tool applicability:

- `applicable_and_supporting`
- `applicable_with_warnings`
- `namespace_limited`
- `not_applicable_to_claim`
- `failed_or_inconclusive`
- `not_run`

Claim horizon:

- `descriptive_support`
- `planning_candidate`
- `architecture_decomposition`
- `lock_authorized`
- `closeout_evidence`
- `released_schema_or_runtime`
- `future_deferred`
- `review_pending`

Source presence posture:

- `present`
- `missing_expected_support_artifact`
- `not_uploaded_in_review_snapshot`
- `generated_later`
- `external_unavailable`

## 5.1 Shared Row Vocabulary

`V68-A` should define one shared row vocabulary and expose the eight schema surfaces
as bounded views over that vocabulary. It should not implement eight disconnected
object families with duplicated semantics.

Minimum source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `integration_note`

Minimum namespace row fields:

- `namespace_ref`
- `namespace_kind`
- `canonical_label`
- `source_refs`
- `equivalence_posture`

Minimum family row fields:

- `family_ref`
- `family_id`
- `family_slice_id`
- `closure_posture`
- `selected_by_refs`
- `closeout_evidence_refs`

Minimum branch row fields:

- `branch_ref`
- `branch_family_id`
- `branch_posture`
- `selection_condition`
- `source_refs`

Minimum evidence surface row fields:

- `evidence_ref`
- `evidence_kind`
- `claim_horizon`
- `source_refs`
- `limitation_note`

Minimum tool applicability row fields:

- `tool_id`
- `target_claim_id`
- `target_namespace_kind`
- `applicability_posture`
- `observed_result_ref`
- `limitation_note`

Minimum coordinate plan row fields:

- `coordinate_ref`
- `coordinate_posture`
- `target_refs`
- `non_authority_guardrail`

## 6. Required Starter Validators

Starter validation should require:

- one explicit map identity and snapshot identity;
- sorted unique source rows by `source_ref`;
- no absolute source paths;
- no source row without source kind, authority layer, source status, and source
  presence posture;
- no integrated source row whose `source_presence_posture` is not `present`;
- no namespace row without namespace kind;
- no namespace row that equates different namespace kinds by string resemblance only;
- no family row without closure posture;
- no connected branch without branch posture;
- no support lineage row without source-status posture;
- no evidence surface row without claim horizon;
- no tool-applicability row without target claim and applicability posture;
- no recursive-coordinate row that claims candidate admission, ratification, or
  implementation authority.

Reject fixtures should cover:

- review feedback mentioned but not present as an artifact and still marked
  integrated;
- global `vNext+` arc number treated as the same identity as a family `V` number;
- closed-family posture without a decision or closeout evidence reference;
- connected conditional branch omitted from the branch register;
- tool result marked globally applicable when the claim is namespace-limited;
- support-layer source marked as lock authority;
- repo cartography schema names misclassified as ARC-AGI challenge artifacts.

## 7. `V68-A` Starter Mapping

`V68-A` should stay bounded to:

- schema definitions;
- model validators;
- canonicalization helpers;
- schema export;
- reference and reject fixtures;
- one hand-curated post-`V67` reference map seed;
- tests that prove the negative laws above.

It should not require:

- full automatic extraction across all 300k lines of Python;
- complete historical row coverage for every early arc;
- product UI work;
- multi-agent orchestration;
- recursive candidate intake.

The starter reference can be intentionally partial if it declares its coverage
horizon. A truthful partial cartography seed is better than a complete-looking map
that hides unknowns.

## 8. Later Slice Direction

`V68-B` should add deterministic derivation and gap scanning.

`V68-C` should add tool-applicability reporting and recursive-coordinate emission
planning.

The `A`, `B`, and `C` support implementation specs are intentionally drafted before
implementation so they can receive one joint external review. They are not lock
authority. Each slice must still receive its own canonical starter bundle
(`LOCKED_CONTINUATION`, pre-start stop-gate decision, and edge assessment) when that
slice becomes active.

If the first implementation pass discovers that the eight surfaces are too large for
one bounded starter, the least risky split is:

- keep `repo_arc_series_cartography@1`, `repo_arc_namespace_map@1`, and
  `repo_family_closure_register@1` in `V68-A`;
- keep `repo_support_lineage_register@1` and `repo_evidence_surface_index@1` in
  `V68-A` if review shows source/evidence posture is the highest-risk seam;
- defer `repo_branch_posture_register@1`,
  `repo_arc_mapping_tool_applicability_report@1`, and
  `repo_recursive_coordinate_emission_plan@1` to `V68-B` / `V68-C`;
- record that split explicitly in the next lock or closeout note.
