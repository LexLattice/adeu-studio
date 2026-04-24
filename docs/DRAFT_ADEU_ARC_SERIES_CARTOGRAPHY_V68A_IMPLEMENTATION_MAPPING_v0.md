# Draft ADEU ARC Series Cartography V68A Implementation Mapping v0

Status: support note for the planned `V68-A` starter implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the starter
`V68-A` slice should create a bounded cartography schema-and-validator backbone
without turning map output into authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v53.md`
- `docs/ARCHITECTURE_ADEU_ARC_SERIES_CARTOGRAPHY_FAMILY_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68C_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md` as support-layer shaping map
- support lineage under `docs/support/arc_series_mapping/`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_MAPPING_V68_PLANNING_v0.md`
  as integrated support-layer GPTPro review
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_CARTOGRAPHY_ABC_SPECS_v0.md`
  as integrated support-layer GPTPro review over the early slice-spec bundle
- `repo_arc_dependency_register@2` as nearby repo-description precedent
- current arc-bundle lint posture:
  - `make arc-start-check ARC=188`
  - `make arc-closeout-check ARC=188`
- current authority-layer doctrine:
  - `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
  - `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
  - `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`

## Workflow Posture

This `V68-A` support spec is part of the early `A` / `B` / `C` support-spec bundle
for joint GPTPro review. It is not the same thing as the active-slice canonical
starter bundle.

When `V68-A` is implemented, the active-slice starter bundle is:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS188.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS188.md`
- `docs/ASSESSMENT_vNEXT_PLUS188_EDGES.md`

The same pattern should repeat for `V68-B` and `V68-C` with their own future
`vNext+` numbers when those slices become active.

## Re-Author With Repo Alignment

Candidate new `V68-A` surfaces:

- `repo_arc_series_cartography@1`
- `repo_arc_namespace_map@1`
- `repo_family_closure_register@1`
- `repo_branch_posture_register@1`
- `repo_support_lineage_register@1`
- `repo_evidence_surface_index@1`
- `repo_arc_mapping_tool_applicability_report@1`
- `repo_recursive_coordinate_emission_plan@1`

Those starter surfaces should remain bounded to:

- one explicit source-set posture;
- one namespace map;
- one family/slice closure register;
- one branch posture register;
- one support lineage register;
- one evidence surface index;
- one tool-applicability report shape;
- one recursive-coordinate emission plan shape;
- one post-`V67` reference fixture family.

They should decide only:

- how current ARC-family cartography rows are represented;
- how source status is represented;
- how namespace identity is kept explicit;
- how closure and branch posture are represented;
- how support and review lineage are represented;
- how evidence surface claim horizons are represented;
- how tool-applicability claims are represented;
- how later recursive coordinates can be emitted without authorizing later actions.

They should keep:

- no scheduling authority;
- no recursive candidate intake;
- no conceptual-diff schema adoption;
- no quality or utility scoring;
- no ratification;
- no contained integration;
- no outcome review;
- no product workbench;
- no dispatch or execution widening.

## Starter Source Binding

`V68-A` reference fixtures should carry at least:

- `cartography_id`
- `snapshot_id`
- `source_set_id`
- `coverage_horizon`
- `source_rows`
- `namespace_rows`
- `family_rows`
- `branch_rows`
- `support_lineage_rows`
- `evidence_surface_rows`
- `tool_applicability_rows`
- `coordinate_plan_rows`

Source rows should include:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `integration_note`

The first reference fixture should mark the captured GPTPro review support docs as
`integrated_shaping_source`. Future review feedback without a committed source
artifact should be marked `review_pending_input`, not `integrated_shaping_source`.

## Starter Validation Split

Local model validators should validate one payload only:

- schema shape;
- frozen enums;
- sorted unique row identities;
- no absolute repo paths;
- no free-text authority layers;
- no missing source-status posture.

Bundle validators should validate cross-artifact relationships:

- top-level cartography rows reference namespace, family, branch, evidence, and tool
  rows that exist in the same bundle;
- family rows have matching namespace rows;
- branch rows have matching family or future-seam rows;
- evidence rows reference a known source row;
- tool rows reference a known evidence or claim row;
- recursive-coordinate rows stay non-authorizing.

Shared row vocabulary should include:

- source rows:
  - `source_ref`
  - `source_kind`
  - `authority_layer`
  - `source_status`
  - `source_presence_posture`
  - `integration_note`
- namespace rows:
  - `namespace_ref`
  - `namespace_kind`
  - `canonical_label`
  - `source_refs`
  - `equivalence_posture`
- family rows:
  - `family_ref`
  - `family_id`
  - `family_slice_id`
  - `closure_posture`
  - `selected_by_refs`
  - `closeout_evidence_refs`
- branch rows:
  - `branch_ref`
  - `branch_family_id`
  - `branch_posture`
  - `selection_condition`
  - `source_refs`
- evidence surface rows:
  - `evidence_ref`
  - `evidence_kind`
  - `claim_horizon`
  - `source_refs`
  - `limitation_note`
- tool applicability rows:
  - `tool_id`
  - `target_claim_id`
  - `target_namespace_kind`
  - `applicability_posture`
  - `observed_result_ref`
  - `limitation_note`
- coordinate plan rows:
  - `coordinate_ref`
  - `coordinate_posture`
  - `target_refs`
  - `non_authority_guardrail`

## Starter Constants

Expected constants:

- `REPO_ARC_SERIES_CARTOGRAPHY_SCHEMA = "repo_arc_series_cartography@1"`
- `REPO_ARC_NAMESPACE_MAP_SCHEMA = "repo_arc_namespace_map@1"`
- `REPO_FAMILY_CLOSURE_REGISTER_SCHEMA = "repo_family_closure_register@1"`
- `REPO_BRANCH_POSTURE_REGISTER_SCHEMA = "repo_branch_posture_register@1"`
- `REPO_SUPPORT_LINEAGE_REGISTER_SCHEMA = "repo_support_lineage_register@1"`
- `REPO_EVIDENCE_SURFACE_INDEX_SCHEMA = "repo_evidence_surface_index@1"`
- `REPO_ARC_MAPPING_TOOL_APPLICABILITY_REPORT_SCHEMA = "repo_arc_mapping_tool_applicability_report@1"`
- `REPO_RECURSIVE_COORDINATE_EMISSION_PLAN_SCHEMA = "repo_recursive_coordinate_emission_plan@1"`

The repo-native field name should be `schema`, not `schema_id`.

## Mandatory Reject Cases

`V68-A` should reject:

- review text marked integrated when no `source_ref` artifact exists;
- integrated source row whose `source_presence_posture` is not `present`;
- `V67` family identity collapsed with `vNext+67` implementation / closeout arc
  identity;
- `vNext+187` closeout identity collapsed with `V67-C` slice identity;
- support-layer mapping doc marked as lock authority;
- branch row for `V43` omitted while future-seam rows reference external contest
  participation;
- tool applicability marked global when the tool applies only to one namespace;
- repo cartography schema names misclassified as ARC-AGI challenge artifacts;
- recursive coordinate plan row that admits, ratifies, implements, or releases a
  later family.

## First Reference Fixture Intent

The first reference fixture should be a post-`V67` seed, not a final exhaustive map.

Required coverage:

- `V67` closed on `main`;
- `V68` planned / not started;
- `V68-A` selected as starter;
- `V69` through `V75` tracked as future deferred families;
- `V43` tracked as connected conditional branch;
- support lineage under `docs/support/arc_series_mapping/` tracked as integrated
  shaping sources where present;
- GPTPro review support docs tracked as `integrated_shaping_source`;
- future follow-on feedback tracked as `review_pending_input` if no artifact is
  available at implementation time.

Recommended first fixture names:

- `repo_arc_series_cartography_v188_reference.json`
- `repo_arc_series_cartography_v188_reject_missing_integrated_review_source.json`
- `repo_arc_series_cartography_v188_reject_family_v67_collapsed_with_global_vnext67.json`
- `repo_arc_series_cartography_v188_reject_v187_collapsed_with_v67c.json`
- `repo_arc_series_cartography_v188_reject_support_doc_as_lock_authority.json`
- `repo_arc_series_cartography_v188_reject_missing_v43_branch_posture.json`
- `repo_arc_series_cartography_v188_reject_global_tool_applicability_overclaim.json`
- `repo_arc_series_cartography_v188_reject_coordinate_authorizes_v69.json`

Unknowns should be explicit. The starter should not fake historical completeness.
