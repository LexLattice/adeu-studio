# Draft ADEU ARC Series Cartography V68B Implementation Mapping v0

Status: support note for the planned `V68-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records the expected
`V68-B` slice shape early so the full `V68-A` / `V68-B` / `V68-C` ladder can receive
joint external review before implementation begins.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v53.md`
- `docs/ARCHITECTURE_ADEU_ARC_SERIES_CARTOGRAPHY_FAMILY_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68A_IMPLEMENTATION_MAPPING_v0.md`

## Slice Thesis

`V68-B` should turn the `V68-A` cartography schema/validator backbone into a
deterministic repo-derived cartography and gap-scan pass.

It should not change the `V68-A` authority posture. The map is still descriptive,
source-status-bearing, and non-authorizing. `V68-B` adds derivation and gap visibility,
not candidate intake, ratification, scheduling, or implementation authority.

## Consumed Basis

`V68-B` should consume the shipped `V68-A` surfaces only:

- `repo_arc_series_cartography@1`
- `repo_arc_namespace_map@1`
- `repo_family_closure_register@1`
- `repo_branch_posture_register@1`
- `repo_support_lineage_register@1`
- `repo_evidence_surface_index@1`
- `repo_arc_mapping_tool_applicability_report@1`
- `repo_recursive_coordinate_emission_plan@1`

It should also consume existing repo evidence sources as derivation inputs, not as
new authority:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v*.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS*.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS*.md`
- `docs/ASSESSMENT_vNEXT_PLUS*_EDGES.md`
- `docs/ARCHITECTURE_*.md`
- `docs/DRAFT_*_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/**`
- `packages/*/schema/*.json`
- `spec/*.json`
- `apps/api/fixtures/**`
- `artifacts/stop_gate/**`
- `artifacts/agent_harness/**`

## Expected Implementation Ownership

Expected package ownership remains:

- `packages/adeu_repo_description`

Expected implementation files:

- `packages/adeu_repo_description/src/adeu_repo_description/arc_series_cartography.py`
- `packages/adeu_repo_description/src/adeu_repo_description/arc_series_cartography_derivation.py`
- `packages/adeu_repo_description/tests/test_arc_series_cartography_v68b.py`

Expected fixture location:

- `apps/api/fixtures/repo_description/vnext_plus189/`

The eventual `vNext+` implementation arc number may shift if `V68-B` is activated
later under a different `vNext+` number. This support note names `vnext_plus189`
only as the expected next lane after `V68-A`; the future lock must set the
authoritative number.

## Selected New `V68-B` Surfaces

`V68-B` should add two helper/report surfaces:

- `repo_arc_cartography_derivation_manifest@1`
- `repo_arc_cartography_gap_scan_report@1`

These should remain support/evidence surfaces for derivation and gap visibility.
They must not replace the cartography objects shipped by `V68-A`.

## Derivation Scope

`V68-B` should derive or partially derive:

- family rows from current selector, architecture, mapping, lock, decision, and
  assessment docs;
- implementation / closeout arc rows from `LOCKED_CONTINUATION_vNEXT_PLUS*` docs;
- closure rows from post-closeout decision and assessment docs;
- support lineage rows from current `docs/support/arc_series_mapping/**`;
- evidence surface rows from closeout artifacts, fixtures, and schema locations;
- namespace rows for known family / slice / implementation-arc / closeout-arc /
  fixture / schema / evidence identities.

It should explicitly allow:

- `derived`;
- `manual_seeded`;
- `review_required`;
- `not_observed`;
- `ambiguous`.

`V68-B` should not force full historical completeness in one pass. A truthful gap
row is better than a silent omission.

Globs are not sources. The derivation manifest may record scanned patterns such as
`docs/LOCKED_CONTINUATION_vNEXT_PLUS*.md`, but only observed concrete files may
become source rows or support evidence.

## Gap Scan Families

Minimum gap families:

- `namespace_kind_ambiguous`
- `family_closure_posture_missing`
- `slice_closure_posture_missing`
- `source_status_missing`
- `support_lineage_missing`
- `evidence_surface_unindexed`
- `branch_posture_missing`
- `tool_applicability_unassessed`
- `coordinate_posture_absent`
- `expected_support_artifact_missing`
- `source_ref_missing`
- `source_ref_stale`
- `authority_layer_mismatch`
- `review_required_ambiguous_derivation`

Each gap row should carry:

- stable `gap_id`
- `gap_family`
- `target_ref`
- `target_namespace_kind`
- `severity`
- `claim_horizon`
- `recommended_next_action`

Severity should be coarse:

- `blocking_for_cartography`
- `needs_review`
- `advisory`

No decimal scores.

## Required Validators

`V68-B` validators should prove:

- derivation manifests identify source globs and exact observed inputs;
- source rows are concrete files or artifacts, not glob patterns;
- derived rows carry derivation posture;
- stale or missing references are explicit gap rows;
- no gap row becomes implementation authority;
- no ambiguous derivation is silently promoted into a settled map row;
- coordinate absence is explicit when recursive-coordinate records are not emitted;
- current `V68` through `V75` future rows remain lifecycle hypotheses, not locks;
- `V43` remains connected conditional unless explicitly selected by a future
  planning doc.

## Mandatory Reject Cases

Reject fixtures should cover:

- a derived map that marks `V69` through `V75` as authorized locks;
- a global `vNext+67` row treated as family `V67`;
- a missing source ref that disappears instead of becoming a gap;
- an expected support artifact missing without an `expected_support_artifact_missing`
  gap;
- a glob pattern promoted into a source row;
- a closure row inferred from support prose without closeout evidence;
- an ambiguous branch posture promoted to settled posture;
- coordinate absence omitted from the derivation result;
- support review text treated as lock evidence.

## Non-Goals

`V68-B` does not own:

- new released candidate-intake semantics;
- adoption of `odeu_conceptual_diff_report@1`;
- quality scoring for model outputs;
- human ratification;
- contained integration or rollback;
- commit, merge, or release authority;
- operator-facing product UI;
- multi-agent or multi-model orchestration.
