# Draft ADEU Recursive Candidate Intake V69B Implementation Mapping v0

Status: support note for the planned `V69-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V69-B`
should add deterministic candidate derivation and gap scanning after `V69-A` has
shipped the candidate-intake schema backbone.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v57.md`
- `docs/ARCHITECTURE_ADEU_RECURSIVE_CANDIDATE_INTAKE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69C_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V69-B` support spec is part of the early `A` / `B` / `C` support-spec bundle
for joint review. It is not an active implementation lock.

When `V69-B` becomes active, it should receive its own canonical starter trio
after `V69-A` is merged and lean-closed. It should not be implemented under the
`V69-A` lock.

## Consumed Inputs

Expected concrete sources:

- released `V69-A` schemas, fixtures, and tests;
- `docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.md`;
- `docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.json`;
- `docs/DRAFT_NEXT_ARC_OPTIONS_v56.md`;
- `docs/DRAFT_NEXT_ARC_OPTIONS_v57.md`;
- `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md`;
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md`;
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RECURSIVE_CANDIDATE_INTAKE_V69_PLANNING_v0.md`;
- committed conceptual-diff, product-wedge, and reasoning-recursion support docs;
- future review artifacts only when committed as concrete source refs.

Globs may appear in the derivation manifest as scanned discovery patterns, but
only observed concrete files may become source rows.

## Candidate New Surfaces

`V69-B` must select two helper surfaces:

- `repo_candidate_intake_derivation_manifest@1`
- `repo_candidate_intake_gap_scan@1`

These should remain separate from the main intake record so derivation
accountability and gap severity can be tested without changing the meaning of a
candidate-admission payload.

## Derivation Manifest

The derivation manifest should record:

- `manifest_id`
- `snapshot_id`
- `source_globs_scanned`
- `observed_source_refs`
- `derivation_rules`
- `candidate_refs_emitted`
- `candidate_refs_suppressed`
- `duplicate_groups`
- `derivation_limitations`

The manifest must distinguish:

- discovered source;
- observed source;
- source admitted into a candidate row;
- source rejected or deferred;
- candidate emitted;
- candidate suppressed as duplicate or out of scope.

## Gap Scan

The gap scan should report:

- `gap_ref`
- `gap_kind`
- `target_candidate_ref`
- `source_refs`
- `severity`
- `recommended_next_surface`
- `limitation_note`

Minimum gap kinds:

- `expected_support_artifact_missing`
- `source_ref_missing`
- `source_presence_mismatch`
- `authority_layer_ambiguous`
- `origin_class_ambiguous`
- `odeu_lane_ambiguous`
- `v68_cartography_source_unmapped`
- `duplicate_without_equivalence`
- `candidate_without_guardrail`
- `candidate_overclaims_authority`
- `required_next_review_missing`
- `stale_candidate_source`
- `derivation_rule_inconclusive`

Minimum severity:

- `info`
- `warning`
- `blocking`

## Derivation Rules

`V69-B` derivation should be deterministic and conservative:

- derive candidates only from concrete observed source refs;
- preserve source authority layer from the source register;
- preserve source presence posture instead of pretending missing support exists;
- mark uncertain ODEU lanes as multi-lane pressure where supported, or gap them as
  ambiguous;
- group obvious duplicates only with explicit equivalence posture;
- emit gap rows instead of silently repairing malformed candidate pressure;
- never mark a candidate as adopted, ratified, implemented, released, or product
  selected.

## Mandatory Reject Cases

`V69-B` should reject:

- glob pattern treated as a source row;
- source referenced as integrated when the concrete file is missing;
- candidate emitted from an unobserved source without a source row carrying source
  absence posture;
- duplicate candidate emitted twice without an equivalence group;
- derivation rule that upgrades support input into lock authority;
- derivation row that embeds `V70` evidence classification;
- gap scan that omits `expected_support_artifact_missing` for a named missing
  review or support artifact;
- gap scan that omits `v68_cartography_source_unmapped` when a candidate source is
  concrete but absent or stale in the consumed `V68` cartography/source-status
  layer;
- candidate overclaim left as success instead of blocking gap;
- stale source ref treated as current without limitation note.

## Expected Fixture Coverage

Recommended fixture names:

- `repo_candidate_intake_derivation_manifest_v192_reference.json`
- `repo_candidate_intake_gap_scan_v192_reference.json`
- `repo_candidate_intake_v192_reject_glob_as_source.json`
- `repo_candidate_intake_v192_reject_missing_integrated_source.json`
- `repo_candidate_intake_v192_reject_duplicate_without_equivalence_group.json`
- `repo_candidate_intake_v192_reject_derivation_upgrades_support_to_lock.json`
- `repo_candidate_intake_v192_reject_embedded_v70_review_classification.json`
- `repo_candidate_intake_v192_reject_missing_expected_support_artifact_gap.json`
- `repo_candidate_intake_v192_reject_v68_cartography_source_unmapped_gap_missing.json`

The future `vNext+192` number is provisional until the active starter lock is
drafted.

## Output Boundary

`V69-B` may make candidate intake reproducible. It may not decide which candidates
are good, true, selected, or ready to implement. Those pressures belong to later
families, especially `V70` and `V71`.
