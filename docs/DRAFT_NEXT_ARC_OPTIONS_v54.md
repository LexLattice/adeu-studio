# Draft Next Arc Options v54

Status: planning draft after `vNext+188` / `V68-A` merged on `main` and after the
lean `V68-A` closeout pass.

Authority layer: planning.

This draft records the next candidate slice inside the already selected `V68` ARC
series cartography family. It does not authorize implementation, release, recursive
candidate intake, ratification, product workbench construction, commit / merge /
release authority, or dispatch widening by itself.

## Current Frontier

- `V67` is closed on `main`.
- `DRAFT_NEXT_ARC_OPTIONS_v53.md` selected the `V68` family and the first concrete
  `V68-A` slice.
- `vNext+188` / `V68-A` shipped the bounded cartography schema, model, validator,
  schema-export, and reference/reject-fixture backbone in `adeu_repo_description`.
- `V68-A` is now represented by post-closeout evidence in:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS188.md`
  - `docs/ASSESSMENT_vNEXT_PLUS188_EDGES.md`
  - `artifacts/agent_harness/v188/evidence_inputs/v68a_arc_series_cartography_evidence_v188.json`
- `V68` remains open. The reviewed lane ladder still expects `V68-B` and `V68-C`
  before later families such as `V69` through `V75` can consume the map responsibly.

## Next Planning Question

Now that the cartography row vocabulary exists, how should ADEU derive a current
repo cartography and visible gap scan from concrete repo artifacts without
converting derivation into scheduling, ratification, implementation, release, or
recursive-adoption authority?

## Recommended Next Slice

- family: `V68`
- next concrete slice: `V68-B`
- recommended selector outcome:
  - select `V68-B` as the next default candidate
  - keep `V68-B` bounded to deterministic repo-derived cartography and gap-scan
    support over the shipped `V68-A` backbone
  - do not use `V68-B` to begin candidate intake, adopt
    `odeu_conceptual_diff_report@1`, score model outputs, ratify future seams,
    build a product workbench, or widen dispatch / execution authority

## Required Shape For `V68-B`

`V68-B` should consume the shipped `V68-A` surfaces:

- `repo_arc_series_cartography@1`
- `repo_arc_namespace_map@1`
- `repo_family_closure_register@1`
- `repo_branch_posture_register@1`
- `repo_support_lineage_register@1`
- `repo_evidence_surface_index@1`
- `repo_arc_mapping_tool_applicability_report@1`
- `repo_recursive_coordinate_emission_plan@1`

It should add only derivation and gap-visibility support surfaces:

- `repo_arc_cartography_derivation_manifest@1`
- `repo_arc_cartography_gap_scan_report@1`

The derivation manifest should record scanned source patterns, exact observed input
files, source statuses, derivation posture, and limitations. Globs may be recorded
as scanned patterns, but only concrete observed files may become source rows.

The gap scan should record missing, stale, ambiguous, or under-indexed cartography
claims as explicit gap rows rather than silently filling them with prose inference.

## Non-Selection

This selector does not select:

- `V68-C` tool-run evidence or recursive-coordinate hardening;
- `V69` candidate intake;
- `V70` quality classification or adversarial review settlement;
- `V71` ratification;
- `V72` contained integration or commit/release posture;
- `V73` outcome review;
- `V74` operator/product projection;
- `V75` dispatch or multi-worker orchestration.

Those remain mapped future seams only until their own planning and lock surfaces
select them.
