# Draft Next Arc Options v55

Status: planning draft after `vNext+189` / `V68-B` merged on `main` and after the
lean `V68-B` closeout pass.

Authority layer: planning.

This draft records the next candidate slice inside the already selected `V68` ARC
series cartography family. It does not authorize implementation, release,
recursive candidate intake, ratification, product workbench construction, commit /
merge / release authority, or dispatch widening by itself.

## Current Frontier

- `V67` is closed on `main`.
- `DRAFT_NEXT_ARC_OPTIONS_v53.md` selected the `V68` family and the first concrete
  `V68-A` slice.
- `vNext+188` / `V68-A` shipped the bounded cartography schema, model, validator,
  schema-export, and reference/reject-fixture backbone in `adeu_repo_description`.
- `vNext+189` / `V68-B` shipped deterministic derivation-manifest and gap-scan
  support over the `V68-A` backbone.
- `V68-B` is now represented by post-closeout evidence in:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS189.md`
  - `docs/ASSESSMENT_vNEXT_PLUS189_EDGES.md`
  - `artifacts/agent_harness/v189/evidence_inputs/v68b_arc_series_cartography_derivation_evidence_v189.json`
- `V68` remains open for the final reviewed slice, `V68-C`, before later families
  such as `V69` through `V75` can consume the map responsibly.

## Next Planning Question

Now that the repo can emit a bounded derivation manifest and gap scan, how should
ADEU harden tool applicability and recursive-coordinate posture without converting
tool success, coordinate rows, or gap recommendations into recursive-adoption,
implementation, release, product, or dispatch authority?

## Recommended Next Slice

- family: `V68`
- next concrete slice: `V68-C`
- recommended selector outcome:
  - select `V68-C` as the next default candidate
  - keep `V68-C` bounded to tool-run evidence, tool-applicability hardening, and
    recursive-coordinate posture over the shipped `V68-A` and `V68-B` surfaces
  - do not use `V68-C` to begin candidate intake, adopt
    `odeu_conceptual_diff_report@1`, score model outputs, ratify future seams,
    build a product workbench, authorize release, or widen dispatch / execution
    authority

## Required Shape For `V68-C`

`V68-C` should consume the shipped `V68-A` and `V68-B` surfaces:

- `repo_arc_series_cartography@1`
- `repo_arc_namespace_map@1`
- `repo_family_closure_register@1`
- `repo_branch_posture_register@1`
- `repo_support_lineage_register@1`
- `repo_evidence_surface_index@1`
- `repo_arc_mapping_tool_applicability_report@1`
- `repo_recursive_coordinate_emission_plan@1`
- `repo_arc_cartography_derivation_manifest@1`
- `repo_arc_cartography_gap_scan_report@1`

It should add only tool-run evidence support:

- `repo_arc_cartography_tool_run_evidence@1`

It should harden and populate the existing tool-applicability and coordinate-plan
surfaces rather than replacing them.

The tool-run evidence surface should record command/tool identity, cwd posture,
target namespace, observed output artifact, exit status, limitation note, and
applicability judgment. A passing tool result is not global truth; it is only
evidence for the claim and namespace it actually checked.

The coordinate posture output should either emit bounded map coordinates or record
deliberate coordinate absence. Silent coordinate omission is not acceptable, but
coordinate rows must not admit candidates, ratify future seams, authorize
integration, authorize release, project product UI, or dispatch work.

## Non-Selection

This selector does not select:

- `V69` candidate intake;
- `V70` quality classification or adversarial review settlement;
- `V71` ratification;
- `V72` contained integration or commit/release posture;
- `V73` outcome review;
- `V74` operator/product projection;
- `V75` dispatch or multi-worker orchestration.

Those remain mapped future seams only until their own planning and lock surfaces
select them.
