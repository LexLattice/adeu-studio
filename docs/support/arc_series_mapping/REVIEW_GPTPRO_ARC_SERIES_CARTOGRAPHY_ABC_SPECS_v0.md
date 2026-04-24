# Review GPTPro ARC Series Cartography ABC Specs v0

Status: support-layer external review captured from GPTPro feedback.

Authority layer: support.

This note preserves GPTPro's second review over the `V68` planning and `A/B/C`
support implementation-spec bundle. It is shaping evidence only. It does not
supersede planning docs, lock drafts, implementation mappings, closeout evidence,
released schemas, or maintainer decisions.

## Verdict

Approve the direction, but do not treat the uploaded set as an activatable
`vNext+188` bundle until grounding patches are applied.

The reviewed bundle was strong as a planning plus support implementation-spec bundle
for `V68`, and the `A/B/C` lane decomposition was judged basically right. The
review's main safety point was that support specs are not active-slice authority:
each slice still needs its own canonical starter bundle before implementation.

## Snapshot / Upload Context

The review was performed against a repo zip snapshot still at the prior frontier:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v52.md` present;
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS187.md` present;
- uploaded `v53` and `V68*` implementation mapping docs were not yet in the repo
  snapshot;
- after copying uploaded planning/support docs into a temp repo, `arc-start` lint
  for `ARC=188` failed only because the canonical starter trio was not present.

Current working-tree response:

- this repo working tree now includes the GPTPro support review artifact;
- it includes the `V68` architecture doc;
- it includes the pre-start `vNext+188` starter trio;
- the review's remaining substantive patches are integrated into the `V68` docs.

## Activation Blockers Identified

1. The integrated GPTPro review support doc must exist if docs mark it
   `integrated_shaping_source`.
2. The architecture doc must exist if implementation mappings and locks cite it as
   admitted companion evidence.
3. The canonical starter trio must exist before `V68-A` can be treated as an
   activatable starter bundle:
   - `LOCKED_CONTINUATION_vNEXT_PLUS188.md`
   - `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS188.md`
   - `ASSESSMENT_vNEXT_PLUS188_EDGES.md`

## Requested Patches

- Add a near-top note in `DRAFT_NEXT_ARC_OPTIONS_v53.md` that the `V68-A/B/C`
  implementation specs are support inputs to the future lock, not implementation
  authority by themselves.
- Keep `packages/adeu_repo_description` as implementation home.
- Avoid eight independent object families with duplicated semantics. Use a shared
  row vocabulary and expose the eight schema surfaces as bounded views over that
  vocabulary.
- Resolve the `adeu_arc_*` naming ambiguity. Since this is repo cartography rather
  than ARC-AGI challenge work, prefer `repo_*` schema names.
- Separate `closure_posture` from `branch_posture`.
- Tighten namespace kinds and move source kind / source authority out of namespace
  kind and into row fields.
- Keep the first `V68-A` fixture explicitly partial.
- For `V68-B`, make derivation manifest and gap-scan report selected surfaces, not
  optional.
- For `V68-B`, add `expected_support_artifact_missing` and specify that globs are
  not sources.
- For `V68-C`, make tool-run evidence a selected surface, not optional.
- For `V68-C`, expect default coordinate posture to be
  `coordinate_absent_deliberate` unless `V68-B` has produced enough settled rows for
  useful coordinate emission.

## Recommended `V68-A` Row Split

```text
source row:
  source_ref
  source_kind
  authority_layer
  source_status
  source_presence_posture
  integration_note

namespace row:
  namespace_ref
  namespace_kind
  canonical_label
  source_refs
  equivalence_posture

family row:
  family_ref
  family_id
  family_slice_id
  closure_posture
  selected_by_refs
  closeout_evidence_refs

branch row:
  branch_ref
  branch_family_id
  branch_posture
  selection_condition
  source_refs

evidence surface row:
  evidence_ref
  evidence_kind
  claim_horizon
  source_refs
  limitation_note

tool applicability row:
  tool_id
  target_claim_id
  target_namespace_kind
  applicability_posture
  observed_result_ref
  limitation_note

coordinate plan row:
  coordinate_ref
  coordinate_posture
  target_refs
  non_authority_guardrail
```

## Recommended Fixture Names

```text
repo_arc_series_cartography_v188_reference.json
repo_arc_series_cartography_v188_reject_missing_integrated_review_source.json
repo_arc_series_cartography_v188_reject_family_v67_collapsed_with_global_vnext67.json
repo_arc_series_cartography_v188_reject_v187_collapsed_with_v67c.json
repo_arc_series_cartography_v188_reject_support_doc_as_lock_authority.json
repo_arc_series_cartography_v188_reject_missing_v43_branch_posture.json
repo_arc_series_cartography_v188_reject_global_tool_applicability_overclaim.json
repo_arc_series_cartography_v188_reject_coordinate_authorizes_v69.json
```

