# Assessment vNext+131 Edges

Status: post-closeout edge assessment for `V44-A` (April 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS131_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: `V46` Benchmark Law Bleeds Upstream Into `V44-A`

- Risk:
  the first structural-assessment slice could mint benchmark-family or scoring doctrine
  before the assessment contracts themselves are frozen.
- Response:
  keep `V44-A` limited to probe and trace contracts only, with `V46` remaining a later
  consumer of those contracts rather than their upstream author.
- Closeout Evidence:
  shipped package ownership and exported schemas are limited to
  `adeu_reasoning_template_probe@1` and `adeu_structural_reasoning_trace@1` only,
  with no taxonomy/profile/benchmark fields in the released package surface.

### Edge 2: Hierarchical Fidelity Remains Prose-Only

- Risk:
  the three-way split could remain rhetorical if the released contracts do not type:
  - top-level plan spine
  - active-step descent
  - child ordering
  - return-to-parent evidence
- Response:
  freeze explicit hierarchical probe and trace anchors in the first slice rather than
  deferring them to later scoring code.
- Closeout Evidence:
  the shipped probe/trace models carry explicit
  `plan_spine_step_ids`,
  `active_plan_step_ref`,
  `child_step_refs`,
  `child_order_policy`,
  `return_to_parent_required`,
  and explicit `return_to_parent` trace evidence.

### Edge 3: Blocked And Invalid Closure Collapse

- Risk:
  the implementation could over-compress structural outcomes and erase the distinction
  between lawful insufficiency and invalid completion claims.
- Response:
  freeze both postures in the released vocabularies and require reject fixtures for
  posture mismatch.
- Closeout Evidence:
  released terminal statuses keep `blocked` and `invalid_early_closure` distinct, and
  the committed reject fixture for invalid early-closure posture fails closed during
  model validation.

### Edge 4: Completed Traces Quietly Accept Prefix-Only Plan Spines

- Risk:
  a completed trace could activate only a valid prefix of the top-level plan spine and
  still pass, weakening horizontal continuity law in the first released slice.
- Response:
  completed traces must activate the full top-level plan spine, not just a lawful
  prefix ordering.
- Closeout Evidence:
  review hardening landed in merged follow-up commit `593dc95`, and
  `test_completed_trace_missing_trailing_plan_step_fails_closed` now proves truncated
  completed traces fail closed.

### Edge 5: Taxonomy And Profile Surfaces Arrive Prematurely

- Risk:
  the implementation could ship normalized failure taxonomy or model-profile fields as
  part of the first trace contract, making `V44-B` retroactively authorless.
- Response:
  forbid taxonomy/profile outputs in `V44-A` and reserve them explicitly for later
  follow-on paths.
- Closeout Evidence:
  the shipped package exports only the probe/trace contracts and validators; no
  normalized taxonomy, profile aggregation, or benchmark projection fields were
  released.

### Edge 6: External Benchmark Bundle Becomes Silent Authority

- Risk:
  the imported reasoning-benchmark package could quietly set the contract shapes for
  `V44-A` even though its real code target is mostly `V46`.
- Response:
  use the imported bundle only as support evidence for vocabulary shaping; re-author
  `V44-A` contracts from repo-owned planning/lock docs.
- Closeout Evidence:
  live implementation ownership is entirely under
  `packages/adeu_reasoning_assessment`, while the external bundle remains normalized
  under `examples/external_prototypes/...` and non-precedent.

### Edge 7: Schema Export Portability Drifts

- Risk:
  schema export can appear deterministic on one platform while silently missing path
  portability guards on another, weakening root-mirror replay confidence.
- Response:
  keep schema export replay-tested and fix platform-specific path detection bugs
  without widening contract semantics.
- Closeout Evidence:
  merged review hardening corrected the Windows absolute-path guard in
  `export_schema.py`, and schema export replay tests still pass against both
  authoritative and mirrored schema outputs.

## Current Judgment

- `V44-A` was the right first move because it froze the structural-assessment object
  before any taxonomy, profile, or benchmark lane could claim upstream authority.
- the shipped result remains properly bounded:
  - one repo-owned package
  - one probe schema
  - one trace schema
  - deterministic flat/hierarchical fixtures
  - no taxonomy/profile/benchmark metrics
- the release also made the hierarchical assessment split real contract law rather
  than planning prose only.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md` should now be read with `V44-A` closed on
  `main` and `V44-B` as the branch-local default next path.
