# Assessment vNext+280 Edges

Status: post-closeout assessment for `BRL-0-C`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS280_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Closed Edge Review

### Edge 1: Impact Cone Selection Becomes Probe Generation

Status: contained.

`BRL-0-C` selects only existing manifest-declared probes from declared
owner-surface rows. It does not mint probe contracts, argv, fixtures,
canonicalization profiles, or expected observation hashes.

### Edge 2: Partial Replay Becomes Full No-Regression Claim

Status: contained.

Certificate posture and bounded claims are narrower than or equal to selected
probe and owner-surface evidence. Partial impact-cone selection yields
`impact_cone_no_observed_regression`, not full-manifest preservation.

### Edge 3: Suite-Root Match Becomes Product Truth

Status: contained.

Certificates carry `bounded_replay_preservation_only_not_product_truth`.
Suite-root match can support bounded preservation evidence, but cannot grant
product truth, HOB closure, OTB transition legality, or official readiness.

### Edge 4: Missing Sentinel Coverage Is Silently Ignored

Status: contained.

Missing sentinel coverage produces blockers. Review feedback hardened the mixed
covered/uncovered case so a touched uncovered surface blocks the report even
when another touched surface has valid selected probes.

### Edge 5: Missing Scope Crashes Certificate Construction

Status: contained.

`blocked_by_missing_scope` now becomes an explicit certificate known gap rather
than an invalid blocked certificate with no gaps.

### Edge 6: Staleness Report Becomes Automatic Refresh

Status: contained.

Stale-lock reports identify required refresh rows only. They do not refresh
manifests, expected hashes, owner maps, fixtures, artifacts, or handoff records.

### Edge 7: Staleness Report Identity Is Trusted Implicitly

Status: contained.

Review feedback added a manifest identity check before a fresh staleness report
can support a ready certificate. A report for another manifest blocks the
certificate.

### Edge 8: Integration Handoff Becomes Transition Authority

Status: contained.

Handoff rows enumerate forbidden promotions and carry
`handoff_constraint_only_not_transition_authority`. They may constrain
downstream use, but they cannot grant OTB transition legality or HOB subtree
closure.

### Edge 9: C Leaks Into Product Workflow

Status: contained.

Source patching, worker dispatch, ProgramBench workflow integration, product
truth, official-eval readiness, and future-family selection remain outside
`BRL-0-C`.

## Review Feedback Integrated

- Gemini review:
  impact-cone status now distinguishes required blocker rows from ordinary
  non-required omitted probes.
- Codex review:
  mixed covered/uncovered owner surfaces now return a blocked impact-cone
  report instead of failing validation.
- Gemini review:
  missing-scope selections now produce an explicit certificate known gap.
- Codex review:
  certificate building now verifies the staleness report belongs to the same
  manifest before trusting freshness.

## Residual Edges

- `BRL-0-C` remains a deterministic preservation-certificate and handoff slice
  only.
- It does not execute replay, generate probes, update expected hashes, dispatch
  workers, patch product code, authorize HOB closure, grant OTB transition
  legality, select future families, claim product truth, or authorize official
  evaluation.
- `BRL-0` is closed for the selected A/B/C behavioral replay lock family
  surfaces.
