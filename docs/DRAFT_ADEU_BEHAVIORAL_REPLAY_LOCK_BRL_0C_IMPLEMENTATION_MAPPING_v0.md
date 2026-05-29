# Draft ADEU Behavioral Replay Lock BRL-0-C Implementation Mapping v0

Status: support / implementation mapping record for planned `BRL-0-C`.

Authority layer: support.

This note maps likely later implementation for `BRL-0-C`. It is not selected by
itself and should remain deferred until `BRL-0-A` and `BRL-0-B` exist on
`main`.

## Slice Intent

`BRL-0-C` should connect replay results to bounded no-regression handoff.

It should answer:

```text
Given a touched owner-surface set, HOB/OTB handoff rows, and replay results,
which protected sentinels were required, which were replayed, and what bounded
no-regression certificate or blocker follows?
```

It must not answer:

```text
Is a HOB subtree closed?
Is an OTB transition legal?
Is the product correct?
Should code be patched?
```

## Candidate Surfaces

- `repo_behavioral_impact_cone_selection_report@1`
- `repo_behavioral_no_regression_certificate@1`
- `repo_behavioral_lock_staleness_report@1`
- `repo_behavioral_replay_integration_handoff@1`

## Impact Cone Selection

`repo_behavioral_impact_cone_selection_report@1` should include:

- `impact_cone_report_ref`
- `candidate_change_ref`
- `touched_owner_surfaces`
- `available_manifest_refs`
- `required_probe_refs`
- `selected_probe_refs`
- `omitted_probe_rows`
- `selection_status`
- `canonical_output_hash`

The selection should be deterministic over declared owner surfaces. If a touched
owner lacks sentinel coverage, the report should block certificate emission
rather than silently proceed.

## No-Regression Certificate

`repo_behavioral_no_regression_certificate@1` should include:

- `certificate_ref`
- `manifest_id`
- `manifest_hash`
- `candidate_artifact_ref`
- `candidate_artifact_hash`
- `execution_report_ref`
- `impact_cone_report_ref`
- `certificate_posture`
- `bounded_claim`
- `covered_probe_refs`
- `covered_owner_surfaces`
- `known_gaps`
- `authority_posture`
- `certificate_hash`

Allowed posture examples:

```text
impact_cone_no_observed_regression
full_manifest_no_observed_regression
packaged_artifact_no_observed_regression
blocked_by_missing_sentinel
blocked_by_replay_diff
blocked_by_stale_manifest
```

## Staleness Report

`repo_behavioral_lock_staleness_report@1` should include:

- `staleness_report_ref`
- `manifest_id`
- `staleness_status`
- `stale_reason_rows`
- `required_refresh_rows`
- `canonical_output_hash`

Staleness reasons include:

- probe contract hash changed;
- fixture tree hash changed;
- canonicalization profile changed;
- expected observation hash changed;
- owner surface map changed;
- candidate artifact substrate changed;
- HOB/OTB handoff hash changed.

## Integration Handoff

`repo_behavioral_replay_integration_handoff@1` should include:

- `handoff_ref`
- `source_family`
- `target_family`
- `certificate_refs`
- `blocker_refs`
- `bounded_use`
- `forbidden_promotions`

The handoff may constrain downstream transitions but may not grant product
truth by itself.

## Acceptance Theme

`BRL-0-C` should make this claim precise:

```text
The changed candidate preserved all protected behavior in the selected replay
scope, or the exact missing/different protected surface is known.
```

It should reject:

```text
All tests probably still pass.
No regression because the patch was small.
No regression because official score improved.
```

