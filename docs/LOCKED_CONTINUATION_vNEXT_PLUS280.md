# LOCKED_CONTINUATION_vNEXT_PLUS280

## Status

Bounded starter lock draft for `BRL-0-C` (impact-cone sentinel selection,
bounded no-regression certificate, stale-lock report, and integration handoff).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`BRL-0-C` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `BRL-0`
- slice: `BRL-0-C`
- branch-local execution target: `arc/brl-0-c`

## Purpose

Freeze the bounded `BRL-0-C` starter slice so the repo can consume released
`BRL-0-A` replay manifests, released `BRL-0-B` replay/diff reports, and
declared owner-surface handoff rows to decide which protected sentinels are
required, whether those sentinels were replayed, whether a bounded
no-regression certificate is valid, and whether stale-lock refresh is required.

`vNext+280` authorizes docs plus the next implementation path over the existing
repo-owned `adeu_behavioral_replay_lock` package. It does not authorize
semantic adjudication, HOB closure recomputation, OTB transition authorization,
probe generation, replay execution, expected-hash updates, source patching,
product correctness claims, official-eval submission, graph-memory authority,
future-family selection, release authority, or recursive policy amendment.

Controlling invariant:

```text
BRL-0-C may turn released replay results and declared owner-surface scope into
a bounded preservation certificate or an explicit blocker.

BRL-0-C may not turn that certificate into product truth, HOB closure, OTB
transition legality, or official-eval readiness.
```

## Instantiated Here

- `BRL-0-C` instantiates the third deterministic behavioral replay lock seam:
  - existing repo-owned package:
    - `adeu_behavioral_replay_lock`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v88.md`
    - `docs/ARCHITECTURE_ADEU_BEHAVIORAL_REPLAY_LOCK_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_BEHAVIORAL_REPLAY_LOCK_BRL_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_BEHAVIORAL_REPLAY_LOCK_BRL_0C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS279.md`
    - `docs/ASSESSMENT_vNEXT_PLUS279_EDGES.md`
    - `artifacts/agent_harness/v279/evidence_inputs/brl_0b_closeout_evidence_v279.json`
  - consumed package surfaces:
    - `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/brl_0a.py`
    - `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/brl_0b.py`
    - `packages/adeu_behavioral_replay_lock/tests/test_brl_0a.py`
    - `packages/adeu_behavioral_replay_lock/tests/test_brl_0b.py`
    - `packages/adeu_behavioral_replay_lock/schema/`
  - emitted starter record shapes:
    - `repo_behavioral_impact_cone_selection_report@1`
    - `repo_behavioral_no_regression_certificate@1`
    - `repo_behavioral_lock_staleness_report@1`
    - `repo_behavioral_replay_integration_handoff@1`

## Machine-Checkable Contract

```json
{
  "schema": "brl_0c_starter_contract@1",
  "target_arc": "vNext+280",
  "target_path": "BRL-0-C",
  "family": "BRL-0",
  "slice": "BRL-0-C",
  "implementation_package": "packages/adeu_behavioral_replay_lock",
  "selected_record_shapes": [
    "repo_behavioral_impact_cone_selection_report@1",
    "repo_behavioral_no_regression_certificate@1",
    "repo_behavioral_lock_staleness_report@1",
    "repo_behavioral_replay_integration_handoff@1"
  ],
  "semantic_authority_granted": false,
  "domain_ontology_authority_granted": false,
  "hob_closure_authority_granted": false,
  "otb_transition_authority_granted": false,
  "probe_generation_authority_granted": false,
  "candidate_replay_execution_authority_granted": false,
  "expected_hash_update_authority_granted": false,
  "impact_cone_selection_authority_granted": true,
  "no_regression_certificate_authority_granted": true,
  "staleness_report_authority_granted": true,
  "integration_handoff_authority_granted": true,
  "implementation_authority_granted": false,
  "worker_dispatch_authority_granted": false,
  "product_authority_granted": false,
  "official_eval_authority_granted": false,
  "future_family_selection_granted": false
}
```

## Required Starter Vocabulary

`BRL-0-C` must reuse `BRL-0-A` and `BRL-0-B` vocabulary where possible and add
only C-level selection/certificate/staleness/handoff vocabulary:

- `impact_cone_selection_status`
- `owner_surface_coverage_status`
- `sentinel_selection_reason`
- `certificate_posture`
- `certificate_authority_posture`
- `staleness_status`
- `stale_reason_kind`
- `integration_handoff_status`
- `bounded_use_posture`

Required certificate postures:

```text
impact_cone_no_observed_regression
full_manifest_no_observed_regression
packaged_artifact_no_observed_regression
blocked_by_missing_sentinel
blocked_by_replay_diff
blocked_by_stale_manifest
blocked_by_stale_owner_surface_map
blocked_by_unreplayed_required_sentinel
```

Required C authority postures:

```text
bounded_replay_preservation_only_not_product_truth
handoff_constraint_only_not_transition_authority
staleness_report_only_not_refresh_authority
```

## Required Record Shapes

Minimum `repo_behavioral_impact_cone_selection_report@1` fields:

- `impact_cone_report_ref`
- `candidate_change_ref`
- `touched_owner_surfaces`
- `available_manifest_refs`
- `required_probe_refs`
- `selected_probe_refs`
- `omitted_probe_rows`
- `selection_status`
- `authority_posture`
- `canonical_output_hash`

Minimum `repo_behavioral_no_regression_certificate@1` fields:

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

Minimum `repo_behavioral_lock_staleness_report@1` fields:

- `staleness_report_ref`
- `manifest_id`
- `staleness_status`
- `stale_reason_rows`
- `required_refresh_rows`
- `authority_posture`
- `canonical_output_hash`

Minimum `repo_behavioral_replay_integration_handoff@1` fields:

- `handoff_ref`
- `source_family`
- `target_family`
- `certificate_refs`
- `blocker_refs`
- `bounded_use`
- `forbidden_promotions`
- `handoff_status`
- `authority_posture`
- `canonical_output_hash`

## Required APIs

`BRL-0-C` must provide deterministic functions or equivalent module APIs that:

- consume released `BRL-0-A` manifests and released `BRL-0-B` replay execution,
  diff, observation, and suite-root reports;
- consume declared candidate change identity and touched owner-surface rows;
- select required replay sentinels from owner-surface coverage without inventing
  new probe contracts;
- block certificate emission when a touched owner surface has no required
  sentinel coverage;
- block certificate emission when any selected sentinel is missing, stale,
  not replayed, or different;
- emit bounded certificates only over the selected replay scope;
- emit stale-lock reports for changed probe contracts, fixtures,
  canonicalization profiles, expected observations, owner-surface maps,
  candidate artifact substrate, or HOB/OTB handoff hashes;
- emit integration handoff rows that constrain downstream use but do not grant
  transition legality or product truth;
- compute stable canonical hashes independent of input row ordering.

## Required Validation

`BRL-0-C` must fail closed when:

- released A or B records are invalid, missing, or hash-stale;
- candidate change identity is missing;
- touched owner surfaces are missing when partial replay scope is requested;
- a touched owner surface has no matching sentinel coverage;
- an omitted required probe lacks an explicit blocker;
- a selected probe has a `diff`, `capture_failed`, `not_run`, or stale status;
- certificate posture exceeds covered probe and owner-surface scope;
- stale-lock reasons are present but certificate emission proceeds;
- handoff rows claim HOB closure, OTB transition legality, product truth, or
  official-eval readiness;
- unknown vocabulary appears in any C row.

## Required Starter Fixtures

`BRL-0-C` must include focused fixtures for:

1. full-manifest replay match emits a bounded no-regression certificate;
2. touched owner surfaces select only required sentinels;
3. missing sentinel coverage blocks certificate emission;
4. unreplayed selected sentinel blocks certificate emission;
5. replay diff blocks certificate emission;
6. stale manifest hash blocks certificate emission;
7. stale owner-surface map blocks certificate emission;
8. stale canonicalization profile blocks certificate emission;
9. stale expected observation hash blocks certificate emission;
10. stale HOB/OTB handoff hash emits a staleness report;
11. certificate bounded claim cannot exceed selected replay scope;
12. integration handoff constrains downstream use but cannot grant transition
    authority;
13. deterministic ordering for selected probes, blockers, stale rows, and
    certificate hashes;
14. unknown vocabulary fails closed.

## Deferred

Deferred outside `BRL-0-C`:

- HOB closure changes;
- OTB transition enforcement;
- ProgramBench workflow integration;
- worker dispatch;
- source patching;
- product correctness claims;
- official-eval readiness claims;
- future-family selection.

## Local Gates

For this docs-only starter bundle:

```text
make arc-start-check ARC=280
```

For the later implementation PR:

```text
make check
```
