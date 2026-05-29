# LOCKED_CONTINUATION_vNEXT_PLUS279

## Status

Bounded starter lock draft for `BRL-0-B` (replay execution report, canonical
observation record, regression diff, and suite-root hash report).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`BRL-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `BRL-0`
- slice: `BRL-0-B`
- branch-local execution target: `arc/brl-0-b`

## Purpose

Freeze the bounded `BRL-0-B` starter slice so the repo can consume released
`BRL-0-A` replay manifests and validation reports, execute already-specified
probe contracts against a supplied candidate artifact, capture canonical
observations, compare expected and actual hashes, and emit structured replay
diffs and suite-root hash reports.

`vNext+279` authorizes docs plus the next implementation path over the existing
repo-owned `adeu_behavioral_replay_lock` package. It does not authorize
semantic adjudication, domain ontology generation, HOB closure recomputation,
OTB transition authorization, probe generation, freeform command planning,
worker dispatch, source patching, impact-cone selection, no-regression
certificates, product authorization, official-eval submission, graph-memory
authority, future-family selection, release authority, or recursive policy
amendment.

Controlling invariant:

```text
BRL-0-B may replay already-locked probe contracts and report expected-vs-actual
behavioral hashes.

BRL-0-B may not decide which probes should exist, silently update expected
hashes, select sentinels, certify no regression, or promote a passing replay
into product correctness.
```

## Instantiated Here

- `BRL-0-B` instantiates the second deterministic behavioral replay lock seam:
  - existing repo-owned package:
    - `adeu_behavioral_replay_lock`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v88.md`
    - `docs/ARCHITECTURE_ADEU_BEHAVIORAL_REPLAY_LOCK_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_BEHAVIORAL_REPLAY_LOCK_BRL_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_BEHAVIORAL_REPLAY_LOCK_BRL_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS278.md`
    - `docs/ASSESSMENT_vNEXT_PLUS278_EDGES.md`
    - `artifacts/agent_harness/v278/evidence_inputs/brl_0a_closeout_evidence_v278.json`
  - consumed package surfaces:
    - `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/brl_0a.py`
    - `packages/adeu_behavioral_replay_lock/tests/test_brl_0a.py`
    - `packages/adeu_behavioral_replay_lock/schema/`
  - emitted starter record shapes:
    - `repo_behavioral_replay_execution_report@1`
    - `repo_behavioral_observation_record@1`
    - `repo_behavioral_regression_diff@1`
    - `repo_behavioral_suite_root_hash_report@1`

## Machine-Checkable Contract

```json
{
  "schema": "brl_0b_starter_contract@1",
  "target_arc": "vNext+279",
  "target_path": "BRL-0-B",
  "family": "BRL-0",
  "slice": "BRL-0-B",
  "implementation_package": "packages/adeu_behavioral_replay_lock",
  "selected_record_shapes": [
    "repo_behavioral_replay_execution_report@1",
    "repo_behavioral_observation_record@1",
    "repo_behavioral_regression_diff@1",
    "repo_behavioral_suite_root_hash_report@1"
  ],
  "semantic_authority_granted": false,
  "domain_ontology_authority_granted": false,
  "hob_closure_authority_granted": false,
  "otb_transition_authority_granted": false,
  "probe_generation_authority_granted": false,
  "freeform_command_planning_authority_granted": false,
  "candidate_replay_execution_authority_granted": true,
  "observation_capture_authority_granted": true,
  "candidate_comparison_authority_granted": true,
  "impact_cone_selection_authority_granted": false,
  "no_regression_certificate_authority_granted": false,
  "implementation_authority_granted": false,
  "worker_dispatch_authority_granted": false,
  "product_authority_granted": false,
  "official_eval_authority_granted": false,
  "future_family_selection_granted": false
}
```

## Required Starter Vocabulary

`BRL-0-B` must reuse `BRL-0-A` vocabulary where possible and add only B-level
execution/capture/diff vocabulary:

- `replay_execution_status`
- `probe_execution_status`
- `observation_capture_status`
- `timeout_status`
- `regression_diff_status`
- `changed_surface_kind`
- `diff_authority_posture`
- `suite_root_status`
- `replay_execution_authority_posture`

Required diff statuses:

```text
match
diff
missing_expected
missing_actual
capture_failed
not_run
blocked_by_manifest_validation
```

Required B authority postures:

```text
replay_report_only_not_product_authority
diff_report_only_not_patch_authority
suite_hash_report_only_not_certificate
```

## Required Record Shapes

Minimum `repo_behavioral_replay_execution_report@1` fields:

- `execution_report_ref`
- `manifest_id`
- `manifest_hash`
- `manifest_validation_report_ref`
- `candidate_artifact_ref`
- `candidate_artifact_hash`
- `execution_environment_ref`
- `execution_environment_hash`
- `probe_execution_rows`
- `observation_record_refs`
- `diff_refs`
- `suite_root_hash_report_ref`
- `execution_status`
- `authority_posture`
- `canonical_output_hash`

Probe execution rows must include:

- `probe_id`
- `probe_contract_hash`
- `execution_status`
- `argv`
- `cwd_ref`
- `env_delta_hash`
- `timeout_policy_ref`
- `fixture_tree_hash_before`
- `fixture_tree_hash_after_actual`
- `observation_record_ref`
- `diff_ref`

Minimum `repo_behavioral_observation_record@1` fields:

- `observation_record_ref`
- `probe_id`
- `probe_contract_hash`
- `raw_exit_code`
- `raw_stdout_ref`
- `raw_stderr_ref`
- `raw_file_tree_hash_after`
- `raw_process_state_ref`
- `timeout_status`
- `canonicalization_profile_ref`
- `canonicalization_profile_hash`
- `canonical_stdout_hash`
- `canonical_stderr_hash`
- `canonical_file_tree_hash_after`
- `canonical_process_state_hash`
- `canonical_observation_hash`

Minimum `repo_behavioral_regression_diff@1` fields:

- `diff_ref`
- `probe_id`
- `expected_observation_hash_ref`
- `expected_canonical_observation_hash`
- `actual_observation_record_ref`
- `actual_canonical_observation_hash`
- `diff_status`
- `changed_surfaces`
- `structured_diff_rows`
- `authority_posture`
- `canonical_output_hash`

Minimum `repo_behavioral_suite_root_hash_report@1` fields:

- `suite_root_hash_report_ref`
- `manifest_id`
- `manifest_hash`
- `expected_suite_root_hash`
- `actual_suite_root_hash`
- `per_probe_hash_rows`
- `suite_root_status`
- `authority_posture`
- `canonical_output_hash`

## Required APIs

`BRL-0-B` must provide deterministic functions or equivalent module APIs that:

- load released `BRL-0-A` manifests, validation reports, probe contracts,
  canonicalization profiles, and expected observation hashes;
- reject replay when manifest validation is not green;
- execute only manifest-declared probe contracts without inventing argv, env,
  cwd, stdin, fixtures, or cleanup behavior;
- capture raw exit, stdout, stderr, file-tree, process-state, and timeout
  surfaces according to the probe contract;
- apply the locked canonicalization profile without hiding protected surfaces;
- compute actual canonical observation hashes and suite-root hashes;
- compare expected and actual hashes without mutating expected baselines;
- emit deterministic execution, observation, diff, and suite-root reports;
- compute stable canonical hashes independent of input row ordering.

## Required Validation

`BRL-0-B` must fail closed when:

- input manifest validation status is not green;
- manifest, validation report, probe contract, expected observation, or
  canonicalization profile hashes do not match released A records;
- candidate artifact identity or execution environment identity is missing;
- a probe contract requests a surface that cannot be observed;
- a probe times out outside its declared timeout policy;
- canonicalization profile referenced by the manifest is unavailable or stale;
- replay mutates a protected fixture tree contrary to the fixture policy;
- expected hashes are silently updated instead of reported as diffs;
- changed protected surfaces are omitted from the diff rows;
- suite-root report claims certificate or product authority;
- unknown vocabulary appears in any B row.

## Required Starter Fixtures

`BRL-0-B` must include focused fixtures for:

1. green A manifest replays to matching observation and suite-root report;
2. manifest validation failure blocks replay;
3. stale manifest hash fails;
4. stale probe contract hash fails;
5. stale canonicalization profile hash fails;
6. candidate artifact identity is required;
7. missing protected stdout/stderr/exit capture fails;
8. changed stdout emits a structured diff;
9. changed stderr emits a structured diff;
10. changed exit code emits a structured diff;
11. changed file-tree hash emits a structured diff;
12. timeout outside policy is reported and does not update expected hashes;
13. fixture mutation contrary to policy fails closed;
14. expected hash update attempt fails closed;
15. suite-root hash report is deterministic under shuffled rows;
16. suite-root report cannot claim no-regression certificate authority.

## Deferred

Deferred to `BRL-0-C`:

- impact-cone sentinel selection;
- fast partial-manifest selection from touched owner surfaces;
- no-regression certificates;
- stale-lock invalidation after owner maps, fixtures, artifacts, or expected
  hashes change;
- HOB/OTB integration handoff.

Deferred to later families or explicit future integration:

- HOB closure changes;
- OTB transition enforcement;
- ProgramBench workflow integration;
- worker dispatch;
- product correctness claims;
- official-eval readiness claims.

## Local Gates

For this docs-only starter bundle:

```text
make arc-start-check ARC=279
```

For the later implementation PR:

```text
make check
```
