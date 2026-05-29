# Draft ADEU Behavioral Replay Lock BRL-0-B Implementation Mapping v0

Status: support / implementation mapping record for planned `BRL-0-B`.

Authority layer: support.

This note maps likely later implementation for `BRL-0-B`. It is not selected by
itself and should remain deferred until `BRL-0-A` exists on `main`.

## Slice Intent

`BRL-0-B` should consume released manifest records from `BRL-0-A`, run the
specified replay, capture canonical observations, and emit diffs.

It should answer:

```text
When this locked manifest is replayed against this candidate artifact, which
protected observation hashes match and which differ?
```

It must not answer:

```text
Should these probes exist?
Should a patch be made?
Is official eval safe?
Is the product semantically correct?
```

## Candidate Surfaces

- `repo_behavioral_replay_execution_report@1`
- `repo_behavioral_observation_record@1`
- `repo_behavioral_regression_diff@1`
- `repo_behavioral_suite_root_hash_report@1`

## Execution Report Expectations

`repo_behavioral_replay_execution_report@1` should include:

- `execution_report_ref`
- `manifest_id`
- `manifest_hash`
- `candidate_artifact_ref`
- `candidate_artifact_hash`
- `execution_environment_ref`
- `probe_execution_rows`
- `observation_record_refs`
- `diff_refs`
- `suite_root_hash_report_ref`
- `execution_status`
- `canonical_output_hash`

## Observation Record Expectations

`repo_behavioral_observation_record@1` should include:

- `observation_record_ref`
- `probe_id`
- `raw_exit_code`
- `raw_stdout_ref`
- `raw_stderr_ref`
- `raw_file_tree_hash_after`
- `raw_process_state_ref`
- `timeout_status`
- `canonicalization_profile_ref`
- `canonical_stdout_hash`
- `canonical_stderr_hash`
- `canonical_file_tree_hash_after`
- `canonical_process_state_hash`
- `canonical_observation_hash`

## Diff Expectations

`repo_behavioral_regression_diff@1` should include:

- `diff_ref`
- `probe_id`
- `diff_status`
- `changed_surfaces`
- `expected_observation_hash`
- `actual_observation_hash`
- `structured_diff_rows`
- `authority_posture`

Diff rows should identify the surface:

```text
exit_code
stdout
stderr
output_files
fixture_tree
process_state
timeout
```

## Validation Rules

`BRL-0-B` should fail closed when:

- input manifest validation is not green;
- candidate artifact identity is missing;
- a protected surface cannot be observed;
- a probe times out outside declared timeout policy;
- canonicalization profile referenced by the manifest is unavailable;
- replay mutates a fixture tree that is declared protected;
- an expected hash is silently updated instead of reported as a diff.

## Deferred To `BRL-0-C`

`BRL-0-B` does not select which manifest subset should run. It executes the
manifest or manifest slice supplied to it. Impact-cone selection and certificate
posture belong to `BRL-0-C`.

