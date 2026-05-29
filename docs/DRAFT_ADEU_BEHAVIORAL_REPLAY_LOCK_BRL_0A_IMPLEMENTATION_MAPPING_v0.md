# Draft ADEU Behavioral Replay Lock BRL-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned `BRL-0-A`.

Authority layer: support.

This note maps likely implementation for `BRL-0-A`. It does not authorize
implementation by itself and does not replace a future `vNext+<n>` lock,
stop-gate decision, or edge assessment.

## Slice Intent

`BRL-0-A` should make locked replay manifests deterministic and reviewable.

It should answer:

```text
Is this replay manifest structurally valid, hash-stable, and explicit about
the protected behavioral surfaces and canonicalization rules it claims?
```

It must not answer:

```text
Did a candidate pass replay?
Which probes should be selected?
Which owner surfaces are affected?
Is the implementation correct?
```

## Selected Surfaces

Likely schema / model surfaces:

- `repo_behavioral_replay_manifest@1`
- `repo_behavioral_probe_contract@1`
- `repo_behavioral_canonicalization_profile@1`
- `repo_behavioral_observation_hash@1`
- `repo_behavioral_replay_manifest_validation_report@1`
- `repo_behavioral_replay_lock_non_authority_guardrail@1`

Likely source files:

- `packages/adeu_behavioral_replay_lock/pyproject.toml`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/__init__.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/models.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/vocabulary.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/manifest.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/canonicalization.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/hashing.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/validation.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/export_schema.py`
- `packages/adeu_behavioral_replay_lock/tests/test_brl_0a.py`
- `packages/adeu_behavioral_replay_lock/tests/test_behavioral_replay_lock_export_schema.py`

## Field-Level Expectations

`repo_behavioral_replay_manifest@1` should include:

- `manifest_id`
- `manifest_version`
- `manifest_authority_layer`
- `manifest_lifecycle_state`
- `manifest_visibility_posture`
- `manifest_scope`
- `product_ref`
- `candidate_artifact_kind`
- `protected_owner_surfaces`
- `owner_surface_rows`
- `owner_surface_map_ref`
- `owner_surface_map_hash`
- `owner_surface_taxonomy_version`
- `canonicalization_profile_ref`
- `execution_environment_ref`
- `execution_environment_hash`
- `sensitive_material_policy_ref`
- `safe_rendering_policy_ref`
- `raw_material_storage_policy_ref`
- `redaction_profile_ref`
- `probe_contract_refs`
- `expected_observation_hash_refs`
- `suite_root_hash`
- `manifest_hash`

`repo_behavioral_probe_contract@1` should include:

- `probe_id`
- `probe_label`
- `owner_surface`
- `protected_sibling_group_ref`
- `argv`
- `stdin_ref`
- `env_delta`
- `cwd_ref`
- `fixture_tree_hash_before`
- `protected_surfaces`
- `surface_policy`
- `fixture_policy`
- `timeout_policy_ref`
- `canonicalization_profile_ref`
- `expected_observation_hash_ref`
- `probe_contract_hash`

`repo_behavioral_canonicalization_profile@1` should include:

- `canonicalization_profile_ref`
- `profile_version`
- `profile_hash`
- `text_rules`
- `structured_rules`
- `path_rules`
- `ordering_rules`
- `file_tree_rules`
- `process_rules`
- `timing_rules`
- `forbidden_normalizations`
- `rule_rows`

`repo_behavioral_observation_hash@1` should include:

- `observation_hash_ref`
- `probe_id`
- `hash_algorithm`
- `canonical_material_kind`
- `hash_domain`
- `exit_code`
- `stdout_hash`
- `stderr_hash`
- `output_file_tree_hash`
- `process_state_hash`
- `timeout_status`
- `canonical_observation_hash`
- `expected_observation_provenance`

`repo_behavioral_replay_manifest_validation_report@1` should include:

- `validation_report_ref`
- `manifest_id`
- `manifest_hash`
- `validation_status`
- `diagnostic_rows`
- `canonical_output_hash`

Owner-surface rows should include:

- `owner_surface`
- `patch_risk_kind`
- `protected_sibling_probe_refs`
- `required_when_touched`
- `coverage_posture`

Execution environment rows should include:

- `execution_environment_ref`
- `execution_environment_hash`
- `os`
- `arch`
- `runtime`
- `interpreter`
- `dependency_lock_ref`
- `locale`
- `timezone`
- `terminal_profile_ref`
- `env_policy_ref`

Surface policy rows should distinguish:

- `raw_observed_surfaces`
- `canonicalized_surfaces`
- `protected_surfaces`
- `explicitly_ignored_surfaces`

Fixture policy rows should distinguish:

- `fixture_tree_hash_before`
- `fixture_tree_hash_after_expected`
- `fixture_tree_protection_kind`
- `workspace_write_allowlist`
- `cleanup_policy_ref`

## Validation Rules

`BRL-0-A` should fail closed when:

- required manifest fields are missing;
- `probe_id` values are duplicated;
- protected surfaces are empty;
- a required owner surface has no protected sibling sentinel rows;
- a protected file-tree surface lacks before/after hash declarations;
- unknown canonicalization vocabulary appears;
- forbidden normalization rules attempt to hide exit-code, stderr, or file-tree
  changes without explicit scope;
- expected observation hash rows are missing for probe contracts;
- expected observation provenance is missing;
- execution environment identity is missing for a replayable manifest;
- a manifest with lifecycle `draft`, `proposed`, `stale`, `superseded`, or
  `invalid` claims certificate or promotion use;
- a manifest claims no-regression over an ignored surface;
- a canonicalization rule drops protected stderr, exit code, timeout status, or
  file-tree mutation;
- a mutating probe lacks expected after-hash or mutation policy;
- raw secret-like environment values appear without safe rendering/storage
  policy;
- owner labels are unknown without local extension posture and taxonomy refs;
- `suite_root_hash` does not match canonical child hash order;
- manifest hash is stale relative to child rows;
- non-authority guardrails are absent.

## Canonical Hash Rules

The initial slice should use deterministic canonical JSON with sorted keys for
hashing. Row order should be canonicalized by stable identifiers:

```text
probe rows:
  sorted by probe_id

canonicalization rules:
  sorted by rule_id

expected observation hashes:
  sorted by probe_id / observation_hash_ref
```

The hash algorithm should be explicit. `sha256` is the first supported
algorithm.

Hash input should be domain-separated by:

```text
schema_id
object_kind
object_version
hash_algorithm
canonicalization_profile_hash, when relevant
canonical payload
```

## Acceptance Tests

Initial tests should prove:

1. A valid manifest validates.
2. Shuffled row order keeps the same manifest hash.
3. Duplicate `probe_id` fails.
4. Missing expected observation hash fails.
5. Unknown canonicalization rule kind fails.
6. Empty protected surface set fails.
7. File-tree protection without fixture hash fails.
8. Suite-root mismatch fails.
9. Non-authority guardrail is exported.
10. Owner-surface rows can require protected sibling sentinels and fail closed
    when the manifest omits them.
11. Expected hash provenance is required.
12. Identical payloads under different object kinds hash differently.
13. Replayable manifests require execution environment profile.
14. Protected/ignored surface contradictions fail.
15. Canonicalization that hides protected stderr or exit code fails.
16. Mutating probes require after-hash or mutation policy.
17. Secret-like env values require safe rendering/storage policy.
18. Lifecycle state controls promotion posture.
19. Unknown owner labels fail unless declared as local extensions with taxonomy
    refs.
20. Canonicalization profile hash changes alter manifest hash.

## Deferred To Later Slices

`BRL-0-A` defers:

- replay execution;
- process spawning;
- filesystem fixture copying;
- candidate artifact packaging;
- observation capture;
- diff rendering;
- impact-cone selection;
- no-regression certificates;
- HOB/OTB transition enforcement.
