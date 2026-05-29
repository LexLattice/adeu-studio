# LOCKED_CONTINUATION_vNEXT_PLUS278

## Status

Bounded starter lock draft for `BRL-0-A` (behavioral replay manifest, probe
contract, canonicalization profile, expected observation hash, manifest
validation report, and non-authority guardrail).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`BRL-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `BRL-0`
- slice: `BRL-0-A`
- branch-local execution target: `arc/brl-0-a`

## Purpose

Freeze the bounded `BRL-0-A` starter slice so the repo can represent and
validate locked behavioral replay manifests before any later slice executes a
probe, captures observations, computes diffs, selects impact-cone sentinels, or
issues no-regression certificates.

`vNext+278` authorizes docs plus the next implementation path over a new
repo-owned behavioral replay lock package. It does not authorize semantic
adjudication, domain ontology generation, HOB closure recomputation, OTB
transition authorization, probe generation, probe execution, command execution
outside the implementation/test lane, worker dispatch, implementation batches,
candidate replay execution, observation capture, candidate comparison,
impact-cone selection, no-regression certificates, product authorization,
official-eval submission, graph-memory authority, future-family selection,
release authority, or recursive policy amendment.

Controlling invariant:

```text
BRL-0-A may validate the structure, identity, canonicalization profile,
expected-observation hashes, owner-surface map, protected surfaces,
environment profile, fixture policy, lifecycle posture, and non-authority
guardrails of a replay manifest.

BRL-0-A may not execute the manifest, observe a candidate, compare behavior,
select sentinels, or certify no regression.
```

## Instantiated Here

- `BRL-0-A` instantiates the first deterministic behavioral replay lock seam:
  - new repo-owned package:
    - `adeu_behavioral_replay_lock`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v88.md`
    - `docs/ARCHITECTURE_ADEU_BEHAVIORAL_REPLAY_LOCK_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_BEHAVIORAL_REPLAY_LOCK_BRL_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_BEHAVIORAL_REPLAY_LOCK_BRL_0A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/support/programbench_revive_v47_causal_story_to_100.md`
  - emitted starter record shapes:
    - `repo_behavioral_replay_manifest@1`
    - `repo_behavioral_probe_contract@1`
    - `repo_behavioral_canonicalization_profile@1`
    - `repo_behavioral_observation_hash@1`
    - `repo_behavioral_replay_manifest_validation_report@1`
    - `repo_behavioral_replay_lock_non_authority_guardrail@1`

## Machine-Checkable Contract

```json
{
  "schema": "brl_0a_starter_contract@1",
  "target_arc": "vNext+278",
  "target_path": "BRL-0-A",
  "family": "BRL-0",
  "slice": "BRL-0-A",
  "implementation_package": "packages/adeu_behavioral_replay_lock",
  "selected_record_shapes": [
    "repo_behavioral_replay_manifest@1",
    "repo_behavioral_probe_contract@1",
    "repo_behavioral_canonicalization_profile@1",
    "repo_behavioral_observation_hash@1",
    "repo_behavioral_replay_manifest_validation_report@1",
    "repo_behavioral_replay_lock_non_authority_guardrail@1"
  ],
  "semantic_authority_granted": false,
  "domain_ontology_authority_granted": false,
  "hob_closure_authority_granted": false,
  "otb_transition_authority_granted": false,
  "probe_generation_authority_granted": false,
  "probe_execution_authority_granted": false,
  "candidate_replay_execution_authority_granted": false,
  "observation_capture_authority_granted": false,
  "candidate_comparison_authority_granted": false,
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

The implementation must define one shared vocabulary source for A/B/C-ready
terms, even though only A surfaces ship in this slice.

Minimum shared vocabulary:

- `manifest_authority_layer`
- `manifest_lifecycle_state`
- `manifest_visibility_posture`
- `probe_owner_surface_kind`
- `patch_risk_kind`
- `protected_surface_kind`
- `surface_policy_kind`
- `fixture_tree_protection_kind`
- `canonicalization_rule_kind`
- `expected_observation_authority_posture`
- `expected_observation_provenance_kind`
- `observation_surface_kind`
- `hash_algorithm`
- `hash_domain`
- `replay_validation_status`
- `manifest_validation_diagnostic_kind`
- `authority_posture`

Minimum owner-surface vocabulary:

- `control_plane_parser`
- `public_schema_mode_dispatch`
- `resource_route_topology`
- `input_dialect_reader`
- `transform_or_embedded_language`
- `state_lifecycle_mutation`
- `subject_identity_binding`
- `output_router_renderer`
- `diagnostic_exit_channel`
- `runtime_substrate_dependency`
- `side_effect_workspace`
- `config_policy_activation`
- `generic_fallback_or_default_behavior`
- `local_extension`

No A/B/C slice may define overlapping strings independently.

## Required Record Shapes

Minimum `repo_behavioral_replay_manifest@1` fields:

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

Minimum owner-surface row fields:

- `owner_surface`
- `patch_risk_kind`
- `protected_sibling_probe_refs`
- `required_when_touched`
- `coverage_posture`
- `local_extension_posture`
- `taxonomy_ref`

Minimum execution environment row fields:

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

Minimum `repo_behavioral_probe_contract@1` fields:

- `probe_id`
- `probe_label`
- `owner_surface`
- `protected_sibling_group_ref`
- `argv`
- `stdin_ref`
- `env_delta`
- `cwd_ref`
- `fixture_tree_hash_before`
- `fixture_tree_hash_after_expected`
- `fixture_tree_protection_kind`
- `workspace_write_allowlist`
- `cleanup_policy_ref`
- `protected_surfaces`
- `surface_policy`
- `fixture_policy`
- `timeout_policy_ref`
- `canonicalization_profile_ref`
- `expected_observation_hash_ref`
- `probe_contract_hash`

Minimum surface policy fields:

- `raw_observed_surfaces`
- `canonicalized_surfaces`
- `protected_surfaces`
- `explicitly_ignored_surfaces`

Minimum `repo_behavioral_canonicalization_profile@1` fields:

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

Minimum canonicalization rule row fields:

- `rule_id`
- `rule_kind`
- `applies_to_surfaces`
- `scope`
- `protected_surface_effect`
- `rule_hash`

Minimum `repo_behavioral_observation_hash@1` fields:

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

Minimum expected-observation provenance fields:

- `provenance_kind`
- `source_ref`
- `source_hash`
- `authority_layer`
- `evidence_boundary_posture`
- `clean_first_pass_posture`

Minimum `repo_behavioral_replay_manifest_validation_report@1` fields:

- `validation_report_ref`
- `manifest_id`
- `manifest_hash`
- `validation_status`
- `diagnostic_rows`
- `canonical_output_hash`

Minimum `repo_behavioral_replay_lock_non_authority_guardrail@1` fields:

- `guardrail_ref`
- `semantic_authority_granted`
- `probe_generation_authority_granted`
- `probe_execution_authority_granted`
- `candidate_replay_execution_authority_granted`
- `observation_capture_authority_granted`
- `candidate_comparison_authority_granted`
- `impact_cone_selection_authority_granted`
- `no_regression_certificate_authority_granted`
- `product_authority_granted`
- `official_eval_authority_granted`
- `future_family_selection_granted`

## Required APIs

`BRL-0-A` must provide deterministic functions or equivalent module APIs that:

- load replay manifests, probe contracts, canonicalization profiles, expected
  observation hashes, owner-surface rows, and guardrail rows;
- validate required fields, shared vocabulary, duplicates, cross references,
  lifecycle posture, visibility posture, surface policy, fixture policy,
  expected-observation provenance, execution environment identity, sensitive
  material policy, and non-authority guardrails;
- compute stable canonical hashes with sorted keys and stable row ordering;
- domain-separate hash inputs by schema id, object kind, object version,
  hash algorithm, canonicalization profile hash when relevant, and canonical
  payload;
- emit validation reports with deterministic diagnostic ordering;
- export authoritative JSON schema plus root `spec/` mirrors.

## Required Validation

`BRL-0-A` must fail closed when:

- required manifest fields are missing;
- `probe_id` values are duplicated;
- protected surfaces are empty;
- a required owner surface has no protected sibling sentinel rows;
- a required owner label is unknown and lacks explicit local-extension posture,
  taxonomy ref, and coverage posture;
- a protected file-tree surface lacks before/after hash declarations;
- unknown canonicalization vocabulary appears;
- canonicalization attempts to hide protected exit code, stderr, timeout status,
  file-tree mutation, or process-state changes;
- a manifest claims no-regression over an ignored surface;
- expected observation hash rows are missing for probe contracts;
- expected observation provenance is missing;
- expected observation provenance lacks source hash, authority layer, evidence
  boundary posture, or clean-first-pass posture;
- execution environment identity is missing for a replayable manifest;
- execution environment hash is stale relative to the environment row;
- a mutating probe lacks expected after-hash or mutation policy;
- raw secret-like environment values appear without safe rendering, storage, and
  redaction policy refs;
- a manifest with lifecycle `draft`, `proposed`, `stale`, `superseded`, or
  `invalid` claims certificate or promotion use;
- `suite_root_hash` does not match canonical child hash order;
- `manifest_hash` is stale relative to child rows;
- non-authority guardrails are absent or grant any forbidden authority.

## Canonical Hash Rules

The initial slice must use deterministic canonical JSON with sorted keys for
hashing. Row order must be canonicalized by stable identifiers:

```text
probe rows:
  sorted by probe_id

owner-surface rows:
  sorted by owner_surface

canonicalization rules:
  sorted by rule_id

expected observation hashes:
  sorted by probe_id / observation_hash_ref
```

The first supported hash algorithm is `sha256`. Hash strings must use an
explicit `sha256:<hex>` representation.

Identical payload bytes under different schema ids, object kinds, object
versions, hash algorithms, or canonicalization profile hashes must produce
different domain-separated object hashes.

## Required Starter Fixtures

`BRL-0-A` must include focused fixtures for:

1. a valid manifest validates;
2. shuffled row order keeps the same manifest hash;
3. duplicate `probe_id` fails;
4. missing expected observation hash fails;
5. unknown canonicalization rule kind fails;
6. empty protected surface set fails;
7. file-tree protection without fixture hash fails;
8. suite-root mismatch fails;
9. stale manifest hash fails;
10. non-authority guardrail is exported and denies all forbidden authority;
11. owner-surface rows can require protected sibling sentinels and fail closed
    when the manifest omits them;
12. expected observation provenance is required;
13. identical payloads under different object kinds hash differently;
14. replayable manifests require execution environment profile;
15. protected/ignored surface contradictions fail;
16. canonicalization that hides protected stderr, exit code, timeout status, or
    file-tree mutation fails;
17. mutating probes require after-hash or mutation policy;
18. secret-like env values require safe rendering, storage, and redaction
    policy refs;
19. lifecycle state controls promotion posture;
20. unknown owner labels fail unless declared as local extensions with taxonomy
    refs;
21. canonicalization profile hash changes alter manifest hash.

## Deferred

Deferred to `BRL-0-B`:

- replay execution;
- process spawning;
- filesystem fixture copying;
- candidate artifact packaging;
- candidate observation capture;
- canonical observation records;
- per-probe behavior diffs;
- suite-root hash comparison reports.

Deferred to `BRL-0-C`:

- impact-cone sentinel selection;
- no-regression certificates;
- lock staleness reports;
- HOB/OTB integration handoff;
- stale-baseline invalidation after protected owner maps change.

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
make arc-start-check ARC=278
```

For the later implementation PR:

```text
make check
```
