# Architecture ADEU Behavioral Replay Lock Family v0

Status: architecture / decomposition note for planned `BRL-0`.

Authority layer: architecture / decomposition.

This note does not authorize semantic adjudication, ontology generation,
probe generation, probe execution, command execution, code edits, worker
dispatch, implementation authority, product authority, graph-memory authority,
recursive policy amendment, PR creation, commit, merge, release, or
future-family selection by itself. It defines the intended family boundary so
starter locks can select bounded implementation slices.

## Family Thesis

`BRL-0` should make behavioral no-regression claims deterministic and bounded.

The missing institutional layer is not another semantic ontology and not another
phase-transition broker. It is the preservation check after a candidate changes:

```text
previously green protected behavior
  + candidate patch
  -> deterministic replay
  -> canonical observation hashes
  -> pass/diff/no-regression certificate
```

Controlling invariant:

```text
Evidence of no regression transfers only through a locked replay manifest and
a successful canonical replay under the manifest's declared observation and
canonicalization rules.
```

Shared-owner invariant:

```text
A shared-owner patch must import protected sibling sentinels before becoming a
new promoted baseline.
```

Typical shared owners include:

```text
formatter registry and byte grammar
config discovery and activation normalization
file/resource routing
package/type context
directive and suppression scope
generic finding fallback
diagnostic and exit-code routing
```

## Relation To HOB And OTB

`BRL-0` is adjacent to but distinct from `HOB-0` and `OTB-0`.

```text
HOB-0:
  deterministic obligation inheritance inside ontology trees

OTB-0:
  deterministic transition legality between meta-program phases

BRL-0:
  deterministic preservation of previously locked behavioral observations
```

HOB leaves may name protected sentinel probes. OTB transitions may require BRL
certificates before allowing local parity, packaged preflight, official-like
eval, or official eval. BRL does not decide HOB closure and does not decide OTB
transition legality by itself.

## Source Stack Consumed

`BRL-0` consumes:

- HOB family doctrine on obligation ownership and child preservation;
- OTB family doctrine on transition gates and authority boundaries;
- ProgramBench support runs showing manual no-regression replay pressure,
  especially the `revive` v47 sequence;
- methodological equivalence doctrine that evidence transfers only through
  witnessed equivalence;
- semantic compiler doctrine on stable IDs, canonical hashes, and fail-closed
  validation.

No consumed source becomes product truth authority, implementation authority,
or future-family selection by being consumed.

## Family Slices

### `BRL-0-A`: Manifest, Canonicalization, And Hash Schema

Starter surfaces:

- `repo_behavioral_replay_manifest@1`
- `repo_behavioral_probe_contract@1`
- `repo_behavioral_canonicalization_profile@1`
- `repo_behavioral_observation_hash@1`
- `repo_behavioral_replay_manifest_validation_report@1`
- `repo_behavioral_replay_lock_non_authority_guardrail@1`

Purpose:

- represent a locked behavioral replay manifest;
- define probe contracts with argv/stdin/env/cwd/fixture expectations;
- define canonicalization profiles for volatile text, JSON, XML, file-tree,
  process, and timing surfaces;
- define canonical observation hash material;
- validate manifest completeness, vocabulary, duplicates, hash consistency, and
  declared protected surfaces;
- export non-authority guardrails.

Forbidden:

- executing probes;
- selecting impact-cone sentinels;
- comparing candidate observations;
- emitting no-regression certificates;
- generating probes;
- deciding semantic/product truth.

### `BRL-0-B`: Replay Execution, Observation Capture, And Diff

Later surfaces:

- `repo_behavioral_replay_execution_report@1`
- `repo_behavioral_observation_record@1`
- `repo_behavioral_regression_diff@1`
- `repo_behavioral_suite_root_hash_report@1`

Purpose:

- replay manifest probes against a supplied candidate artifact;
- capture exit/stdout/stderr/files/process/timing observations;
- canonicalize observations according to the locked profile;
- compute per-probe and suite-root hashes;
- compare expected and actual canonical observations;
- emit structured diffs without granting product authority.

Forbidden:

- deciding which probes should exist;
- patching source;
- dispatching workers;
- treating a passing replay as universal correctness;
- silently updating expected hashes.

### `BRL-0-C`: Impact Cone, Certificates, And Integration Handoff

Later surfaces:

- `repo_behavioral_impact_cone_selection_report@1`
- `repo_behavioral_no_regression_certificate@1`
- `repo_behavioral_lock_staleness_report@1`
- `repo_behavioral_replay_integration_handoff@1`

Purpose:

- select protected sentinels from declared touched owner surfaces and HOB/OTB
  handoff records;
- distinguish fast impact-cone replay from full locked manifest replay;
- issue bounded no-regression certificates;
- invalidate stale manifests when probe contracts, fixtures, canonicalization
  profiles, artifacts, owner maps, or expected hashes change;
- provide HOB/OTB integration handoff without taking over their authority.

Forbidden:

- claiming official readiness without an OTB transition;
- claiming HOB closure;
- generating new semantic obligations;
- treating score improvement as no-regression proof.

## Core Data Concepts

### Replay Manifest

```yaml
manifest_id: revive_v47_locked_tail
manifest_version: 1
manifest_authority_layer: support | lock
manifest_scope:
  product_ref: string
  protected_owner_surfaces: []
  bounded_claim: "no observed regression over this manifest"
owner_surface_rows:
  - owner_surface: string
    patch_risk_kind: formatter | config | file_routing | package_context |
      directive_scope | generic_fallback | diagnostic_routing | other
    protected_sibling_probe_refs: []
owner_surface_map_ref: string
owner_surface_map_hash: "sha256:..."
owner_surface_taxonomy_version: string
canonicalization_profile_ref: string
execution_environment_ref: string
execution_environment_hash: "sha256:..."
manifest_lifecycle_state: draft | proposed | locked | released | stale |
  superseded | invalid
manifest_visibility_posture: implementation_visible_regression |
  checker_only_sealed | orchestrator_only | public_reference_matrix |
  source_tail_matrix
sensitive_material_policy_ref: string
safe_rendering_policy_ref: string
probe_rows: []
expected_observation_hashes: []
suite_root_hash: "sha256:..."
```

### Probe Contract

```yaml
probe_id: string
owner_surface: string
argv: []
stdin_ref: string | null
env_delta: {}
cwd_ref: string
fixture_tree_hash_before: "sha256:..."
protected_surfaces:
  exit_code: true
  stdout: true
  stderr: true
  files: false
  process_state: false
  timing: false
surface_policy:
  raw_observed_surfaces: []
  canonicalized_surfaces: []
  protected_surfaces: []
  explicitly_ignored_surfaces: []
fixture_policy:
  fixture_tree_hash_before: "sha256:..." | null
  fixture_tree_hash_after_expected: "sha256:..." | null
  fixture_tree_protection_kind: immutable | mutation_expected |
    mutation_allowed_unprotected | cleanup_required | output_only
  workspace_write_allowlist: []
  cleanup_policy_ref: string | null
timeout_policy_ref: string
canonicalization_profile_ref: string
```

### Observation Hash

```yaml
probe_id: string
canonical_observation_material:
  exit_code: int | null
  stdout_hash: "sha256:..."
  stderr_hash: "sha256:..."
  output_file_tree_hash: "sha256:..." | null
  process_state_hash: "sha256:..." | null
  timeout_status: string
canonical_observation_hash: "sha256:..."
expected_observation_provenance:
  authority_posture: reference_observation | prior_candidate_green |
    source_tail_equivalent | host_library_equivalent |
    fixture_corpus_equivalent | public_scout_locked |
    sealed_probe_locked | other
  source_run_ref: string
  source_artifact_ref: string
  source_artifact_hash: "sha256:..."
  source_environment_ref: string
  canonicalization_profile_ref: string
  canonicalization_profile_hash: "sha256:..."
  observation_capture_time: string | null
  witness_scope: string
  forbidden_promotion: []
```

### Hash Domain

All BRL hashes should be domain-separated. The hash input includes the schema
and object identity before the canonical payload:

```yaml
hash_domain:
  schema_id: string
  object_kind: string
  object_version: string
  hash_algorithm: sha256
  canonicalization_profile_hash: string | null
```

This prevents same-shaped payloads from different schemas from implying the
same semantic object.

### Canonicalization Rule

Canonicalization rules should declare their scope and allowed effect:

```yaml
rule_id: string
surface: stdout | stderr | file_tree | json | xml | process_state |
  timing | path | env
rule_kind: string
scope: string
allowed_effect: string
forbidden_effects: []
justification: string
```

Forbidden by default:

```text
normalizing exit code away;
normalizing protected stderr away;
normalizing protected file-tree mutation away;
normalizing timeout status away;
normalizing process-state leakage away;
collapsing stdout/stderr channels;
rewriting ordering without explicit scoped ordering rules.
```

## Bounded No-Regression Semantics

`BRL-0` must always phrase no-regression claims as bounded:

```text
No observed regression over manifest M, profile C, candidate artifact A, and
protected surfaces S.
```

It must not phrase them as:

```text
No regression in the product.
Product is correct.
Official eval will pass.
```

## Integration Pressure From Revive

The `revive` run showed the need for three replay tiers:

```text
Tier 1:
  impact-cone sentinels after each patch

Tier 2:
  full locked manifest before packaged handoff

Tier 3:
  packaged artifact replay before official eval
```

The first BRL family does not need to implement all tiers in slice A. It should
define manifest fields so later slices can represent them without schema churn.

## Lifecycle And Visibility

Only `locked` or `released` manifests can support later no-regression
certificates. `draft` and `proposed` manifests may validate structurally but
cannot support promotion. `stale`, `superseded`, and `invalid` manifests may be
inspected but cannot support replay promotion.

If implementation workers can see a probe, the manifest may protect it as a
regression surface, but it must not call it a heldout or generalization proof.
