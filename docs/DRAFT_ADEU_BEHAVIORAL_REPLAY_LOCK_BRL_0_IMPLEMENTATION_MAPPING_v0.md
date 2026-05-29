# Draft ADEU Behavioral Replay Lock BRL-0 Implementation Mapping v0

Status: support / implementation mapping record for planned `BRL-0`.

Authority layer: support.

This note maps likely implementation surfaces for the `BRL-0` family. It does
not authorize implementation by itself and does not replace a future
`vNext+<n>` lock, stop-gate decision, or edge assessment.

## Family Intent

`BRL-0` should make no-regression replay deterministic after replay manifests,
probe contracts, canonicalization profiles, and expected observation hashes have
been supplied.

The first practical trigger is a shared-owner patch:

```text
patch_intent
  + touched_owner_surfaces
  + previously_green_sibling_surfaces
  -> required replay manifest or blocker
```

It should answer:

```text
Given this locked replay manifest and candidate observation, did the protected
behavioral surfaces remain identical under the manifest's canonicalization
rules?
```

It must not answer:

```text
Are these the right probes?
Is the product correct?
Should code be patched?
Is official eval safe?
What semantic obligations apply?
```

## Recommended Package Shape

Likely package ownership:

- `packages/adeu_behavioral_replay_lock`

Likely schema mirror:

- `spec/adeu_behavioral_replay_lock/`

Likely package modules:

- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/models.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/vocabulary.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/manifest.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/canonicalization.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/hashing.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/validation.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/replay.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/diff.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/impact_cone.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/certificate.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/invalidation.py`
- `packages/adeu_behavioral_replay_lock/src/adeu_behavioral_replay_lock/export_schema.py`

Later starter locks may narrow this shape.

## Family Slices

| Slice | Implementation posture |
|---|---|
| `BRL-0-A` | Implement first. Manifest, probe contract, canonicalization profile, observation hash, validation report, non-authority guardrail. |
| `BRL-0-B` | Implement later. Replay execution, observation capture, canonical diff, suite-root hash report. |
| `BRL-0-C` | Implement later. Impact-cone sentinel selection, no-regression certificates, staleness reports, HOB/OTB handoff. |

## Shared Vocabulary

The family should use one canonical vocabulary source exported to schema.

Minimum shared enums:

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
- `observation_surface_kind`
- `hash_algorithm`
- `replay_validation_status`
- `replay_execution_status`
- `regression_diff_kind`
- `no_regression_certificate_posture`
- `staleness_reason`
- `authority_posture`

Recommended generic owner taxonomy:

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

No slice should define overlapping strings independently.

## Family Data Flow

```text
replay manifest
  + probe contracts
  + canonicalization profile
  + expected observation hashes
  -> BRL-0-A manifest validation
  -> BRL-0-B replay execution and observation diff
  -> BRL-0-C no-regression certificate and integration handoff
```

## Non-Authority Boundary

`BRL-0` may validate replay manifests, replay specified probes in later slices,
emit diffs, and issue bounded no-regression certificates. It may not decide
semantic truth, generate probes, dispatch workers, patch source, grant product
authority, or select future families.

## Integration Boundaries

HOB integration:

```text
HOB leaves can reference replay-protected sentinel probes.
BRL does not decide HOB inheritance or closure.
```

OTB integration:

```text
OTB transitions can require BRL certificates before allowing a phase transition.
BRL does not decide transition legality by itself.
```

ProgramBench integration:

```text
ProgramBench reconstruction runs can materialize locked probe manifests and
candidate replay reports.
BRL does not decide official score meaning.
```

No integration is selected by this mapping draft.

## Family Acceptance Theme

The family should be considered complete only when it can prove:

```text
source changed
  !=
previously green behavior changed
```

and can deterministically report:

- manifest validation failures;
- missing protected surfaces;
- stale fixture hashes;
- missing protected sibling sentinels for a touched owner;
- missing expected-observation provenance;
- missing execution environment profile;
- raw/protected/ignored surface policy contradictions;
- unsafe raw env/stdin/stdout/stderr material declarations;
- lifecycle states that cannot support promotion;
- changed stdout/stderr/exit/file/process hashes;
- canonicalization vocabulary errors;
- impact-cone sentinel omissions in later slices;
- bounded no-regression certificates in later slices.
