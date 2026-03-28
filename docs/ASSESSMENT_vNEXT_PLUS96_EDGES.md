# Assessment vNext+96 Edges

Status: planning-edge assessment for `V42-G2`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS96_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Post-Hoc Reconstruction Drift

- Risk:
  run records could be serialized after execution from partial traces, while claiming
  full in-band ADEU occupation.
- Response:
  require stage-aware emission evidence refs and monotonic sequence register; reject
  reconstruction posture without typed staged occupancy chain.

### Edge 2: All-At-Once Compatible Dump

- Risk:
  all required refs could be present in one artifact dump without proving staged in-band
  occupation.
- Response:
  reject runs with missing/non-monotonic `emission_sequence_register` or missing
  per-stage emission evidence refs.

### Edge 3: Intermediate Surface Omission

- Risk:
  one or more required `task/observation/hypothesis/action` surfaces could be missing,
  but the run is still treated as valid.
- Response:
  fail closed on any missing or malformed intermediate ref for required surfaces,
  including required `action_proposal_ref` for blocked/deferred posture.

### Edge 4: Rollout/Posture Contradiction

- Risk:
  rollout presence could contradict terminal posture or `rollout_trace_ref` existence.
- Response:
  require explicit `run_terminal_posture` + `rollout_presence_posture` consistency and
  reject contradictions.

### Edge 5: Puzzle-Identity Chain Mismatch

- Risk:
  run artifacts could mix puzzle/bundle/register identities across different puzzle
  chains.
- Response:
  enforce one typed identity chain (`puzzle_input_bundle_id`, `selection_register_id`,
  `puzzle_input_id`, `puzzle_id`) and reject cross-chain drift.

### Edge 6: Config Identity Drift

- Risk:
  run records could be compared as equivalent while using different hidden run configs.
- Response:
  require stable config identity anchors (`agent_profile_ref`, `run_config_ref`,
  `run_config_hash`, optional `prompt_profile_ref`) and reject contradictions.

### Edge 7: Hidden Branching Laundering

- Risk:
  prompt-only hidden branching could alter strategy while emitted typed surfaces hide
  that branch.
- Response:
  require branching-affecting posture to be reflected in typed run surfaces and reject
  hidden-branch equivalence claims.

### Edge 8: Reasoning-Effort Ambiguity

- Risk:
  a decorative single effort label could launder non-comparable run settings.
- Response:
  require explicit requested/observed/source-kind effort fields and reject ambiguous
  effort claims.

### Edge 9: Deterministic Replay Overclaim

- Risk:
  `V42-G2` deterministic replay language could be interpreted as deterministic fresh
  model re-execution.
- Response:
  pin deterministic replay scope to fixed emitted artifacts and fixed in-band evidence;
  explicitly forbid fresh model re-execution determinism claims.

### Edge 10: Premature Harness Widening

- Risk:
  `V42-G2` could silently widen into multi-puzzle harness orchestration or behavior
  synthesis surfaces.
- Response:
  keep this slice bounded to one local attempt over one selected puzzle; defer `G3` and
  `G4` explicitly.

### Edge 11: Narrative Overclaim

- Risk:
  descriptive run summaries could be interpreted as authoritative control-plane evidence.
- Response:
  keep summaries non-authoritative and subordinate to typed identity/occupation fields.

## Current Judgment

- `V42-G2` is the correct next seam after `V42-G1` because the practical missing layer is
  one bounded local reasoning attempt with explicit in-band ADEU ladder occupation.
- Start this slice only with strict fail-closed posture against reconstruction,
  staged-emission ordering gaps, rollout-posture contradictions, and identity/config
  chain drift.
