# Draft Stop-Gate Decision vNext+96

Status: proposed gate for `V42-G2`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS96.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- one canonical `adeu_arc_reasoning_run_record@1` is released with authoritative/mirror
  schema parity;
- one bounded entrypoint consumes a released `adeu_arc_puzzle_input_bundle@1` plus one
  selected puzzle and emits in-band `V42-A`/`V42-B`/`V42-C` ladder occupancy;
- deterministic replay scope is explicitly limited to deterministic derivation/validation
  over fixed emitted artifacts and fixed in-band evidence;
- run identity chain is typed and stable across run/puzzle/environment/session/
  competition refs;
- run configuration identity is typed and stable (`agent_profile_ref`, `run_config_ref`,
  `run_config_hash`, optional `prompt_profile_ref`);
- run execution lifecycle, terminal posture, and rollout-presence posture are explicit
  and machine-checkable;
- stage-aware emission evidence refs are present per occupied surface plus one monotonic
  `emission_sequence_register`;
- blocked/deferred action posture is admissible with required `action_proposal_ref`
  (without forced committed rollout);
- post-hoc artifact reconstruction posture is rejected fail closed;
- all-at-once compatible dump posture (all refs present but no staged monotonic emission
  evidence) is rejected fail closed;
- prompt-only hidden branching is not treated as equivalent to explicit typed ladder
  occupation and branching visibility surfaces are required when branching affects
  posture;
- fixture ladder is committed under `apps/api/fixtures/arc_agi/vnext_plus96/` with one
  accepted run record and rejection fixtures for reconstruction, surface omissions,
  staged-emission ordering gaps, identity/config mismatch, hidden-branching laundering,
  and rollout-presence contradiction;
- Python tests cover schema validation, schema parity, deterministic accepted replay, and
  required rejection paths.

## Do Not Accept If

- `V42-G2` redefines released semantics from `V42-A`..`V42-F` or `V42-G1`;
- implementation widens into `V42-G3` three-puzzle orchestration or `V42-G4`
  behavior-evidence synthesis;
- intermediate surfaces are backfilled after-the-fact rather than emitted in-band;
- deterministic replay language is overclaimed as deterministic fresh model
  re-execution;
- staged per-surface emission evidence is missing or sequence ordering is non-monotonic;
- rollout presence/absence is contradictory with terminal posture and `rollout_trace_ref`;
- summary or narrative fields override typed run identity or occupation surfaces;
- benchmark tournament execution, API/web operator routes, or generalized multi-agent
  orchestration are introduced.

## Local Gate

- run `make arc-start-check ARC=96` for starter-bundle validation;
- for implementation PRs that touch Python/runtime surfaces, run `make check` (or state
  skipped scopes explicitly when running a narrower subset).
