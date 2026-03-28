# Locked Continuation vNext+89

Status: `V42-A` implementation contract.

## V89 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v42a_arc_local_adapter_contract@1",
  "target_arc": "vNext+89",
  "target_path": "V42-A",
  "target_scope": "local_arc_toolkit_adapter_and_task_session_freeze_baseline",
  "task_packet_schema": "adeu_arc_task_packet@1",
  "implementation_package": "adeu_arc_agi",
  "official_environment_authority": "official_arc_toolkit",
  "official_local_adapter_required": true,
  "local_first_required": true,
  "adapter_deontic_boundary_required": true,
  "task_packet_id_derivation": "canonical_full_packet_payload_hash",
  "toolkit_legal_action_envelope_provenance_required": true,
  "boundary_policy_semantics_limited_to_deontic_admissibility": true,
  "synthetic_prompt_packet_forbidden": true,
  "competition_mode_deferred": true,
  "scorecard_and_replay_authority_deferred": true,
  "observation_hypothesis_action_artifacts_deferred": true,
  "solver_search_deferred": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "decomposition_doc": "docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v24.md"
}
```

## Slice

- Arc label: `vNext+89`
- Family label: `V42-A`
- Scope label: local ARC toolkit adapter and task/session freeze baseline

## Objective

Introduce the first concrete ARC participation slice by activating only the local
environment-adapter and task/session freeze lane and releasing one canonical
`adeu_arc_task_packet@1` artifact over the official local ARC toolkit boundary before any
observation-frame, hypothesis, action-proposal, rollout, scorecard, competition-mode, or
workbench surface is released.

This slice establishes the first ADEU ARC substrate for:

- canonical `adeu_arc_task_packet@1`;
- one authoritative local adapter posture over the official ARC toolkit;
- exact task/game/session freeze over one bounded local ARC world;
- explicit mode-policy and legal-action envelope as first-class admissibility surfaces;
- deterministic initial-state identity and replay posture;
- committed local reference fixtures proving adapter-boundary honesty without solver
  widening.

This slice remains deliberately prior to:

- observed ARC frame extraction;
- hypothesis-state release;
- action proposal or rollout trace release;
- local benchmark runner or model comparison surface;
- scorecard or replay authority;
- competition-mode online submission;
- API or web operator surfaces;
- generalized multi-agent or multi-benchmark orchestration.

Its job is to prove that ADEU can wrap the official local ARC toolkit honestly before any
later slice tries to reason or act within that world.

## Frozen Implementation Decisions

1. Active package strategy:
   - activate only `packages/adeu_arc_agi` in `vNext+89`;
   - `packages/adeu_arc_solver` remains deferred and may not be implicitly selected by
     helper naming, fixture structure, or prose-only promises.
2. Environment-authority strategy:
   - the official local ARC toolkit remains authoritative for environment state,
     task/game/session identity, and legal external interaction;
   - `vNext+89` may wrap that authority but may not replace it with repo-local fake
     environment semantics or free-form prompt interpretation;
   - adapter-boundary policy must remain explicit and machine-readable.
3. Task-packet strategy:
   - `adeu_arc_task_packet@1` is the only newly released artifact family in this slice;
   - authoritative JSON schema must live under `packages/adeu_arc_agi/schema/`;
   - mirrored export must live under `spec/`;
   - mirrored export must match the authoritative schema byte-for-byte after canonical
     export;
   - `task_packet_id` must be derived from canonical full packet payload identity, not
     only from raw initial environment state identity;
   - the task packet must carry exact local boundary identity for:
     - `environment_authority`
     - `adapter`
     - `mode_posture`
     - `game_ref`
     - `session_ref`
     - `initial_state_ref`
     - `initial_state_hash`
     - `toolkit_legal_action_envelope`
     - `legal_action_envelope`
     - `legal_action_envelope_provenance`
     - `adapter_boundary_policy`
   - if `legal_action_envelope` is a normalized ADEU mirror of toolkit data, the packet
     must carry provenance that makes normalization inspectable and loss-auditable.
4. Deontic-boundary strategy:
   - ARC-side mode restrictions and legal action envelope must be represented as
     first-class admissibility surfaces, not prose-only metadata;
   - the slice must distinguish:
     - allowed local interaction;
     - deferred online or competition interaction;
     - forbidden environment-semantic redefinition in this slice.
   - `adapter_boundary_policy` may constrain admissibility and authority posture only;
     it may not smuggle observation hypotheses, latent solver heuristics, or
     environment-interpretation claims.
5. Local-first strategy:
   - `vNext+89` must target local/offline posture only;
   - competition-mode, scorecard, and replay authority remain deferred;
   - no leaderboard or competitiveness claim may be minted from the first slice.
6. Path decomposition strategy:
   - `vNext+89` is the first concrete `V42-A` arc;
   - any widening into observation, hypothesis, action, rollout, benchmarking, or online
     scorecard integration remains available only for later concrete arcs outside this
     baseline.

## Required Deliverables

1. New typed ARC task/session freeze surface:
   - extend `packages/adeu_arc_agi` with deterministic helpers that materialize
     canonical `adeu_arc_task_packet@1` over the official local ARC toolkit boundary;
   - export schema helpers needed for authoritative and mirrored JSON-schema output;
   - keep solver search, scorecard, replay, API/web, and competition-mode surfaces out
     of scope.
2. Canonical task/session packet artifact:
   - `adeu_arc_task_packet@1`
3. Deterministic local adapter entrypoints that:
   - consume authoritative local ARC toolkit task/game/session state;
   - materialize one canonical `adeu_arc_task_packet@1`;
   - reject synthetic prompt-authored task/session packets presented as toolkit
     authority;
   - fail closed when environment authority, adapter lineage, mode posture, legal-action
     envelope, or initial-state identity is invalid.
4. Top-level schema anchors for `adeu_arc_task_packet@1`:
   - `schema`
   - `task_packet_id`
   - `environment_authority`
   - `adapter`
   - `mode_posture`
   - `game_ref`
   - `session_ref`
   - `initial_state_ref`
   - `initial_state_hash`
   - `toolkit_legal_action_envelope`
   - `legal_action_envelope`
   - `legal_action_envelope_provenance`
   - `adapter_boundary_policy`
5. Deterministic task-packet laws that fail closed on at least:
   - any non-official or non-local environment authority posture;
   - any missing or empty legal-action envelope;
   - any unaccounted or non-loss-auditable normalization between
     `toolkit_legal_action_envelope` and `legal_action_envelope`;
   - any adapter-boundary policy that leaves local-vs-online posture implicit;
   - any adapter-boundary policy that carries non-deontic observation/hypothesis/action
     semantics;
   - any `task_packet_id` derivation that ignores packet-level boundary identity and
     depends only on initial-state fields;
   - any mismatch between frozen initial-state identity and canonical packet hash;
   - any synthetic prompt-authored task/session packet represented as if sourced from
     the official local toolkit;
   - any attempt to carry scorecard, replay, competition-mode, observation, hypothesis,
     action, or rollout authority in the first slice;
   - any attempt to replace toolkit-exposed action legality with repo-local invented
     semantics.
6. Committed reference fixtures:
   - one accepted reference fixture ladder under
     `apps/api/fixtures/arc_agi/vnext_plus89/` covering:
     - one canonical local task/session packet
     - one rejected non-local or non-authoritative adapter posture
     - one rejected packet with official/local authority posture but empty or inconsistent
       legal-action envelope carry-through
   - the accepted fixture ladder must prove:
     - deterministic packet replay;
     - explicit local mode posture;
     - explicit legal-action envelope carry-through;
     - explicit toolkit-vs-mirrored envelope normalization provenance;
     - no scorecard or replay authority leakage.
7. Python tests covering:
   - schema/model validation for `adeu_arc_task_packet@1`;
   - authoritative/mirrored schema export parity;
   - deterministic packet replay from the accepted fixture ladder;
   - rejection of non-local or non-authoritative adapter posture;
   - rejection of empty legal-action envelope;
   - rejection of inconsistent toolkit-vs-mirrored envelope normalization without
     explicit provenance;
   - rejection of policy-semantic smuggling in `adapter_boundary_policy`;
   - rejection of synthetic prompt-authored task/session packets as toolkit authority;
   - rejection of scorecard/replay/competition-mode leakage in the first slice.

## Hard Constraints

- `vNext+89` may not reopen or redefine the released `V41` practical-analysis
  contracts.
- `vNext+89` may not ship:
  - observation-frame extraction,
  - hypothesis-state release,
  - action proposal or rollout trace release,
  - local benchmark runner or model tournament surfaces,
  - scorecard or replay authority,
  - competition-mode online submission,
  - API or web operator routes,
  - generalized multi-agent or multi-benchmark orchestration,
  - leaderboard or challenge-readiness claims.
- `vNext+89` may not treat metadata-only prose as sufficient for ARC-side deontic
  boundaries.
- `vNext+89` may not derive `task_packet_id` from initial-state identity alone while
  ignoring adapter/mode/legal-envelope boundary identity.
- `vNext+89` may not hide normalization loss between toolkit legality data and mirrored
  ADEU legality data.
- `vNext+89` may not smuggle solver or interpretation semantics inside
  `adapter_boundary_policy`.
- `vNext+89` may not replace the official local ARC toolkit with repo-local substitute
  environment semantics.
- `vNext+89` may not emit canonical packets from prompt-only synthetic task/session
  reconstruction presented as toolkit authority.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- the first ARC adapter seam, task/session packet grammar, schema export, fixtures, and
  fail-closed local-boundary rules are one bounded family-start surface;
- splitting them would create artificial staging inside the same narrow substrate proof
  without reducing semantic risk.
