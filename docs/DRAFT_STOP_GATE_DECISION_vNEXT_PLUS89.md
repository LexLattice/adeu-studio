# Draft Stop-Gate Decision vNext+89

Status: proposed gate for `V42-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS89.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new ARC task-packet schema validates and exports cleanly;
- one committed local ARC task/session reference packet replays deterministically;
- `task_packet_id` derivation is deterministic over canonical full packet payload
  identity, not only raw initial-state identity;
- the packet carries explicit local mode posture and explicit legal-action envelope;
- toolkit-reported legal-action envelope and ADEU-mirrored legal-action envelope
  normalization remain provenance-carrying and loss-auditable;
- the adapter boundary remains tied to the official local ARC toolkit rather than to a
  repo-local fake environment;
- ARC-side mode and legality constraints are represented as machine-readable admissibility
  surfaces rather than as prose-only metadata;
- `adapter_boundary_policy` remains deontic-only and does not carry hidden
  observation/hypothesis/action semantics;
- the implementation stays inside `packages/adeu_arc_agi` and does not implicitly widen
  into `packages/adeu_arc_solver`;
- the slice ships no scorecard, replay, competition-mode, observation, hypothesis,
  action, or rollout authority;
- Python tests cover:
  - schema/model validation,
  - authoritative/mirrored schema parity,
  - deterministic fixture replay,
  - rejection of non-local or non-authoritative adapter posture,
  - rejection of empty legal-action envelope,
  - rejection of inconsistent toolkit-vs-mirrored legality normalization without
    explicit provenance,
  - rejection of policy-semantic smuggling in `adapter_boundary_policy`,
  - rejection of synthetic prompt-authored task/session packets presented as toolkit
    authority,
  - rejection of first-slice scorecard/replay leakage.

## Do Not Accept If

- the slice invents environment semantics instead of wrapping the official toolkit;
- local-vs-online or legal-action posture remains implicit in prose;
- packet identity quietly means two different things (environment-state identity vs
  full governed packet identity);
- toolkit legality data and mirrored legality data diverge without explicit,
  inspectable provenance;
- boundary policy carries latent solver heuristics or environment interpretation claims;
- canonical task/session packets are prompt-authored reconstructions rather than
  official local toolkit state captures;
- the first slice widens into solver search, observation extraction, or action planning
  while claiming to be only adapter/task-packet work;
- scorecard or replay lineage is introduced as if local adapter baseline already proved
  those seams;
- the package boundary quietly expands into `adeu_arc_solver`, API routes, or web
  surfaces;
- the slice claims model competitiveness or leaderboard readiness from adapter-boundary
  work alone.

## Local Gate

- run `make arc-start-check ARC=89`
