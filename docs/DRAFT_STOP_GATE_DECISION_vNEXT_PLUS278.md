# Draft Stop-Gate Decision vNext+278

Status: proposed gate for `BRL-0-A`.

Authority layer: planning.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS278.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This proposed decision is scoped to `vNext+278` / `BRL-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS278.md`.
- It does not authorize semantic adjudication, domain ontology generation, HOB
  closure recomputation, OTB transition authorization, probe generation, probe
  execution, candidate replay execution, observation capture, candidate
  comparison, impact-cone selection, no-regression certificates, worker
  dispatch, product behavior claims, official-eval authority, ProgramBench
  integration, future-family selection, release authority, or recursive policy
  amendment.

## Accept When

- the implementation stays in a new repo-owned
  `packages/adeu_behavioral_replay_lock` package;
- authoritative schemas and root `spec/` mirrors export for all selected
  `BRL-0-A` record shapes;
- the package defines one shared vocabulary source for A/B/C-ready terms;
- replay manifests validate required fields, lifecycle state, visibility
  posture, protected owner surfaces, owner-surface rows, execution environment
  identity, sensitive material policy, safe rendering policy, raw material
  storage policy, redaction profile, probe contracts, expected observation
  hashes, suite-root hash, and manifest hash;
- probe contracts validate argv/stdin/env/cwd, fixture hashes, protected
  surfaces, ignored surfaces, mutation policy, timeout policy, owner surface,
  and expected observation hash refs;
- canonicalization profiles reject unknown rules and forbidden normalization of
  protected exit code, stderr, timeout status, file-tree mutation, or process
  state;
- expected observation hashes require explicit provenance, source hash,
  authority layer, evidence boundary posture, and clean-first-pass posture;
- stable canonical JSON hashing is domain-separated by schema id, object kind,
  object version, hash algorithm, canonicalization profile hash when relevant,
  and canonical payload;
- shuffled input row order preserves canonical hashes;
- lifecycle states prevent promotion or certificate use when a manifest is
  draft, proposed, stale, superseded, or invalid;
- non-authority guardrails are exported and deny semantic, HOB, OTB, probe,
  replay, observation, comparison, impact-cone, certificate, product,
  official-eval, worker, and future-family authority;
- focused tests cover all required starter fixtures from the lock;
- local verification includes `make check`.

## Do Not Accept If

- the implementation executes probes, spawns candidate commands, captures
  observations, compares candidate behavior, selects impact-cone sentinels, or
  emits no-regression certificates;
- the package silently updates expected hashes or treats expected hash presence
  as observed candidate parity;
- canonicalization can hide protected stderr, exit code, timeout status,
  file-tree mutation, or process-state changes;
- owner-surface labels are free text without local extension posture and
  taxonomy refs;
- a manifest can claim no-regression over ignored surfaces;
- missing expected-observation provenance is accepted;
- a replayable manifest can omit execution environment identity;
- mutating probes can omit before/after fixture hashes or mutation policy;
- sensitive raw material can be represented without safe rendering, storage,
  and redaction policy refs;
- lifecycle state, visibility posture, or authority layer is used to grant
  product, official-eval, or transition authority;
- B/C surfaces leak into A.

## Local Gate

- starter bundle:
  - `make arc-start-check ARC=278`
- implementation PR:
  - `make check`
