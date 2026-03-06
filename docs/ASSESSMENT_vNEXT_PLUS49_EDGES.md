# Assessment vNext+49 Edges (Draft Planning)

This document records the pre-implementation edge set for `vNext+49`.

Status: planning assessment (March 6, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS49_EDGES.md",
  "phase": "pre_implementation_assessment",
  "authoritative": true,
  "authoritative_scope": "v49_prelock_edge_planning",
  "required_in_decision": true,
  "notes": "This document captures the edge set that justifies a v49 V34-A completion slice instead of a direct move to V34-B."
}
```

## Scope

- In scope: `V34-A` completion/hardening only:
  - `X3` downstream signature-result handoff enforcement
  - `X4` signing evidence integration + continuity-guard repair
- Out of scope: `V34-B` through `V34-G`, stop-gate metric-key expansion, stop-gate
  schema-family fork, and `L2` boundary release.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md`
- `docs/ASSESSMENT_vNEXT_PLUS48_EDGES.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS48.md`
- `docs/ASSESSMENT_vNEXT_PLUS48_PRE_V49_EDGES.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_signature.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`
- `packages/adeu_agent_harness/tests/test_taskpack_signature.py`

## Why v49 Exists

`docs/DRAFT_NEXT_ARC_OPTIONS_v8.md` defaulted `vNext+49` to `V34-B`.

That default is not used.

The direct pre-v49 review found that `V34-A` is materially shipped but not yet fully
institutionalized in the real downstream harness path. The remaining gap is narrow enough for
one thin completion slice and important enough that it should not be carried into `V34-B`.

## Pre-Lock Edge Set (v49)

1. Downstream handoff bypass risk: `open_blocking`.
   - Current shape:
     - shared downstream validator exists;
     - downstream runner/verifier/packaging interfaces still appear v47-shaped.
   - Why it matters:
     - `V34-A` can still be treated as preflight-only instead of as a real downstream gate.
   - Required v49 disposition:
     - runner, verifier, and packaging paths must fail closed on missing/unbound handoff.

2. Cross-entrypoint signature-policy drift risk: `open_blocking`.
   - Current shape:
     - policy is centralized in one helper, but not visibly enforced across all downstream
       path boundaries.
   - Why it matters:
     - different entrypoints can drift semantically while the lock text claims one frozen
       contract.
   - Required v49 disposition:
     - shared helper semantics must become the actual downstream acceptance rule.

3. Detached or stale signature-result replay risk: `open_blocking`.
   - Current shape:
     - v48 lock forbids detached/unbound current-result acceptance;
     - current visible harness path does not yet make that operationally obvious.
   - Why it matters:
     - signing can be reduced to a sidecar check rather than a bound execution precondition.
   - Required v49 disposition:
     - only a current orchestrated preflight result may be accepted downstream.
     - "stale" must be defined as exact mismatch against the current authoritative binding
       fields rather than by informal timing language.

4. Taskpack snapshot drift risk after preflight: `open_blocking`.
   - Current shape:
     - downstream paths re-open taskpack files after initial bundle verification steps;
     - the pre-v49 pipeline does not yet declare that hashing and later consumption must bind
       to the same taskpack snapshot.
   - Why it matters:
     - a file swap between check and use can preserve the appearance of a valid preflight
       ticket while changing the actual taskpack bytes later consumed.
   - Required v49 disposition:
     - runner, verifier, and packaging must recompute manifest/bundle hashes from the same
       taskpack bytes they subsequently consume and fail closed on any mismatch.

5. Sidecar-only signing evidence risk: `open_blocking`.
   - Current shape:
     - `v34a_signing_wiring_evidence@1` exists in closeout inputs;
     - evidence writer remains pinned to older verifier-wiring schema expectations.
   - Why it matters:
     - signing is provable in docs, but not clearly part of the canonical harness evidence
       surface.
   - Required v49 disposition:
     - signing-handoff completion evidence must become a first-class closeout requirement.

6. Historical continuity sentinel blind-spot risk: `open`.
   - Current shape:
     - one v48 continuity test compares `metrics_v47_closeout.json` to itself.
   - Why it matters:
     - one asserted continuity guard is weaker than intended.
   - Required v49 disposition:
     - repair the guard and cover it with deterministic tests.
     - self-compare configuration must itself fail closed.

7. Arc-sequencing drift risk: `open_planning_blocking`.
   - Current shape:
     - `V34-B` is the default next path in options v8.
   - Why it matters:
     - moving to matrix-lane expansion before `V34-A` completion would scale an incomplete
       trust-boundary handoff.
   - Required v49 disposition:
     - keep v49 constrained to `V34-A` completion only.

## Guardrail Expectations for v49

- No redefinition of v48 signing semantics.
- No new stop-gate metric keys.
- No stop-gate schema-family fork.
- No `V34-B` matrix-lane release hidden inside the handoff work.
- No evidence-surface weakening in the name of backward compatibility.
- No relaxed acceptance path for detached or stale signing artifacts.
- No acceptance of a taskpack bundle whose current read snapshot differs from the bound
  preflight bundle hash.
- No acceptance of a baseline/current continuity check when both artifact paths are identical.

## Required Closeout Proof for v49

The following should be true at v49 closeout:

- downstream runner path visibly enforces signature-result handoff;
- downstream verifier path visibly enforces signature-result handoff;
- downstream packaging path visibly enforces signature-result handoff;
- downstream runner/verifier/packaging paths visibly fail closed when the current taskpack
  snapshot recomputes a different manifest or bundle hash from the bound signing result;
- canonical closeout surface visibly carries the new handoff completion proof;
- repaired historical v47-to-v48 continuity guard is green;
- repaired historical continuity guard fails closed on self-compare configuration;
- v48-to-v49 stop-gate continuity remains exact-set equal with derived cardinality `80`.

## Coverage Expectations

At minimum, v49 should add or tighten deterministic coverage for:

- runner path missing/unbound signing-result rejection;
- verifier path missing/unbound signing-result rejection;
- packaging path missing/unbound signing-result rejection;
- stale or detached signing-result rejection;
- exact-binding stale rejection where reference time or binding hashes differ;
- current taskpack snapshot mismatch after preflight verification rejection;
- closeout/evidence-path rejection when required handoff evidence is missing;
- repaired historical v47-to-v48 continuity test using distinct artifacts;
- repaired historical continuity test rejects identical baseline/current artifact paths;
- preservation of v48 deterministic env and fail-closed behavior.

## Accepted Non-v49 Deferrals

These remain deferred and should not be smuggled into v49:

1. `V34-B` matrix-lane parity expansion.
2. `V34-C` independent zero-trust policy recomputation.
3. `V34-D` retry-context feeder automation.
4. `V34-E` remote/enclave attestation.
5. `V34-F` standalone integrity self-verification.
6. `V34-G` `remote_enclave` deployment mode.
7. multi-signer/quorum signature governance.
8. crypto-provider portability beyond the frozen deterministic OpenSSL contract.

## Edge Summary (Machine-Checkable)

```json
{
  "schema": "v49_prelock_edge_summary@1",
  "arc": "vNext+49",
  "target_path": "V34-A",
  "blocking_edges": [
    "downstream_handoff_bypass_risk",
    "cross_entrypoint_signature_policy_drift_risk",
    "detached_or_stale_signature_result_replay_risk",
    "taskpack_snapshot_drift_risk",
    "sidecar_only_signing_evidence_risk",
    "arc_sequencing_drift_risk"
  ],
  "non_blocking_edges": [
    "historical_continuity_sentinel_blind_spot_risk"
  ],
  "out_of_scope_deferrals": [
    "V34-B",
    "V34-C",
    "V34-D",
    "V34-E",
    "V34-F",
    "V34-G",
    "multi_signer_quorum",
    "crypto_provider_portability"
  ],
  "recommended_selection": "V34-A_completion_only"
}
```

## Recommendation

1. Draft and review `docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md` as a `V34-A` completion lock.
2. Keep `V34-B` deferred until downstream handoff completion is closed on `main`.
3. Treat evidence integration and the repaired continuity sentinel as real v49 acceptance
   work, not optional cleanup.
