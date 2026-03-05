# Assessment vNext+48 Pre-v49 Edges

Status: targeted planning assessment (March 5, 2026 UTC).

Purpose:

- assess `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md`
  together;
- decide whether the repo is actually ready to move from `V34-A` to `V34-B`;
- separate what v48 fully closed from what is still only partially integrated.

## Short Answer

`V34-A` looks closed at the contract/verifier/test-helper level, but not yet fully closed at
the end-to-end harness-pipeline level.

I would not move directly to `V34-B` as currently sequenced in `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
without one more thin `V34-A` completion slice.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md`
- `docs/ASSESSMENT_vNEXT_PLUS48_EDGES.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS48.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_signature.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`
- `packages/adeu_agent_harness/tests/test_taskpack_signature.py`
- `artifacts/agent_harness/v48/evidence_inputs/v34a_signing_wiring_evidence_v48.json`

## What v48 Clearly Closed

- deterministic pre-flight signature verification exists;
- single-signature-only envelope posture is enforced;
- signer key id plus algorithm binding is enforced;
- explicit verification reference time is enforced;
- deterministic `signature_verification_result@1` emission exists;
- a reusable downstream validation helper exists;
- fail-closed `AHK48xx` diagnostics and guard tests exist.

That is real progress. The thin-slice did not fail. It just appears narrower in implementation
than the current lock and closeout prose imply.

## Open Edges Before `V34-B`

### 1. P1: Downstream handoff is specified more strongly than it is wired

`docs/DRAFT_NEXT_ARC_OPTIONS_v8.md` says `V34-A` should emit
`signature_verification_result@1` for downstream runner/verifier/packaging consumption.

`docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md` strengthens that into a frozen topology:

- downstream runner/verifier/packaging lanes consume `signature_verification_result@1`;
- preflight is required before runner/verifier/packaging;
- user-supplied verification-result paths are forbidden;
- exact binding checks are required before execution.

The repo does contain the downstream validator:

- `validate_signature_verification_result_for_downstream(...)` in
  `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_signature.py`

But the released harness entrypoints still look v47-shaped:

- `run_taskpack.py` does not accept or validate a signature-verification-result input;
- `verify_taskpack_run.py` does not accept or validate a signature-verification-result input;
- `package_ux.py` still packages from verified-result/evidence/provenance plus runtime and
  metric continuity inputs only;
- `write_closeout_evidence.py` still consumes the older verifier-wiring input model only.

Conceptually:

```text
lock intent
verify_taskpack_signature
    -> run_taskpack
    -> verify_taskpack_run
    -> write_closeout_evidence
    -> package_ux

current visible wiring
verify_taskpack_signature (standalone + test-covered helper)

run_taskpack
    -> verify_taskpack_run
    -> write_closeout_evidence
    -> package_ux
```

Assessment:

- this is the main open edge;
- it is not a failure of the verifier contract itself;
- it is a failure to finish the promised in-process handoff topology.

Why this matters for `V34-B`:

- `V34-B` scales packaging/runtime parity across more lanes;
- if the trust-boundary handoff is not first centralized, `V34-B` risks multiplying an
  incomplete preflight contract across more surfaces.

### 2. P1: v48 signing evidence is docs-side, not canonical harness evidence

`docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md` requires a
`v34a_signing_wiring_evidence@1` closeout block.

That block exists in:

- `artifacts/agent_harness/v48/evidence_inputs/v34a_signing_wiring_evidence_v48.json`

But the live harness evidence lane is still pinned to the older verifier wiring schema:

- `write_closeout_evidence.py` allowlists `v33c_verifier_wiring_evidence@1`;
- its CLI requires `--verifier-wiring-evidence` using that older schema;
- `package_ux.py` likewise still consumes the older evidence bundle/provenance shape.

Assessment:

- the v48 signing wiring evidence exists as closeout proof;
- it does not yet appear to be part of the harness's canonical evidence bundle contract;
- this leaves signing as a sidecar closeout claim instead of a first-class packaged evidence
  surface.

Why this matters for `V34-B`:

- matrix-lane parity is much easier to reason about if every lane is carrying the same
  canonical trust evidence shape;
- otherwise parity may be checked on a surface that still omits the new signing authority lane.

### 3. P2: one stop-gate continuity test is still too weak for the claim it supports

`packages/adeu_agent_harness/tests/test_taskpack_signature.py` includes
`test_stop_gate_metric_keyset_exact_equal_v47`, but it compares
`metrics_v47_closeout.json` to itself.

Assessment:

- this does not invalidate the v48 closeout by itself;
- it does mean one local guard is a sentinel instead of a real v47-to-v48 continuity check;
- that is easy to fix and should be fixed before using v48 as a stronger platform for later
  slices.

### 4. P2: options v8 overstates how much of "trust-anchor distribution" v48 actually landed

`docs/DRAFT_NEXT_ARC_OPTIONS_v8.md` names `V34-A` as
`TaskPack Signing + Trust-Anchor Distribution`.

What is clearly present in code is:

- registry schema/validation;
- signature envelope schema/validation;
- standalone pre-flight verification.

What is not yet clearly present in the broader harness is:

- a pipeline-owned distribution/handoff surface that carries trust artifacts through later
  stages;
- canonical packaging/evidence integration for the new signing lane.

Assessment:

- this is better framed as a planning-clarity gap than a correctness bug;
- before `V34-E` or portability-heavy work, the repo should clarify whether "distribution"
  means "schema exists as an external artifact" or "the harness now owns carriage of that
  artifact through its pipeline."

## Options v8 Enhancements

### 1. Add an explicit dependency edge before `V34-B`

The current dependency list only states:

- `V34-E` depends on `V34-A`;
- `V34-G` preserves `V33-D` mode invariants.

It should also state something close to:

- `V34-B` depends on `V34-A` downstream handoff stabilization, not only on generic path
  completion.

That dependency is not just conceptual. It is operational. Matrix-lane expansion should not
precede central enforcement of the v48 signing handoff.

### 2. Clarify the meaning of "distribution" inside `V34-A`

`V34-A` should explicitly distinguish between:

- registry/envelope schema authority; and
- harness-owned transport/packaging/evidence carriage of those authority artifacts.

Right now the first part is implemented. The second part is not clearly part of the released
pipeline.

### 3. Re-evaluate `V34-F` only after the handoff story is finished

The portability-first note in options v8 is sensible, but `V34-F` becomes cleaner only after
the repo has a fully explicit answer to:

- what exactly is being distributed;
- where trust evidence lives in packaged outputs;
- how a downstream verifier proves it is consuming the current preflight result rather than a
  sidecar artifact.

So the immediate next move is not "pull `V34-F` earlier now". The immediate next move is
"finish the `V34-A` handoff story first, then reconsider `V34-B` versus `V34-F`."

## Recommendation

### Recommended sequencing revision

1. `vNext+49`: use a thin `V34-A` completion/hardening lock instead of moving directly to
   `V34-B`.
2. `vNext+50`: move to `V34-B` only after the v48 trust-boundary handoff is visibly enforced.
3. Re-evaluate whether `V34-F` should move earlier once the signing/evidence/distribution
   surface is actually pipeline-owned.

### Recommended contents of the thin completion slice

- wire `signature_verification_result@1` into the orchestrated runner/verifier/packaging path;
- forbid user-supplied detached signing-result inputs at downstream entrypoints in the actual
  pipeline, not only in helper semantics;
- update evidence writer and packaging contracts if signing wiring is meant to be first-class
  closeout/package evidence;
- fix the weak v47-to-v48 stop-gate continuity test;
- refresh the v48 closeout assessment language so it does not overclaim pipeline adoption.

## Bottom Line

The repo does not look blocked on v48 cryptography or schema design. It looks blocked on
finishing v48 as a real harness-wide handoff.

That is exactly the kind of thing worth addressing before `V34-B`, because `V34-B` expands
surfaces and fixtures. It should not be the arc that first reveals that `V34-A` was only
partially wired.
