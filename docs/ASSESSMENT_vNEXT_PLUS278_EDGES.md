# Assessment vNext+278 Edges

Status: post-closeout edge assessment for `BRL-0-A`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS278_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Closed Edge Review

### Edge 1: Manifest Validation Becomes Replay Execution

- Closeout state:
  contained.
- Evidence:
  A validates manifest structure, references, hashes, lifecycle posture, and
  guardrails only. No probe execution, process spawning, observation capture, or
  candidate replay APIs shipped.

### Edge 2: Probe IDs Mask Changed Probe Payloads

- Closeout state:
  contained after review hardening.
- Evidence:
  manifests now bind referenced probe ids to `probe_contract_hash` values and
  reject same-id/different-payload substitutions.

### Edge 3: Expected Observation Refs Mask Changed Expected Hashes

- Closeout state:
  contained after review hardening.
- Evidence:
  manifests bind expected observation refs to canonical observation hashes and
  include those child hashes in the suite root.

### Edge 4: Canonicalization Profile Ref Is Under-Bound

- Closeout state:
  contained after review hardening.
- Evidence:
  supplied canonicalization profiles must carry the exact profile hash declared
  by the manifest.

### Edge 5: Suite Root Omits Child Identity

- Closeout state:
  contained after review hardening.
- Evidence:
  suite-root computation includes probe contract hashes and expected
  observation hashes, not only refs.

### Edge 6: Protected Surface Is Silently Ignored

- Closeout state:
  contained.
- Evidence:
  protected/ignored contradictions fail closed, and canonicalization rules may
  not hide protected stderr, exit-code, timeout, file-tree, or process-state
  changes.

### Edge 7: Secret-Like Environment Values Leak Into Replay Material

- Closeout state:
  contained.
- Evidence:
  secret-like env values require safe rendering, raw material storage, and
  redaction policy refs before the manifest can validate.

### Edge 8: Local Owner Labels Bypass Taxonomy

- Closeout state:
  contained.
- Evidence:
  unknown owner labels fail unless declared as local extensions with taxonomy
  refs and coverage posture.

### Edge 9: A Leaks Into B/C

- Closeout state:
  contained.
- Evidence:
  A ships manifest validation and hash contracts only. Replay execution,
  observation capture, regression diffs, suite-root reports, impact-cone
  selection, no-regression certificates, staleness reports, and integration
  handoffs remain deferred.

### Edge 10: Canonical Determinism Is Claimed But Not Tested

- Closeout state:
  contained.
- Evidence:
  focused fixtures cover shuffled input determinism, domain-separated hashes,
  stale manifest hashes, stale suite roots, and canonicalization profile hash
  changes.

## Review Feedback Integrated

- Gemini review:
  secret-like environment marker detection now includes broader credential and
  auth markers.
- Codex review:
  probe contracts are now bound by content hash, not only by `probe_id`.
- Codex review:
  supplied canonicalization profile hashes must match the manifest's locked
  profile hash.

## Residual Edges

- `BRL-0-A` remains a deterministic manifest-validation and hash-schema slice
  only.
- It does not execute probes, capture observations, compare expected and actual
  behavior, produce replay reports, select impact-cone sentinels, issue
  no-regression certificates, invalidate stale locks after patches, or hand off
  readiness to HOB/OTB.
- `BRL-0-B` should consume released A manifests and validation reports while
  preserving the A non-authority posture and adding replay execution,
  observation capture, regression diff, and suite-root hash report surfaces.

## Current Judgment

`BRL-0-A` is closed. The `BRL-0` family remains open for the planned
`BRL-0-B` replay execution, canonical observation capture, regression diff, and
suite-root hash report slice.
