# Assessment vNext+278 Edges

Status: planning-edge assessment for `BRL-0-A`.

Authority layer: planning.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS278_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Manifest Validation Becomes Behavioral Truth

- Risk:
  a structurally valid replay manifest could be mistaken for evidence that a
  candidate still behaves correctly.
- Response:
  keep `BRL-0-A` validation-only. Candidate replay, observation capture, diffs,
  and no-regression certificates are deferred to B/C.

### Edge 2: Expected Hashes Become Fresh Observations

- Risk:
  expected observation hashes could be laundered as new candidate evidence.
- Response:
  require provenance, source hash, authority layer, evidence-boundary posture,
  and clean-first-pass posture for every expected observation hash.

### Edge 3: Canonicalization Hides Real Regressions

- Risk:
  broad normalization could mask protected stderr, exit-code, timeout,
  file-tree, or process-state changes.
- Response:
  make forbidden normalizations first-class and fail closed when a rule affects
  a protected surface outside its declared scope.

### Edge 4: Owner-Surface Taxonomy Becomes Free Text

- Risk:
  arbitrary owner labels could bypass sibling sentinel obligations.
- Response:
  require known owner-surface vocabulary or explicit local-extension posture,
  taxonomy ref, and coverage posture.

### Edge 5: Ignored Surfaces Conflict With Protected Surfaces

- Risk:
  a manifest could claim no-regression while ignoring the very surface it claims
  to protect.
- Response:
  reject protected/ignored contradictions and reject no-regression claims over
  ignored surfaces.

### Edge 6: Mutating Probes Lack Fixture Identity

- Risk:
  a replay manifest could preserve stdout while silently changing files or
  workspace state.
- Response:
  require before/after fixture hashes, mutation policy, workspace write
  allowlist, and cleanup policy for mutating probes.

### Edge 7: Environment Drift Is Under-Specified

- Risk:
  replay hashes may transfer across different runtime, locale, timezone,
  terminal, dependency, or environment substrate without proof.
- Response:
  require execution environment identity and environment hash for replayable
  manifests.

### Edge 8: Sensitive Material Leaks Into Manifests

- Risk:
  raw env/stdin/stdout/stderr material could expose secrets in committed
  fixtures or reports.
- Response:
  require sensitive material, safe rendering, raw storage, and redaction policy
  refs before accepting secret-like material.

### Edge 9: Lifecycle State Overpromotes Draft Or Stale Manifests

- Risk:
  draft, proposed, stale, superseded, or invalid manifests could be used as
  certificate or promotion substrates.
- Response:
  make lifecycle state validation block promotion/certificate posture in
  `BRL-0-A`.

### Edge 10: Hashes Lack Domain Separation

- Risk:
  identical canonical payloads under different object kinds or profiles could
  collide at the evidence layer.
- Response:
  include schema id, object kind, object version, hash algorithm,
  canonicalization profile hash when relevant, and canonical payload in hash
  material.

### Edge 11: A Leaks Into B/C

- Risk:
  the first slice could start replaying probes or selecting sentinels because
  those are the eventual family purpose.
- Response:
  keep `BRL-0-A` limited to manifest/hash/schema validation and guardrails.
  Replay execution, observation capture, diff, impact cone, certificates, and
  integration handoff remain deferred.

### Edge 12: BRL Overrides HOB Or OTB

- Risk:
  a replay manifest could be treated as obligation closure or transition
  authority.
- Response:
  keep BRL non-authoritative relative to HOB inheritance/closure and OTB
  transition legality. Later integration may constrain those lanes, but A does
  not mint authority for them.

## Current Judgment

`BRL-0-A` is worth implementing now because it closes the structural gap exposed
by iterative ProgramBench reconstruction: previously green behavior needs a
deterministic replay manifest and hash contract before later changes can claim
preservation. The first slice should remain deliberately narrow and boring:

```text
manifest + probe contract + canonicalization + expected hash + validation
  yes

execution + observation + diff + certificate
  not in A
```
