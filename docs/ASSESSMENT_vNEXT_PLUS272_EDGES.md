# Assessment vNext+272 Edges

Status: post-closeout edge assessment for `HOB-0-A`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS272_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Closed Edge Review

### Edge 1: Broker Becomes Semantic Judge

- Closeout result:
  contained.
- Evidence:
  activation assessment rows preserve model/upstream semantic judgment posture;
  the broker validates catalog refs, vocabulary, warrants, and row shape, but
  does not compute applicability.

### Edge 2: A Accidentally Implements Closure Aggregation

- Closeout result:
  contained.
- Evidence:
  A emits traversal diagnostics and frontier rows only. Full closure reports,
  probe matrix plans, implementation batch contracts, operationalization
  reports, and delta attribution remain absent.

### Edge 3: Missing Children Silently Disappear

- Closeout result:
  contained.
- Evidence:
  active-parent fixtures deterministically import catalog children, and missing
  inherited child rows fail closed in traversal validation.

### Edge 4: Irrelevance Becomes A Prose Escape Hatch

- Closeout result:
  contained.
- Evidence:
  proof-sensitive statuses require proof rows discriminated by proof kind/type
  with protected surfaces, warrant refs, proof text, and evidence refs;
  proof-text alone is not accepted.

### Edge 5: Scoped Deferral Masquerades As Irrelevance

- Closeout result:
  contained.
- Evidence:
  scoped deferrals remain distinct from irrelevance proof and block false
  gold-ready claims.

### Edge 6: `not_inherited` And `optional_observed` Become Escape Hatches

- Closeout result:
  contained.
- Evidence:
  `not_inherited` requires catalog/default or inactive-parent justification,
  and optional observation cannot silently satisfy required inherited closure.

### Edge 7: Stale Catalog Ledgers Reused After Tree Changes

- Closeout result:
  contained.
- Evidence:
  catalog, activation, inherited ledger, traversal validation, and guardrail
  records bind catalog id/version/hash; stale catalog reuse fails validation.

### Edge 8: Frontier Output Becomes Implementation Authority

- Closeout result:
  contained.
- Evidence:
  frontier rows name required next descent actions and diagnostics only; the
  guardrail denies probe execution, implementation, worker dispatch, product
  authority, and future-family selection.

### Edge 9: Probe Matrices Sneak Into A

- Closeout result:
  contained.
- Evidence:
  no probe matrix, probe authority, or observation/execution records shipped in
  A; probe-matrix planning remains deferred to `HOB-0-B`.

### Edge 10: Canonical Determinism Is Claimed But Not Tested

- Closeout result:
  contained.
- Evidence:
  shuffled input fixtures preserve canonical output order and validation hash.

## Review Feedback Integrated

- Codex review:
  structured proof handling and validation diagnostics remained fail-closed
  while preserving the A/B boundary.
- Gemini review:
  schema and validation wording was tightened where useful; redundant
  broadening suggestions were not applied when they would have moved B closure
  aggregation into A.

## Residual Edges

- Full subtree closure/readiness reporting remains deferred to `HOB-0-B`.
- Probe-matrix planning remains deferred to `HOB-0-B`.
- Implementation batch contracts remain deferred to `HOB-0-B`.
- Delta attribution and stale-ledger invalidation remain deferred to
  `HOB-0-C`.
- The broker still does not decide semantic applicability, mutate catalogs,
  execute probes, dispatch workers, patch product code, authorize product
  behavior, or select future families.

## Current Judgment

`HOB-0-A` is closed on `main`. The implementation proves the deterministic
institutional move:

```text
model/upstream activation says parent applies
  -> broker imports inherited children
  -> broker requires admissible status/proof rows
  -> broker rejects false closure/readiness claims
  -> broker emits next frontier rows
```

The family remains open for `HOB-0-B`.
