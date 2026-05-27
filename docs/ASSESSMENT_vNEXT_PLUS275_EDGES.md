# Assessment vNext+275 Edges

Status: post-closeout edge assessment for `OTB-0-A`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS275_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Closed Edge Review

### Edge 1: Artifact Presence Becomes An Implied Transition Claim

- Closeout state:
  contained.
- Evidence:
  `repo_phase_transition_claim@1` is a first-class required input. Transition
  identity validation checks circuit, phase, transition id, and transition kind.

### Edge 2: Valid Transition Becomes Action Authority

- Closeout state:
  contained.
- Evidence:
  valid reports use `valid_for_broker_frontier`; legal frontier rows carry
  `broker_validation_only_not_execution_authority`.

### Edge 3: Bridge Consistency Collapses Into Bridge Completeness

- Closeout state:
  contained.
- Evidence:
  validation reports expose separate `bridge_consistency_status` and
  `bridge_completeness_status`; consistent but incomplete bridges remain
  blocked.

### Edge 4: Artifact Identity Is Under-Specified

- Closeout state:
  contained after review hardening.
- Evidence:
  required objects compare file, canonical payload, semantic object,
  evidence-boundary, obligation-set, catalog, and bridge hashes, plus authority
  layer, source phase, identity claim, and freshness basis.

### Edge 5: Evidence Contamination Is Only Checked Directly

- Closeout state:
  contained after review hardening.
- Evidence:
  evidence rows carry `derived_from_evidence_refs`; forbidden evidence is
  checked with an iterative ancestry walk, including required-artifact evidence
  refs even when the claim omits the artifact ref.

### Edge 6: Duplicate Rows Silently Overwrite Evidence

- Closeout state:
  contained after review hardening.
- Evidence:
  duplicate artifact, evidence, and obligation refs emit conflict diagnostics
  instead of silently overwriting earlier rows.

### Edge 7: Obligation Transfers Under-Cover The Bridge Contract

- Closeout state:
  contained after review hardening.
- Evidence:
  all bridge-declared created, preserved, discharged, and blocked/deferred
  obligations are required when silent drops are forbidden. Obligation phase
  mismatches fail closed.

### Edge 8: Blocked Obligations Lack Warrant

- Closeout state:
  contained after review hardening.
- Evidence:
  blocked obligations require `blocker_ref`, just as discharged/deferred rows
  require their own warrant refs.

### Edge 9: Useful But Overstrong Artifacts Are Only Blocked

- Closeout state:
  contained.
- Evidence:
  unsupported readiness claims emit `posture_downgrade_required` frontiers with
  requested and maximum-supported postures.

### Edge 10: OTB Becomes A Semantic Judge

- Closeout state:
  contained.
- Evidence:
  A validates rows, hashes, declared transfer posture, and evidence boundaries.
  It does not decide domain meaning, phase content quality, product correctness,
  or official readiness.

### Edge 11: A Leaks Into B/C

- Closeout state:
  contained.
- Evidence:
  A ships validation reports, legal frontiers, and guardrails only. Closure
  aggregation, gate plans, worker baton contracts, evidence posture plans,
  operationalization reports, delta attribution, stale-object invalidation, and
  integration handoff remain deferred.

### Edge 12: Canonical Determinism Is Claimed But Not Tested

- Closeout state:
  contained.
- Evidence:
  focused fixtures cover stable ordering and canonical hashes under shuffled
  input.

## Review Feedback Integrated

- Codex review:
  transition kind is now compared against the catalog transition row.
- Codex review:
  evidence attached to required artifacts is validated even when omitted from
  claim artifact refs.
- Codex review:
  all contract-declared obligation transfer families are required.
- Gemini review:
  transitive evidence validation uses iterative DFS rather than recursion.
- Gemini review:
  duplicate artifact, evidence, and obligation refs fail closed.
- Gemini review:
  obligation source/target phases must match the bridge transition.
- Gemini review:
  blocked obligations require `blocker_ref`.

## Residual Edges

- `OTB-0-A` remains a deterministic transition validator only.
- It does not compute transition closure/readiness summaries, gate execution
  plans, worker baton contracts, evidence posture plans, operationalization
  reports, delta attribution, stale-object invalidation, or integration
  handoffs.
- `OTB-0-B` should consume released A records and preserve the A non-authority
  posture while adding plan-only closure and operationalization surfaces.

## Current Judgment

`OTB-0-A` is closed. The `OTB-0` family remains open for the planned
`OTB-0-B` closure, gate planning, baton contract, evidence posture, and
operationalization slice.
