# Assessment vNext+274 Edges

Status: post-closeout edge assessment for `HOB-0-C` and `HOB-0`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS274_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Closed Edge Review

### Edge 1: Delta Attribution Becomes Product Truth

- Closeout state:
  contained.
- Evidence:
  delta ledgers require `pressure_attribution_only_not_product_truth`, and
  attribution rows remain evidence-boundary typed pressure over numbered nodes.

### Edge 2: Score Movement Becomes Macro Closure

- Closeout state:
  contained.
- Evidence:
  macro closure attribution requires released closure evidence and local
  locked-probe evidence posture. Official-like pressure cannot close a macro.

### Edge 3: Post-Eval Pressure Is Laundered As Clean Evidence

- Closeout state:
  contained.
- Evidence:
  attribution and handoff rows require explicit evidence boundary posture;
  disallowed clean-first-pass laundering is rejected.

### Edge 4: Stale Ledger Reuse After Catalog Changes

- Closeout state:
  contained after review hardening.
- Evidence:
  stale-ledger invalidation reports bind prior/current catalog
  id/version/hash. Changed hashes require invalidated refs and reason rows;
  unchanged hashes reject contradictory invalidation refs.

### Edge 5: Integration Handoff Becomes Future-Family Selection

- Closeout state:
  contained after review hardening.
- Evidence:
  handoff rows are pressure-only and require explicit no-authority postures for
  ProgramBench integration, semantic compiler integration, probe execution,
  implementation, and future-family selection. Mixed pressure kinds in one
  handoff are rejected.

### Edge 6: C Reopens A Or B Decisions

- Closeout state:
  contained.
- Evidence:
  C consumes released A/B substrate and validates catalog continuity. It does
  not decide activation applicability and does not recompute closure outside
  released B closure evidence.

### Edge 7: Family Closeout Hides Unresolved Blockers

- Closeout state:
  contained after review hardening.
- Evidence:
  closed family alignment requires exact `HOB-0-A`, `HOB-0-B`, and `HOB-0-C`
  slice refs and rejects residual deferred refs or blockers. Open-with-deferred
  family posture rejects active blockers.

### Edge 8: Canonical Determinism Is Claimed But Not Tested

- Closeout state:
  contained.
- Evidence:
  focused C fixtures cover deterministic ordering and canonical hashes for
  delta attribution rows.

### Edge 9: C Emits Execution Or Implementation Authority

- Closeout state:
  contained.
- Evidence:
  C emits only delta attribution, stale-ledger invalidation, pressure-only
  handoff, and family closeout alignment shapes. Probe execution, worker
  dispatch, implementation authority, product truth, ProgramBench integration,
  and future-family selection remain absent.

## Review Feedback Integrated

- Codex review:
  unchanged prior/current catalog hashes now reject invalidated ledger/probe
  plan refs and reason rows.
- Gemini review:
  all handoff pressure rows must match the top-level handoff pressure kind.
- Gemini review:
  `hob_0_family_open_with_deferred_refs` requires deferred refs and rejects
  active blockers.

## Residual Edges

- HOB remains a deterministic broker only. It does not decide semantic
  applicability, generate ontology catalogs, run probes, dispatch workers,
  patch product code, authorize product behavior, integrate ProgramBench, or
  select future families.
- C handoff rows are pressure-only. They may inform later families, but they do
  not select or authorize those families.
- Delta attribution remains evidence-bound pressure. It is not clean product
  truth, benchmark truth, model performance, or macro closure unless released
  closure evidence supports the narrower closure posture.

## Current Judgment

`HOB-0-C` is closed. The full `HOB-0` family is closed as deterministic
hierarchical obligation brokerage:

```text
HOB-0-A:
  catalog + activation + inherited ledger + validation/frontier

HOB-0-B:
  closure + frontier priority + plan-only probe matrix + bounded batches

HOB-0-C:
  delta pressure attribution + stale-ledger invalidation + pressure-only
  handoff + family closeout alignment
```
