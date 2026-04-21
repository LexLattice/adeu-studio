# Assessment vNext+184 Edges

Status: post-closeout edge assessment for `V66-C` (April 21, 2026 UTC).

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS184_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Compile Report Could Quietly Become Source Authority

- Risk:
  the advisory compile report could be overread as if it changes source truth,
  migration posture, semantic-diff authority, or lock authority by itself.
- Response:
  keep compile-report posture advisory and fail-closed.
  - compile report is not source authority by itself
  - compile report is not transition law by itself
  - compile report is not migration or semantic-diff authority by itself
- Closeout Evidence:
  shipped builders/tests preserve advisory-only reduction and reject authority
  overread outside the selected `V66-A` / `V66-B` lineage.

### Edge 2: Prose-Boundary Notices Could Quietly Infer Policy From Prose

- Risk:
  warning surfaces could start treating normative-sounding prose as if it were
  compiled policy.
- Response:
  keep prose-boundary notices evidence-bound and explicit.
  - only compiler-recognized authority blocks compile
  - examples, quotes, HTML comments, and indented-code contexts do not become
    policy by tone
- Closeout Evidence:
  shipped notice detection/tests strip non-authoritative contexts and keep
  notice rows advisory-only and evidence-bound.

### Edge 3: Generated Reader Views Could Re-Enter As Authority Inputs

- Risk:
  `V66-C` could accidentally treat generated reader projections as if they were
  governing source or transition-law evidence.
- Response:
  keep generated projections shaping-only and non-authoritative.
  - generated projections remain excluded from governed source discovery
  - generated projections remain non-authoritative even when they render
    authority text
- Closeout Evidence:
  shipped compile-report derivation/tests preserve generated-reader input as
  shaping-only and not as source authority.

### Edge 4: Semantic Diff Could Quietly Become Promotion Law

- Risk:
  drift visibility could be overread as if it authorizes markdown transition or
  source migration by itself.
- Response:
  keep semantic diff review-only and shaping-only.
  - semantic diff records visibility only
  - semantic diff is not authority by itself
- Closeout Evidence:
  shipped advisory reduction/tests preserve semantic-diff input as shaping-only
  and non-authoritative.

### Edge 5: `V66-C` Could Widen Beyond The Same Governed Source Set

- Risk:
  adoption hardening could start rediscovering or classifying new docs outside
  the shipped `V66-A` / `V66-B` lineage.
- Response:
  keep the carried source set exact and fail-closed.
  - same shipped governed ANM source set only
  - no fresh source-set widening by default
- Closeout Evidence:
  shipped builders/tests remain downstream of exact shipped `V66-A` /
  `V66-B` basis only and reject lineage mismatch.

### Edge 6: Advisory Outcomes Could Quietly Become Supersession Pressure

- Risk:
  advisory outcomes such as later transition candidates could be overread as if
  they were active transition law.
- Response:
  keep candidate outcomes non-entitling and non-escalating.
  - no advisory outcome supersedes markdown by itself
  - explicit shipped lock-level transition law remains required
- Closeout Evidence:
  shipped compile report/tests preserve advisory-only posture and explicit
  current-markdown-controls posture absent shipped transition law.

### Edge 7: Consumed Basis Could Become Prose-Only Instead Of Mechanically Bound

- Risk:
  the advisory reports could talk about shipped `V66-A` / `V66-B` lineage
  without carrying exact refs and hashes, weakening replayability.
- Response:
  keep consumed lineage exact and hashed.
  - emitted `V66-C` artifacts must carry exact consumed-basis refs and hashes
  - same basis plus same frozen policy must yield the same advisory result
- Closeout Evidence:
  shipped models/builders/tests preserve exact consumed-lineage refs and hashes
  plus frozen-policy anchoring for advisory replayability.

### Edge 8: Invalid Structure Could Quietly Collapse Into A Recommendation

- Risk:
  missing prior basis, hash mismatch, bad notice evidence, or invalid policy
  anchor could still yield a nominal recommendation instead of invalidating the
  report.
- Response:
  keep `report_status` distinct from advisory outcome.
  - structural invalidity blocks the recommendation
  - the recommendation is only meaningful when `report_status == valid`
- Closeout Evidence:
  shipped builders/tests now recompute invalid reason from current report status
  and preserve fail-closed invalidity without stale notice-state leakage.

## Current Judgment

- `V66-C` was the right closing slice because `V66-A` already closed the
  bounded source discovery / authority-profile / class-policy starter on
  `main`, and `V66-B` already closed the bounded migration-binding /
  generated-reader-projection / semantic-diff seam on `main`, while explicit
  advisory adoption hardening over that same lineage was still missing.
- the shipped result remained properly bounded:
  - same shipped `V66-A` governed source set only
  - same shipped `V66-B` migration / projection / diff lineage only
  - one compile-report seam only
  - one prose-boundary notice seam only
  - exact consumed-basis refs and hashes remain first-class
  - explicit frozen-policy replayability anchor remains first-class
  - generated projection and semantic diff remain shaping-only
  - current markdown remains controlling absent explicit shipped transition law
  - examples and quoted text remain non-compiling contexts
  - no fresh source-set widening
  - no markdown supersession or source-of-truth promotion by advisory output
  - no `V47` language / checker widening
- `V66-C` is now closed on `main`.
- `V66` is now closed on `main`.
- the current ANM-native documentation-practice family ladder is now complete
  on `main`.
