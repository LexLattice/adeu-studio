# Assessment vNext+185 Edges

Status: post-closeout edge assessment for `V67-A` (April 23, 2026 UTC).

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS185_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: The Starter Artifact Language Could Be Overread As A Hidden Solver

- Risk:
  shipping a typed adjudication-result surface in `V67-A` could be overread as if
  the repo had already shipped bounded candidate evaluation.
- Response:
  keep `V67-A` result fixtures schema/validator-only and non-engine-computed.
  - no bounded adjudication engine in `V67-A`
  - no feasibility computation by implication
- Closeout Evidence:
  shipped models/tests remain starter language plus validation posture only and
  defer bounded computation to `V67-B`.

### Edge 2: Ergonomic Classes Could Drift Into Free Widget Vocabulary

- Risk:
  ergonomic registry rows could become route-local widget labels instead of the
  frozen artifact-inspector starter vocabulary.
- Response:
  keep the starter class set exact and reject unknown class drift.
  - exact finite class ids only
  - no ad hoc widget taxonomy
- Closeout Evidence:
  shipped registry models/tests preserve the selected finite class vocabulary and
  reject unknown class ids.

### Edge 3: Candidate Rows Could Quietly Mint New UX Semantics

- Risk:
  finite candidate rows could be overread as permission to mint new regions,
  lanes, action clusters, or same-context reveal terms outside the released UX
  governance basis.
- Response:
  keep candidate rows strictly bound to released projection refs, approved
  profiles, and glossary terms only.
  - no new semantic lanes or regions by candidate row
  - no new same-context vocabulary by candidate row
- Closeout Evidence:
  shipped candidate-table validation/tests preserve exact released projection and
  glossary binding and reject unknown refs or reveal terms.

### Edge 4: Source Lineage Could Quietly Weaken Replayability

- Risk:
  starter fixtures could talk about lineage in prose while omitting exact
  repo-relative refs and hashes, making future adjudication replay-weak.
- Response:
  keep lineage rows exact, sorted, and replayable.
  - repo-relative `artifact_ref` only
  - exact `artifact_hash` rows only
  - actual-canonical-payload mismatch fails closed
- Closeout Evidence:
  shipped bundle-validation/tests preserve exact source refs and hashes and now
  report concrete failing `artifact_ref` values on mismatch.

### Edge 5: Physical Or Visual Claims Could Overstate Measurement Certainty

- Risk:
  DPR-only or otherwise incomplete chains could be mistaken for admissible
  physical-size or visual-angle reasoning.
- Response:
  keep admissibility derivation explicit and fail closed for dependent claims.
  - DPR presence alone is not physical-size admissibility
  - visual-angle admissibility remains dependent on the full required chain
- Closeout Evidence:
  shipped admissibility checks/tests reject present-but-inadmissible DPR chains
  and preserve fail-closed physical / visual reasoning posture.

### Edge 6: Platform Or Preference Layers Could Quietly Become Hard Law

- Risk:
  platform presets or user preferences could silently weaken higher-order hard
  floors or become constitutional law by convenience.
- Response:
  keep authority-stack precedence explicit and fail closed.
  - platform presets are not hard law unless repo-adopted
  - user preference may raise but may not lower hard floors
- Closeout Evidence:
  shipped rule-authority checks/reject fixtures preserve exact precedence and
  non-lowering posture.

### Edge 7: Canonical Helper Drift Could Escape The Frozen Discovery Guard

- Risk:
  adding new canonical JSON helpers in `V67-A` could silently drift the frozen
  conformance-entrypoint set and break downstream reproducibility checks.
- Response:
  keep canonical-helper discovery explicit and update the frozen allowlist when
  new helper entrypoints are intentionally introduced.
  - new canonical helper entrypoints require explicit allowlist update
  - drift remains fail-closed under the existing conformance test
- Closeout Evidence:
  shipped follow-up hardening updated the frozen canonical-entrypoint allowlist
  and restored deterministic conformance parity under CI.

## Current Judgment

- `V67-A` was the right first shipped slice because the family first needed the
  ergonomic artifact language itself before any bounded computation.
- the shipped result remained properly bounded:
  - same existing repo-owned implementation package (`adeu_core_ir`) only
  - seven starter ergonomic artifact-language surfaces only
  - deterministic authoritative and mirror schema exports
  - exact finite ergonomic class and candidate profile vocabularies
  - glossary-bound same-context validation
  - exact source-lineage replayability
  - fail-closed preset / preference / admissibility posture
  - scalar-score export prohibition
  - no bounded adjudication engine
  - no runtime measurement evidence artifact
  - no runtime bridge report
- `V67-A` is now closed on `main`.
- `V67` remains active on `main`; the bounded adjudication-engine seam is the next
  selected follow-on under `V67-B`.
