# Assessment vNext+133 Edges

Status: planning-edge assessment for `V44-C`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS133_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Differential Diagnosis Overclaims As Profile

- Risk:
  the first paired-condition slice could slide directly into model-profile aggregation
  or promotion while the family only has pair-level evidence.
- Response:
  keep `V44-C` differential-first only and forbid profile artifacts, rankings, and
  one-number outputs in the starter slice.

### Edge 2: Knowledge Deficit Is Claimed Without A Real Pair

- Risk:
  the implementation could infer knowledge deficit from a single blocked run or a weak
  compatibility hint rather than a real supplied-versus-withheld pair.
- Response:
  require released paired-condition compatibility posture and the full starter
  supplied/withheld pair before any strong differential judgment is lawful.

### Edge 3: Pair Semantics Become Implementation Taste

- Risk:
  the differential helper could silently decide what counts as “same probe” or
  “compatible pair” using unstated heuristics.
- Response:
  bind pairing law to released `V44-A` compatibility anchors and fail closed on
  incompatible or incomplete pairs.

### Edge 3A: Pair-Level Evidence Refs Stay Ambiguous

- Risk:
  the released differential artifact could cite unqualified `event_index` values that
  stop being meaningful once more than one condition trace is in play.
- Response:
  require trace-qualified supporting event refs in the released artifact so every
  supporting event is anchored to one condition role and one trace.

### Edge 4: `paired_condition_insufficient` Hides Real Structural Failure

- Risk:
  the insufficient-pair posture could become a catch-all that masks clear starter
  procedural-discipline failures.
- Response:
  keep strong judgments available whenever supplied/withheld evidence is strong enough,
  and use `paired_condition_insufficient` only for incomplete, incompatible, or
  materially underdetermined pairs.

### Edge 4A: Status/Judgment Coupling Stays Implicit

- Risk:
  the implementation could emit strong judgments from incomplete or incompatible
  starter pairs because the coupling between `differential_status` and
  `differential_judgment` remains only implied.
- Response:
  freeze the coupling explicitly so incomplete/incompatible pairs may emit only
  `paired_condition_insufficient`, while strong and ambiguous judgments require
  complete starter pairs.

### Edge 5: `V46` Benchmark Projection Bleeds Upstream

- Risk:
  the differential slice could start carrying benchmark-family or scoring assumptions
  simply because the imported benchmarking package expects downstream projections.
- Response:
  keep `V44-C` as a released substrate consumer of `V44-A` and `V44-B` only, with
  `V46` remaining a later consumer of the differential surface.

### Edge 6: External Bundle Becomes Silent Pairing Authority

- Risk:
  the imported reasoning-benchmark package could quietly set pair semantics even
  though its primary code target is still the later benchmarking lane.
- Response:
  use the external bundle only as support evidence, and re-author pair law from the
  released `V44-A` / `V44-B` contracts and committed fixtures.

### Edge 7: Optional Injected-Knowledge Evidence Widens The Slice

- Risk:
  `injected_knowledge_continuation` could quietly become a three-condition override
  doctrine even though the starter slice is supposed to stay supplied-versus-withheld
  first.
- Response:
  allow injected-knowledge evidence only as bounded support that cannot override the
  starter pair law by itself.

## Current Judgment

- `V44-C` is the right next move because the family now has both the assessment object
  (`V44-A`) and the normalized failure substrate (`V44-B`) needed for bounded
  knowledge-versus-procedure diagnosis.
- the slice should remain narrow and differential-first:
  - one differential schema
  - one deterministic pair helper
  - deterministic starter pair fixtures
  - no profile aggregation
  - no benchmark projection
- if the implementation stays that narrow, it should prepare later profile work
  without letting the differential lane overclaim as model ranking.
