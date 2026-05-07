# Assessment vNext+244 Edges

Status: pre-lock edge assessment for `PB-PY-0-C`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS244_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Local Fixture Could Become Official ProgramBench Task

- Required containment:
  `programbench_local_cleanroom_fixture@1` must use only synthetic,
  repo-internal, or toy cleanroom fixture origin posture. Official ProgramBench
  tasks are forbidden in `PB-PY-0-C`.
- Starter expectation:
  reject fixtures that mark official ProgramBench tasks usable as local
  fixtures.

### Edge 2: Fixture Could Expose Forbidden Evidence To Worker

- Required containment:
  hidden tests, original source, decompilation artifacts, external repos,
  internet lookup, and hidden oracle material must not be worker-visible or
  inference-admissible.
- Starter expectation:
  reject worker-visible forbidden evidence and hidden-test inference rows.

### Edge 3: Comparison Packet Could Be Contaminated By Unequal Conditions

- Required containment:
  comparison packets must declare shared fixture, model/worker profile, budget,
  allowed tools, cleanroom policy, probe budget, submission shape, and
  evaluation oracle.
- Starter expectation:
  reject packets that treat changed model, budget, tool access, probe budget,
  fixture, submission shape, or oracle as a clean lane delta.

### Edge 4: Lane Delta Could Drift Beyond A/B/C Substrate

- Required containment:
  the only intended lane delta is base ADEU, ADEU plus conceptual profile, and
  ADEU plus conceptual profile plus Python overlay.
- Starter expectation:
  reject missing lane ids, extra authority-bearing lane ids, and lane
  difference declarations that smuggle official benchmark access or different
  tool policies.

### Edge 5: Local Probe Pass Could Become Hidden-Test Equivalence

- Required containment:
  `programbench_probe_equivalence_audit@1` must keep local probes as local
  research observations only.
- Starter expectation:
  reject hidden-test equivalence, official benchmark truth, evaluator access,
  or postmortem hidden-test feedback as inference evidence.

### Edge 6: Generated Local Submission Could Become Official Solver

- Required containment:
  any local artifact shape stays inside the synthetic/local fixture context and
  cannot become official benchmark submission, official score, model ranking,
  or benchmark truth.
- Starter expectation:
  reject official submission, official score, or leaderboard claims.

### Edge 7: Released A/B Rows Could Be Ignored Or Rewritten

- Required containment:
  C rows must consume released A fixture contract and released B realization
  overlay refs without rewriting them or promoting them to benchmark authority.
- Starter expectation:
  reject unresolved, missing, or authority-promoted A/B refs.

### Edge 8: Family Closeout Alignment Could Close More Than PB-PY-0

- Required containment:
  closeout alignment may close only the local `PB-PY-0` research fixture
  family. It must not select official ProgramBench work, V86, V87, V88,
  implementation-lock review, product, graph, release, or recursive-policy
  work.
- Starter expectation:
  reject future-family or official-benchmark selection claims.

## Residual Edges

- `PB-PY-0-C` may close `PB-PY-0` as a local cleanroom research fixture family,
  but any official ProgramBench participation, hidden evaluator governance, or
  benchmark-result governance requires a later selector or lock.
- Broader conceptual broker implementation, multi-language realization
  overlays, V86/V87/V88 continuation, product, graph, release, and
  recursive-policy work remain unselected.
- Local probe results can guide future research posture only; they cannot
  become hidden-test equivalence or benchmark truth.

## Current Judgment

- `PB-PY-0-C` is starter-ready if the lock, decision, and assessment pass the
  local arc-start gate.
- The selected slice is narrow enough to start: it defines one local fixture,
  one controlled A/B/C comparison packet, one local probe audit, and one family
  closeout alignment surface.
- The most important implementation risk is authority leakage:
  fixture and comparison artifacts must stay local, same-condition controlled,
  non-official, non-hidden-test-equivalent, and non-benchmark-truth-bearing.
