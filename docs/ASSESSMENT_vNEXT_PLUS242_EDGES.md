# Assessment vNext+242 Edges

Status: pre-lock edge assessment for `PB-PY-0-A`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS242_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Cleanroom Profile Could Become Implementation Authority

- Required containment:
  `programbench_cleanroom_reconstruction_profile@1` must keep
  `implementation_authority_posture` non-authoritative and must not emit
  Python code, command plans, or execution authority.
- Starter expectation:
  reject profile rows that claim implementation, execution, or generated code.

### Edge 2: Public Descriptor Could Become Benchmark Truth

- Required containment:
  public ProgramBench observations must carry source URL, retrieval posture, and
  advisory-only / not-used-as-evaluation-truth posture.
- Starter expectation:
  reject rows that treat public task counts, test counts, or score snapshots as
  task truth or benchmark truth.

### Edge 3: Forbidden Evidence Could Be Merely Labeled After Exposure

- Required containment:
  forbidden inference stores must not be registered, mounted, queried, or
  exposed to the worker during inference.
- Starter expectation:
  reject rows where original source, decompilation, internet lookup, external
  repos, host secrets, Docker socket, or hidden tests are worker-visible during
  inference.

### Edge 4: Hidden Tests Could Become Inference Evidence

- Required containment:
  hidden tests may be external court during evaluation only. They must not be
  visible to or inferred by the worker during reconstruction.
- Starter expectation:
  reject hidden-test rows marked inference-admissible or cleanroom-visible.

### Edge 5: Local Probe Pass Could Become Hidden-Test Equivalence

- Required containment:
  worker-generated probes may support local development posture but may not
  prove hidden-test equivalence.
- Starter expectation:
  reject local probe rows marked as benchmark truth or hidden-test equivalence.

### Edge 6: Concept Boundary Seed Could Become Python Realization

- Required containment:
  seed rows make O-lane inventory visible but do not authorize Python stdlib
  patterns, implementation plans, or generated code. Boundary-outline fields
  are advisory seed material for later review, not full concept-boundary
  authority.
- Starter expectation:
  reject concept seed rows that claim `ConceptRealizationRecord@1` or
  `PythonReconstructionPlan@1` authority.

### Edge 7: Fixture Contract Could Become Fixture Implementation

- Required containment:
  `programbench_local_cleanroom_fixture_contract@1` defines the law for a later
  local fixture but does not build the reference executable, usage docs,
  oracle, or submission harness.
- Starter expectation:
  reject fixture-contract rows with `fixture_implementation_posture` claiming a
  built fixture.

### Edge 8: Python Stdlib Guidance Could Collapse Concept Into Code Idiom

- Required containment:
  `PB-PY-0-A` does not ship Python realization overlay rows at all. Later
  `PB-PY-0-B` must keep stdlib surfaces as realization options, not canonical
  concept definitions.
- Starter expectation:
  no Python realization rows ship in A.

### Edge 9: Official ProgramBench Participation Could Be Smuggled In

- Required containment:
  no official runner integration, official task execution, benchmark
  submission, hidden evaluator handling, benchmark score, or model ranking.
- Starter expectation:
  reject rows that claim official benchmark participation or scores.

### Edge 10: Phase Separation Could Collapse

- Required containment:
  inference, local development, evaluation, and postmortem phases must be
  explicit and separately constrained.
- Starter expectation:
  reject rows that retroactively admit evaluation/postmortem material as
  inference evidence.

### Edge 11: PB-PY-0-A Could Select PB-PY-0-B/C Or V86-V88

- Required containment:
  `PB-PY-0-A` may emit deferred handoff notes only. It must not select
  `PB-PY-0-B`, `PB-PY-0-C`, `V86`, `V87`, `V88`, implementation-lock review,
  product work, graph work, or recursive-policy work.
- Starter expectation:
  reject rows that mark a later slice or family selected, and reject any
  `PB-PY-0-B` / `PB-PY-0-C` artifact kind included in the A fixture set.

### Edge 12: Later Comparison Could Become Uncontrolled

- Required containment:
  later `PB-PY-0-C` comparisons must keep same-condition controls explicit:
  shared fixture, worker/model profile, budget, allowed tools, cleanroom policy,
  probe budget, submission shape, and evaluation oracle. The only intended lane
  delta should be base ADEU versus conceptual profile versus conceptual profile
  plus Python overlay.
- Starter expectation:
  A records this as a later-slice requirement only; no comparison packet ships
  in A.

## Residual Edges

- `PB-PY-0-B` must consume released `PB-PY-0-A` rows and prove that
  `ConceptRealizationRecord@1` and Python stdlib surfaces remain realization
  overlays, not canonical concept definitions or execution authority. Its
  `python_reconstruction_plan@1` rows must contain no source code, executable
  file paths, shell commands, generated implementation artifacts, or fixture
  payloads.
- `PB-PY-0-C` must instantiate at most one local cleanroom fixture under the
  released A fixture contract and keep the A/B/C comparison local,
  non-official, non-benchmark-truth, and same-condition controlled. Official
  ProgramBench tasks remain forbidden as local fixture origins.
- Any official ProgramBench participation, hidden evaluator result governance,
  broader conceptual broker implementation, V86/V87/V88 continuation, product,
  graph, release, or recursive-policy family must be selected by a later
  selector or lock.

## Current Judgment

- `PB-PY-0-A` is starter-ready if the lock, decision, and assessment pass the
  local arc-start gate.
- The selected slice is narrow enough to start: it defines cleanroom profile,
  source-index, concept-seed, guardrail, and fixture-contract surfaces only.
- The most important implementation risk is evidence leakage: forbidden
  material must be operationally unreachable during inference, not merely
  labeled after exposure.
