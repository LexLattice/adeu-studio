# Draft Multi-Arc Roadmap Post V85 v0

Status: planning roadmap after `V85` closed on `main` through `vNext+241`,
after the V85 resident-model probe corpus was committed as repo evidence, and
after the hardened conceptual-first retrieval support pass.

Authority layer: planning.

This roadmap records the current best anticipated post-`V85` territory. It is
a support planning surface for the next family selector. It is not a selector,
lock, starter bundle, implementation authority, runtime authority, product
authority, release authority, benchmark truth, ProgramBench participation
authority, source-ingestion authority, internet/decompilation authority, graph
authority, recursive-policy authority, or future-family selection by itself.

Interpretive doctrine:

- horizon-sensitive terms such as `bounded`, `complete`, `closed`,
  `deferred`, and `forbidden` should be read using
  `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`;
- planning-boundary lines below are scope guards and
  absence-of-authorization statements for this roadmap, not lock-equivalent
  permanent prohibitions by themselves;
- planning-vs-lock authority transfer should be read using
  `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`;
- future seam selection and widening posture should be read using
  `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`;
- internal family sequencing should follow
  `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`: one family-level
  `DRAFT_NEXT_ARC_OPTIONS_v*` selector per family, then per-slice
  `vNext+<n>` starter bundles.

## Current Frontier

- `V68` through `V85` are closed on `main`.
- `V85` closed as the semantic declaration and canonical meta-loop lookup
  review family.
- latest closed implementation arc: `vNext+241`
- latest family-level selector: `docs/DRAFT_NEXT_ARC_OPTIONS_v75.md`
- next planning obligation: draft `docs/DRAFT_NEXT_ARC_OPTIONS_v76.md` if the
  next family is selected outside closed `V85`.

Primary post-`V85` support inputs:

- `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85_FAMILY_CLOSEOUT_v0.md`
- `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
- `docs/support/ADEU Conceptual-First Retrieval Pipeline v1.md`
- `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
- `artifacts/agent_harness/meta_loop_probes/SERIES_INTERPRETATION_v0.md`

## Roadmap Thesis

`V85` made resident semantic declaration and canonical lookup reviewable. The
next practical pressure should test whether that semantic substrate can help a
real software-reconstruction benchmark shape without jumping straight to
official ProgramBench participation or benchmark-truth claims.

ProgramBench is a good external pressure because the task shape stresses
exactly the gap ADEU is trying to close:

```text
cleanroom evidence
  -> behavior ontology
  -> concept boundaries
  -> language realization options
  -> implementation obligations
  -> witness probes
  -> equivalence audit
```

The immediate practical arc should be narrow:

```text
PB-PY-0:
  ProgramBench Python Reconstruction Realization Pack
```

Across its A/B/C ladder, it should produce a tiny Python standard-library
realization overlay and one cleanroom-style fixture that proves the harness can
move from recovered program entities to executable Python obligations.
`PB-PY-0-A` should define the fixture contract only; `PB-PY-0-C` may instantiate
the local fixture. The family should not attempt full ProgramBench solving,
official benchmark submission, hidden-test inference, or model ranking.

## Territory Graph

| Candidate / band | Theme | Likely ladder | Current posture | Reason |
|---|---|---|---|---|
| `PB-PY-0` | ProgramBench Python reconstruction realization pack | `A` cleanroom profile/profile-intake and fixture contract; `B` Python realization overlay; `C` one fixture plus A/B/C comparison packet | `selected_next_candidate` for future selector | nearest practical way to test V85-style declaration/lookup evidence on a real reconstruction-shaped problem without claiming benchmark truth |
| conceptual-first retrieval v0.1 | canonical concept DB, retrieval profiles, semantic broker, evidence coverage, claim/evidence binding | concept seed, boundary records, task profile, brokered plan, store realization, coverage report, patch proposal | `mapped_not_selected` | support doc is strong but too broad for the first practical ProgramBench wedge |
| ProgramBench cleanroom adapter | CLI/help/probe-log/generated-output/side-effect stores plus forbidden-store enforcement | cleanroom evidence adapters, probe store realization, ProgramODEUProfile handoff, forbidden-store checks | `deferred_to_later_family` | should consume a first realization pack and one local fixture before external benchmark widening |
| `V86` | obligation expansion / evidence contract / edge probe plan | obligation expansion bundle, edge probe plan, evidence contract, closeout witness requirement map | `mapped_not_selected` | still valid meta-loop continuation, but practical ProgramBench wedge can instantiate a narrow concept-to-witness lane first |
| `V87` | reviewer / auditor taskpack and audit artifact review | reviewer taskpack, audit report, boundary conformance review, audit non-authority guardrail | `mapped_not_selected` | depends on obligation/evidence substrate or a practical fixture producing audit pressure |
| `V88` | deterministic closeout transition table / remand routing | transition table, closeout adjudication summary, remand route register, waiver/permanence/unknown guardrails | `mapped_not_selected` | should not be selected until earlier expansion/audit surfaces exist |
| canonical implementation-lock review | later implementation-lock package review | canonical implementation lock request, stop-gate, lock input bundle, implementation-slice readiness | `deferred_to_later_family` | still carried from `V84-C` / `V85-C`, but not the next practical target |
| official ProgramBench participation | external benchmark run / result governance | benchmark source profile, cleanroom authority, run envelope, result posture, no-benchmark-truth guardrail | `blocked_pending_authority` | PB-PY-0 may prepare a local fixture; it must not become official benchmark participation |

## PB-PY-0 Candidate Shape

Recommended selector name:

```text
PB-PY-0: ProgramBench Python Reconstruction Realization Pack
```

Candidate thesis:

`PB-PY-0` may make a tiny concept-to-Python realization pack reviewable for
ProgramBench-style cleanroom reconstruction, but it must not implement
ProgramBench itself, run official benchmark tasks, access forbidden evidence,
claim benchmark truth, submit results, rank models, or authorize runtime
execution outside a bounded local fixture.

Candidate ladder:

| Slice | Role |
|---|---|
| `PB-PY-0-A` | ProgramBench cleanroom reconstruction profile intake, concept boundary seed, local fixture contract, and non-benchmark-truth guardrail |
| `PB-PY-0-B` | `ConceptRealizationRecord@1` / `PythonReconstructionPlan@1` overlay for CLI, I/O, config, errors, outputs, and side effects |
| `PB-PY-0-C` | one cleanroom fixture plus A/B/C comparison packet: base ADEU, ADEU + concept profile, ADEU + concept profile + Python overlay |

## Anti-Drift Rules

- `ProgramODEUProfile` is not implementation authority.
- `PythonReconstructionPlan` is not execution authority.
- Python stdlib guidance is realization guidance, not canonical program truth.
- Local probe pass is not hidden-test equivalence.
- Hidden ProgramBench tests are external court, not inference evidence.
- Public ProgramBench descriptors are benchmark context, not task truth.
- Cleanroom retrieval must not use original source, decompilation, internet,
  hidden tests, external source repos, host secrets, or task-external code
  repositories.
- Forbidden inference stores must not be registered, mounted, queried, or
  exposed to the worker during inference. Classification alone is not enough if
  the worker can already access the material.
- Benchmark result rows must not claim benchmark truth without a later
  benchmark authority surface.
- `PB-PY-0` does not select `V86`, `V87`, `V88`, official ProgramBench
  participation, implementation-lock review, productization, graph authority,
  release authority, or recursive policy amendment.

## Recommended Next Selector

Draft `docs/DRAFT_NEXT_ARC_OPTIONS_v76.md` to select `PB-PY-0-A` as the next
default starter candidate.
