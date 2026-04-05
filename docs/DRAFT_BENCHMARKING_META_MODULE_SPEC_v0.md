# Draft Benchmarking Meta Module Spec v0

Status: working high-level draft for a separate but connected planning direction.

Authority posture:

- this document is a support/planning-seed artifact;
- it is not a lock doc;
- it does not select the next family by itself;
- it does not authorize runtime behavior, schema release, or implementation by itself.

Related inputs:

- `docs/DRAFT_PROCEDURAL_DEPTH_FIDELITY_BENCHMARK_SPEC_v0.md`
- `docs/DRAFT_STRUCTURAL_REASONING_ASSESSMENT_SPEC_v0.md`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`
- `docs/DRAFT_CONTEST_PARTICIPATION_MODULE_SPEC_v0.md`
- released `V41` practical-analysis substrate
- released `V42` ARC-AGI-3 participation specialization

## 1. Direct Answer

ADEU Studio should have a reusable benchmarking module.

This module is an applied ADEU capability for:

- designing benchmarks;
- generating benchmark instances;
- executing benchmark runs;
- scoring results;
- diagnosing failure topology;
- comparing variants with explicit non-regression posture.

It is not tied to one benchmark family.

It is the general benchmark control layer from which concrete benchmark families are
projected.

## 2. Core Thesis

A useful benchmark is not merely:

- a task;
- a score;
- a leaderboard.

A useful benchmark is a typed measurement instrument with explicit:

- ontology of benchmark objects;
- deontic rules of execution and scoring;
- epistemic interpretation of what results do and do not justify;
- utility posture for why the benchmark exists.

When the benchmark world itself is hierarchical, the substrate should also support:

- explicit plan-spine objects;
- explicit active-step and child-step relations;
- explicit reintegration events after local descent;
- explicit diagnostic separation between horizontal, vertical, and reintegration failure
  classes.

The module's job is to make benchmarks explicit enough that they become:

- composable;
- diagnosable;
- comparable within stated limits;
- non-regressive;
- projectable into concrete benchmark families.

## 3. Why This Is A Separate Arc Direction

This direction is connected to structural reasoning assessment and to ADEU runtime work,
but it should not be collapsed into either.

The structural-assessment branch asks:

- how to assess whether a model can inhabit an explicit inferential skeleton at all.

This benchmarking-module branch asks:

- how ADEU Studio should represent, run, score, and interpret benchmark families as
  governed semantic objects across multiple possible subjects under test.

So this direction may consume insights from:

- structural reasoning assessment;
- contest participation;
- ADEU runtime governance;
- multi-role execution design.

But it should not mint, by itself:

- contest doctrine;
- model-selection doctrine;
- routing doctrine;
- role-assignment doctrine;
- training or distillation entitlement.

## 4. Subject-Under-Test Taxonomy

The benchmark module should not implicitly assume one subject under test.

It should support at least:

- base model;
- prompted model;
- routed single-agent runtime;
- multi-agent system;
- ADEU harness or runtime surface;
- human-plus-tool-plus-model composite system.

This distinction matters because the same benchmark family may mean different things
when applied to:

- a raw model;
- a scaffolded system;
- a governed runtime;
- or a composite socio-technical configuration.

## 5. Conceptual Model

```text
benchmark_module :=
  semantic_measurement_system(
    benchmark_family,
    subject_under_test,
    baseline_regime,
    perturbation_axes,
    scoring_contract,
    trace_model,
    failure_taxonomy,
    interpretation_policy,
    non_regression_policy
  )
```

A benchmark family should compile:

```text
benchmark_idea
  -> benchmark_family_spec
  -> benchmark_projection_spec
  -> benchmark_instance_set
  -> benchmark_run_trace
  -> benchmark_metrics_report
  -> benchmark_diagnostic_report
```

## 6. ADEU Decomposition Of Benchmarking

### 6.1 O-layer

What exists in the benchmark world?

- benchmark family;
- benchmark projection;
- benchmark instance;
- subject under test;
- run;
- step, transition, or event;
- baseline regime;
- perturbation axis;
- metric;
- trace;
- failure event;
- diagnostic summary.

### 6.2 D-layer

What governs the benchmark?

- allowed evidence sources;
- allowed tools;
- execution constraints;
- scoring rules;
- instance validity rules;
- comparison rules;
- non-regression policies;
- baseline-preservation policies;
- subject-typing rules.

### 6.3 E-layer

What does the benchmark justify?

- what capability is actually being measured;
- what confounds remain;
- what baseline is stable;
- what perturbation delta is meaningful;
- what interpretation is valid versus overclaimed.

### 6.4 U-layer

Why does the benchmark exist?

- capability mapping;
- regression detection;
- architecture comparison;
- system diagnosis;
- routing or orchestration research input;
- training or distillation research input;
- ADEU-grade capability typing.

## 7. Required Benchmark Principles

### 7.1 Baseline-first

Every benchmark family should define a low-noise baseline regime before testing harder
variants.

### 7.2 Perturbation-explicit

Difficulty should not be treated as one blob. Harder variants must be typed by explicit
perturbation axes.

### 7.3 Non-regression-aware

Higher-layer gains must be evaluated against preserved baseline competence.

### 7.4 Traceability

Benchmark outputs should permit step or event-level diagnosis, not only end-score
judgment.

### 7.5 Capability-vector orientation

Benchmarks should prefer multi-axis profiles over single scalar capability claims.

### 7.6 Projection modularity

A general benchmark family should support concrete projections without collapsing the
top-layer schema into the first projection.

### 7.7 Diagnostic-first output posture

Benchmark findings should be diagnostic by default.

They may inform later:

- model selection;
- routing;
- role assignment;
- training;
- architectural decisions.

But they should not, by themselves, authorize those downstream promotions.

## 8. Epistemic Posture Of Benchmark Outputs

The benchmark module should not emit only scores and reports.

It should also make the epistemic posture of its outputs explicit.

At a minimum, outputs should distinguish between:

- observed:
  directly measured behavior from the run;
- derived deterministically:
  metrics or deltas computed from explicit scoring rules;
- inferred interpretively:
  topology or boundary-condition hypotheses derived from observed traces and metrics;
- adjudicated:
  human-reviewed interpretation or benchmark-quality judgment;
- settled:
  later accepted posture under a separate governance path.

This matters because benchmark reports often look more authoritative than their actual
warrant.

## 9. Reliability Semantics

The benchmark module should not talk about:

- stable baseline;
- reliable `100%`;
- low noise;
- non-regression;

without defining what those mean operationally.

At a minimum, the module should require explicit policy for:

- repeated-run stability under fixed execution context;
- acceptable variance bands for baseline families;
- paraphrase or equivalent-instance stability when the projection claims it;
- non-regression floors below which perturbation results should not be overread;
- whether reliability is judged:
  - per instance,
  - per family,
  - per repeated-run bundle,
  - or per fixed execution-context bundle.

Reliability claims without repetition policy should remain weak.

## 10. General Artifact Family

The first family should likely emit a bounded, reusable benchmark artifact set.

Illustrative candidate artifacts are:

- `benchmark_family_spec@1`
- `benchmark_projection_spec@1`
- `benchmark_instance_spec@1`
- `benchmark_execution_context@1`
- `benchmark_run_trace@1`
- `benchmark_metrics_report@1`
- `benchmark_diagnostic_report@1`
- `benchmark_validation_report@1`

These names are planning-level candidate names, not frozen lock-level schema IDs.

### 10.1 Candidate artifact roles

`benchmark_family_spec@1`:

- top-level benchmark family description with purpose, capability axes, baseline regime,
  perturbation axes, scoring posture, and non-regression policy.

`benchmark_projection_spec@1`:

- concrete benchmark realization inside a family.

`benchmark_instance_spec@1`:

- one benchmark instance with bounded instructions, source surface, gold surfaces, and
  validity rules.

`benchmark_execution_context@1`:

- captures the configuration under which a benchmark run is actually executed.

`benchmark_run_trace@1`:

- observed benchmark execution trace for one subject under test.

`benchmark_metrics_report@1`:

- aggregate measured results with baseline, perturbation, delta, and non-regression
  posture.

`benchmark_diagnostic_report@1`:

- interpretive output with failure topology and open questions, still diagnostic by
  default.

`benchmark_validation_report@1`:

- evaluates the benchmark family or projection itself for reproducibility, diagnostic
  sharpness, noise level, and baseline stability.

## 11. Benchmark Lifecycle

### Stage A: family definition

Define the benchmark family at the semantic level.

### Stage B: projection design

Choose one concrete capability slice and encode its instance rules.

### Stage C: baseline validation

Verify that the clean baseline regime is stable and low-noise through explicit:

- repeated-run stability checks;
- family-wide variance reporting;
- benchmark-instance quality checks;
- non-regression floor tests before perturbation results are accepted.

### Stage D: perturbation introduction

Add one typed complexity or ambiguity factor at a time.

### Stage E: metrics and topology analysis

Measure not just score, but where and how failure occurs.

### Stage F: non-regression comparison

Compare subject variants against the preserved baseline.

### Stage G: bounded capability profile extraction

Characterize capability envelope within the benchmark's explicit scope and epistemic
limits.

## 12. Execution-Context Capture

Benchmark comparisons should be ontologically clean.

So benchmark runs should make explicit, when relevant:

- model version;
- prompt scaffold;
- tool availability;
- context budget;
- runtime mode;
- determinism or stochasticity posture;
- source-surface or repo-snapshot identity.

Without that, repeated comparisons become hard to interpret and easy to overclaim.

## 13. Benchmark Axis Categories

The top-layer module should support at least these benchmark axis types:

- procedural depth;
- hierarchical action-plan fidelity;
- branching complexity;
- recursive structure;
- delayed constraints;
- scope restrictions;
- ambiguity;
- evidence conflict;
- state carry distance;
- ontology density;
- deontic hardness;
- repairability;
- provenance sensitivity.

Not every projection uses all axes.

## 14. Diagnostic-To-Promotion Boundary

Benchmark results may later become inputs to:

- model selection;
- routing design;
- role assignment;
- training or distillation planning;
- architecture comparison.

But the module should make explicit that:

- diagnostic findings do not imply promotion entitlement;
- routing recommendations do not imply routing authority;
- role-fit hypotheses do not imply role-assignment authority;
- benchmark strength on one axis does not imply general capability authority.

Only separately governed downstream artifacts should convert benchmark diagnosis into
operational promotion.

## 15. Non-Goals

This module should not initially aim to:

1. become a generic benchmark leaderboard platform;
2. reduce all capabilities to one scalar metric;
3. replace domain-specific evals;
4. infer causal explanations beyond what the benchmark design supports;
5. guarantee that every benchmark family is equally mature or comparable;
6. authorize downstream role, routing, or training decisions by benchmark output alone.

## 16. Connection To Procedural Depth Fidelity

`docs/DRAFT_PROCEDURAL_DEPTH_FIDELITY_BENCHMARK_SPEC_v0.md` should be read as:

- one first concrete benchmark projection candidate inside this broader module;
- not the top-layer module itself;
- not the only future benchmark family;
- not a replacement for the broader structural-assessment branch.

The two-doc split is correct:

- this doc holds the general benchmark module doctrine;
- the procedural-depth doc holds one concrete benchmark projection.

## 17. Planning-Seed Acceptance Criteria

This high-level seed is mature enough to feed next-arc planning only if it can support:

1. a clear distinction between general benchmark architecture and concrete benchmark
   projections;
2. a clear subject-under-test taxonomy rather than implicit model-only assumptions;
3. baseline-first and perturbation-explicit benchmark doctrine;
4. explicit reliability semantics for stable baseline, reliable `100%`, and acceptable
   variance;
5. explicit benchmark artifact family for family specs, projections, instances, execution
   context, traces, metrics, diagnostics, and validation reports;
6. explicit epistemic posture for benchmark outputs;
7. explicit diagnostic-first boundary before downstream promotion;
8. explicit benchmark-self-validation rather than subject-only evaluation;
9. explicit execution-context capture for reproducible comparison;
10. explicit ADEU O/E/D/U interpretation of benchmarking as a measurement system.

## 18. Suggested Follow-On Docs

If this direction is selected for next-arc planning, the next bundle should probably
be:

- one next-arc planning draft for the benchmarking branch;
- one benchmark family decomposition draft;
- one benchmark artifact draft;
- and then bounded concrete benchmark projections such as the procedural-depth family.

No concrete family/path label is selected by this document.

## 19. Machine-Checkable Seed Summary

```json
{
  "schema": "benchmarking_meta_module_seed@1",
  "artifact": "docs/DRAFT_BENCHMARKING_META_MODULE_SPEC_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_seed",
  "selects_next_family": false,
  "authorizes_runtime_or_schema_release": false,
  "general_module_theme": "adeu_applied_benchmarking_module",
  "general_benchmark_layer_required": true,
  "projection_modularity_required": true,
  "subject_under_test_taxonomy_required": true,
  "baseline_first_required": true,
  "reliability_semantics_required": true,
  "perturbation_explicit_required": true,
  "traceability_required": true,
  "non_regression_required": true,
  "benchmark_validation_required": true,
  "execution_context_capture_required": true,
  "diagnostic_first_output_posture_required": true,
  "benchmark_output_epistemic_postures": [
    "observed",
    "derived_deterministically",
    "inferred_interpretively",
    "adjudicated",
    "settled"
  ],
  "candidate_artifacts": [
    "benchmark_family_spec@1",
    "benchmark_projection_spec@1",
    "benchmark_instance_spec@1",
    "benchmark_execution_context@1",
    "benchmark_run_trace@1",
    "benchmark_metrics_report@1",
    "benchmark_diagnostic_report@1",
    "benchmark_validation_report@1"
  ],
  "diagnostic_findings_non_promotional_required": true,
  "source_docs": [
    "docs/DRAFT_PROCEDURAL_DEPTH_FIDELITY_BENCHMARK_SPEC_v0.md",
    "docs/DRAFT_STRUCTURAL_REASONING_ASSESSMENT_SPEC_v0.md",
    "docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md"
  ]
}
```

## 20. Compressed Theorem

ADEU Studio should be able to treat benchmarks as governed semantic measurement systems,
not merely as tasks with scores.

The first safe move is a general benchmark module that can represent benchmark families,
subjects under test, execution contexts, baseline regimes, perturbation axes, traces,
metrics, validation reports, and bounded diagnostic interpretation without directly
authorizing downstream operational promotion.
