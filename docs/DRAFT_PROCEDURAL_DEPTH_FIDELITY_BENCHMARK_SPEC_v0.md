# Draft Procedural Depth Fidelity Benchmark Spec v0

Status: working high-level draft for a concrete benchmark projection inside the broader
benchmarking-module direction.

Authority posture:

- this document is a support/planning-seed artifact;
- it is not a lock doc;
- it does not select the next family by itself;
- it does not authorize runtime behavior, schema release, or implementation by itself.

Related inputs:

- `docs/DRAFT_BENCHMARKING_META_MODULE_SPEC_v0.md`
- `docs/DRAFT_STRUCTURAL_REASONING_ASSESSMENT_SPEC_v0.md`
- `docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`

## 1. Name

Primary label:

- `Procedural Depth Fidelity Benchmark`

Alternative internal label:

- `Arbitrary Instruction Following Benchmark`

This document uses `Procedural Depth Fidelity` as the preferred public framing because
it is more specific about what is actually being measured.

## 2. Purpose

Measure how reliably a subject under test can follow a long, explicit, non-ambiguous
instruction constitution over a bounded artifact world.

This benchmark is designed to isolate:

- arbitrary instruction following;
- procedural persistence;
- branch obedience;
- state-carry fidelity;
- constraint compliance;
- failure topology.

It is not primarily a knowledge benchmark.

## 3. Core Claim

Before diagnosing higher-order reasoning failures, we need a clean measure of whether
the subject under test can inhabit an externally imposed procedural world at all.

This benchmark exists to answer that lower-layer question directly.

## 4. Target Capability

The target capability is:

- stable execution of explicit structured instructions over depth.

This includes:

- following ordered steps;
- preserving carried state;
- obeying negative constraints;
- selecting correct branches;
- avoiding forbidden actions;
- maintaining fidelity over long chains.

## 5. Relationship To Structural Assessment

This benchmark is connected to the broader structural-assessment direction, but it
should not be collapsed into it.

The structural-assessment branch asks, at a higher doctrinal level:

- can a model inhabit an explicit inferential skeleton at all?

This benchmark projection asks, in one applied measurement form:

- how well does a subject under test execute explicit instruction constitutions over
  depth, branching, delayed constraints, and bounded artifact worlds?

So this benchmark may consume structural-assessment ideas.

It should not, by itself, replace the broader structural-assessment doctrine or claim to
be the only valid projection of that doctrine.

## 6. Subject-Under-Test Posture

This benchmark should support more than one subject-under-test class.

At minimum it should be applicable to:

- base model;
- prompted model;
- routed single-agent runtime;
- multi-agent system;
- ADEU harness or runtime surface.

This matters because procedural fidelity can degrade or improve depending on whether the
benchmark is applied to:

- a raw model;
- a prompt-scaffolded model;
- a multi-step governed runtime.

### 6.1 Execution-context capture

Comparisons are only meaningful if the execution context is explicit.

At a minimum, this projection should capture:

- subject identity and version;
- prompt scaffold or wrapper identity when applicable;
- tool availability;
- context-budget posture;
- runtime mode;
- determinism or stochasticity posture;
- repo-snapshot or source-surface identity;
- orchestration topology when the subject is a routed or multi-agent system.

This projection should inherit the broader benchmarking module's execution-context
discipline rather than rely on informal run labels.

## 7. Initial Benchmark World

The first `v0` world should be:

- repo-grounded;
- read-only;
- deterministic;
- typed;
- low ambiguity;
- machine-checkable.

The repo is used not as a coding challenge, but as a bounded ontology and evidence
surface.

### 7.1 Snapshot and stale-result posture

Because the repo is a moving world, the benchmark should not rely on live, drifting
state without saying so.

The initial projection should therefore prefer:

- snapshot-bound instance generation;
- explicit source-set or repo-snapshot identity;
- explicit stale-result posture for benchmark outputs;
- explicit rules for whether cross-snapshot comparison is valid or only advisory.

Without that, a repo-grounded benchmark can look deterministic while actually drifting
with the underlying tree.

## 8. Baseline Regime

The baseline regime should be designed for maximum interpretability.

### 8.1 Required properties

- instructions are unambiguous;
- outputs are deterministic;
- state variables are explicit;
- no hidden trick wording;
- no ambiguous references;
- no uncontrolled tool noise;
- scope boundaries are explicit.

### 8.2 Initial baseline classes

- linear retrieval chains;
- linear comparison chains;
- linear state-carry chains.

Illustrative pattern:

- find artifact `A`;
- extract field `X`;
- compare with field `Y` from artifact `B`;
- store result in variable `Z`;
- use `Z` in step `N+5`;
- emit exact structured answer.

### 8.3 Reliability semantics

This benchmark should not talk about:

- stable baseline;
- reliable `100%`;
- low noise;
- acceptable variance;

without defining them operationally.

At a minimum, the projection should require:

- repeated-run policy under fixed execution context and fixed repo snapshot;
- explicit statement of whether reliability is judged per instance, per family, or per
  repeated-run bundle;
- explicit variance or instability thresholds for baseline families;
- explicit non-regression floors below which perturbation results should not be
  overread;
- explicit statement of whether paraphrase-equivalent instances are part of reliability
  judgment or a separate perturbation regime.

In this family, reliable `100%` should mean perfect measured performance over an
explicitly declared repeated-run bundle, not one clean-looking run.

## 9. Perturbation Regimes

Once baseline is stable, introduce one axis at a time.

### 9.1 Branch perturbation

Add if/else forks and branch-local state.

Measures:

- branch selection fidelity;
- forbidden-branch contamination;
- alternate-state handling.

### 9.2 Depth perturbation

Increase step count and dependency span.

Measures:

- longest correct prefix;
- depth survival curve;
- collapse topology.

### 9.3 Delayed-constraint perturbation

Introduce rules whose effects matter many steps later.

Measures:

- negative-constraint persistence;
- long-range obedience.

### 9.4 Recursive perturbation

Introduce repeated subroutines over selected artifacts.

Measures:

- recursive template execution;
- subroutine stability;
- aggregation fidelity.

### 9.5 Paraphrase-invariance perturbation

Introduce semantically equivalent restatements while preserving the same unambiguous
instruction constitution.

Measures:

- surface-form invariance;
- equivalent-instruction preservation;
- paraphrase-induced drift.

### 9.6 Ambiguity perturbation

Introduce tightly controlled lexical or referential ambiguity.

Measures:

- interpretation stability;
- ambiguity-handling delta relative to baseline.

### 9.7 Evidence perturbation

Introduce conflicting or competing evidence surfaces with explicit admissibility rules.

Measures:

- evidence-sensitive obedience;
- provenance handling.

## 10. Core Metrics

### 10.1 Step-follow rate

Correctly executed steps divided by applicable steps.

### 10.2 Longest correct prefix

Deepest continuous prefix executed without error.

### 10.3 Depth degradation curve

Accuracy as a function of step depth.

### 10.4 Branch accuracy

Correct branch-selection rate.

### 10.5 Constraint-violation rate

Frequency of explicit rule violations.

### 10.6 State-carry score

Correct preservation and reuse of carried variables.

### 10.7 Recovery locality

Ability to resume after local failure or correction.

This metric should only be scored when the projection defines an explicit local
correction or intervention protocol. If the first bounded implementation does not define
that protocol, recovery locality should remain deferred rather than scored informally.

### 10.8 Failure topology profile

Distribution of:

- isolated misses;
- contiguous collapse;
- branch confusion;
- scope leakage;
- hallucinated completion;
- restart drift;
- recursive corruption.

### 10.9 Baseline-preservation score

For subject variants, degree to which higher-layer gains preserve lower-layer clean
competence.

## 11. Failure Taxonomy

### 11.1 O failures

- wrong artifact selected;
- wrong object tracked;
- ontology confusion;
- incorrect identity binding.

### 11.2 D failures

- wrong order;
- forbidden action executed;
- branch law violated;
- scope restriction broken;
- delayed rule forgotten.

### 11.3 E failures

- unsupported value claimed;
- state confusion;
- incorrect evidence use;
- provenance rule ignored.

### 11.4 U failures

- shortcut completion instead of step fidelity;
- plausible summary replacing procedure;
- premature closure;
- optimization for final-looking answer over lawful execution.

## 12. Gold Representation

Each benchmark instance should compile to a machine-checkable gold representation.

Suggested gold components:

- step IDs;
- required preconditions;
- expected operation;
- allowed source surface;
- expected output;
- expected state delta;
- allowed branches;
- forbidden actions.

This prevents scoring from depending on prose plausibility.

### 12.1 Gold-trace formalism

The projection should not stay vague about what kind of gold object it uses.

For earliest linear families, `v0` should prefer a strict total-order trace with
explicit state deltas.

For branching or recursive families, the gold should widen into a typed transition graph
or partial-order representation that explicitly enumerates valid alternate paths or
equivalence classes.

Equivalent valid paths should be represented in the gold object itself, not inferred ad
hoc by the scorer after the run.

## 13. Initial Instance Families

These are benchmark families, not single instances.

The first practical implementation should center on `Linear-20` and `Linear-50`.
`Linear-100` should remain an early extension until scoring and gold-trace formalism are
shown to be stable enough to justify deeper stress tests.

### 13.1 `Linear-20`

Small deterministic chain for early sanity checks.

### 13.2 `Linear-50`

Intermediate baseline.

### 13.3 `Linear-100`

Early deep-baseline extension once the smaller linear families are stable.

### 13.4 `Branch-60`

Moderate branching with clear state rules.

### 13.5 `Recursive-40`

Fewer top-level steps, but repeated subroutine structure.

## 14. Benchmark Interpretation Policy

### 14.1 A perfect baseline result is meaningful

If a subject achieves reliable `100%` in a baseline family, that marks a solved regime,
not a useless result.

### 14.2 Perturbation results must be interpreted relative to baseline

Do not overclaim ambiguity or complexity weakness if the baseline itself is unstable.

### 14.3 No higher-order gains without baseline preservation

A subject variant that improves on perturbed cases while degrading baseline should be
flagged for regression review.

### 14.4 Diagnostic-first posture

This benchmark may later inform:

- model selection research;
- routing research;
- multi-agent role-fit research;
- scaffold design;
- SRM-style capability profiling.

But benchmark outputs should remain diagnostic by default.

They should not, by themselves, authorize:

- constitutional role assignment;
- routing authority;
- model promotion;
- training entitlement.

### 14.5 Projection-level epistemic posture inheritance

This projection should inherit the broader benchmarking module's output-posture
discipline.

At a minimum, outputs should distinguish between:

- observed run behavior;
- derived deterministic scores and deltas;
- inferred interpretive hypotheses;
- adjudicated benchmark-quality judgment;
- settled posture under a later governance path.

Projection-level metrics and benchmark diagnostics should not skip those posture layers.

### 14.6 Benchmark-self-validation matters

Typed scoring does not by itself prove that the benchmark family is low-noise,
reproducible, or diagnostically sharp.

This projection should therefore include explicit validation of:

- repeated-run stability;
- instance quality;
- gold-trace adequacy;
- scorer determinism;
- baseline noise floor.

## 15. Utility Of The Benchmark

This benchmark supports:

- model comparison research;
- system comparison research;
- role-routing research input;
- scaffold design;
- fine-tune or regression checks;
- SRM-style capability profiling;
- diagnosis of root causes before tackling complex open tasks.

## 16. Connection To Multi-Agent Design

This benchmark can be useful to multi-agent design research.

For example, it may help generate bounded hypotheses such as:

- strong linear fidelity may fit executor-like roles;
- strong branch handling may fit planner-like roles;
- strong constraint obedience may fit governance-check roles;
- strong evidence handling may fit reviewer or auditor roles;
- strong recursion may fit decomposition or refinement roles.

Those should remain role-fit hypotheses, not assignment authority, until a separate
promotion law exists.

## 17. v0 Acceptance Criteria

A `v0` of this benchmark projection should be considered real only if it can:

1. define at least one clean baseline family;
2. define repeated-run reliability policy for stable baseline and reliable `100%`;
3. capture execution context and repo-snapshot identity explicitly;
4. generate machine-checkable instance specs;
5. define explicit gold-trace formalism for both linear and non-linear families;
6. score at least linear chains deterministically;
7. produce failure-topology and benchmark-validation reports, not just end accuracy;
8. compare two subject variants with non-regression awareness;
9. distinguish baseline instability from perturbation-induced degradation;
10. keep benchmark outputs diagnostic-first and epistemically typed.

## 18. Suggested Artifact Family

Illustrative candidate artifacts are:

- `procedural_depth_family_spec@1`
- `procedural_depth_projection_spec@1`
- `procedural_depth_instance@1`
- `procedural_depth_execution_context@1`
- `procedural_depth_gold_trace@1`
- `procedural_depth_run_trace@1`
- `procedural_depth_metrics@1`
- `procedural_depth_failure_topology@1`
- `procedural_depth_non_regression_report@1`
- `procedural_depth_benchmark_validation_report@1`

These names are planning-level candidate names, not frozen lock-level schema IDs.

## 19. Suggested Follow-On Docs

If this direction is selected for next-arc planning, the next bundle should probably
be:

- one benchmark-branch planning draft;
- one procedural-depth artifact draft;
- one procedural-depth instance-generation draft;
- and one tiny `Linear-20` reference family over a bounded repo snapshot.

## 20. Machine-Checkable Seed Summary

```json
{
  "schema": "procedural_depth_fidelity_benchmark_seed@1",
  "artifact": "docs/DRAFT_PROCEDURAL_DEPTH_FIDELITY_BENCHMARK_SPEC_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_seed",
  "selects_next_family": false,
  "authorizes_runtime_or_schema_release": false,
  "parent_family": "benchmarking_meta_module",
  "role": "first_concrete_projection",
  "repo_grounded_read_only_world_preferred": true,
  "snapshot_bound_instance_generation_required": true,
  "explicit_stale_result_posture_required": true,
  "execution_context_capture_required": true,
  "baseline_first_required": true,
  "reliability_semantics_required": true,
  "baseline_repeated_run_policy_required": true,
  "perturbation_axes": [
    "branch",
    "depth",
    "delayed_constraint",
    "recursive",
    "paraphrase_invariance",
    "ambiguity",
    "evidence"
  ],
  "core_metrics": [
    "step_follow_rate",
    "longest_correct_prefix",
    "depth_degradation_curve",
    "branch_accuracy",
    "constraint_violation_rate",
    "state_carry_score",
    "recovery_locality",
    "failure_topology_profile",
    "baseline_preservation_score"
  ],
  "recovery_locality_requires_explicit_correction_protocol": true,
  "gold_trace_formalism_required": true,
  "projection_inherits_parent_output_epistemic_postures_required": true,
  "diagnostic_first_output_posture_required": true,
  "constitutional_role_assignment_not_authorized": true,
  "benchmark_self_validation_required": true,
  "practical_initial_reference_families": [
    "Linear-20",
    "Linear-50"
  ],
  "linear_100_early_extension_until_scoring_stable": true,
  "candidate_artifacts": [
    "procedural_depth_family_spec@1",
    "procedural_depth_projection_spec@1",
    "procedural_depth_instance@1",
    "procedural_depth_execution_context@1",
    "procedural_depth_gold_trace@1",
    "procedural_depth_run_trace@1",
    "procedural_depth_metrics@1",
    "procedural_depth_failure_topology@1",
    "procedural_depth_non_regression_report@1",
    "procedural_depth_benchmark_validation_report@1"
  ],
  "source_docs": [
    "docs/DRAFT_BENCHMARKING_META_MODULE_SPEC_v0.md",
    "docs/DRAFT_STRUCTURAL_REASONING_ASSESSMENT_SPEC_v0.md",
    "docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md"
  ]
}
```

## 21. Compressed Theorem

Before we can interpret complex reasoning failure, we must first know whether a subject
under test can reliably execute a long, explicit, non-ambiguous instruction
constitution.

Procedural Depth Fidelity exists to measure that substrate directly, with baseline-first
discipline, typed perturbations, machine-checkable gold traces, explicit execution
contexts, benchmark-self-validation, and bounded diagnostic interpretation.
