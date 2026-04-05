I inspected the imported reasoning-benchmark bundle against the pending structural
reasoning and benchmarking planning seams.

The narrative claim is that this bundle belongs in the still-pending `V44` / `V46`
lane, with:

* doctrinal sharpening in `V44`
* operationalization in `V46`
* no reopening of `V43`

## 1. Claimed planning impact

The imported narrative claims updates to:

* `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`
* `docs/DRAFT_STRUCTURAL_REASONING_ASSESSMENT_SPEC_v0.md`
* `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`
* `docs/DRAFT_BENCHMARKING_META_MODULE_SPEC_v0.md`
* `docs/DRAFT_PROCEDURAL_DEPTH_FIDELITY_BENCHMARK_SPEC_v0.md`

Those planning changes sharpen the doctrinal split between:

* horizontal action continuity / plan-spine fidelity
* vertical semantic decomposition / active-step compilation fidelity
* reintegration fidelity after local descent

## 2. Claimed code/package impact

The imported narrative claims a bounded proto-module under `packages/adeu_benchmarking`
with:

* benchmark family/projection substrate artifacts
* one hierarchical procedural-depth projection
* deterministic canonicalization/materialization helpers
* deterministic gold-trace derivation
* deterministic metrics and diagnostic scoring
* schema export support

It also claims repo wiring via:

* `Makefile` bootstrap addition for `packages/adeu_benchmarking[dev]`

## 3. Claimed artifact family

The imported narrative claims the following candidate artifact families:

* `benchmark_family_spec@1`
* `benchmark_projection_spec@1`
* `benchmark_execution_context@1`
* `benchmark_metrics_report@1`
* `benchmark_diagnostic_report@1`
* `benchmark_validation_report@1`
* `procedural_depth_instance@1`
* `procedural_depth_gold_trace@1`
* `procedural_depth_run_trace@1`

The procedural-depth benchmark is claimed as a tiny hierarchical `3x3` reference
chain with four canonical cases:

* `clean_success`
* `vertical_active_step_undercompilation`
* `horizontal_plan_spine_failure`
* `reintegration_failure`

## 4. Claimed verification

The imported narrative claims:

* targeted package pytest over `packages/adeu_benchmarking/tests`
* deterministic schema export checking
* small replayable fixtures under `packages/adeu_benchmarking/tests/fixtures/v46a/`
  and `v46b/`
* no full-repo `make check`

## 5. Maintainer intake interpretation

This claim bundle is useful because it is aimed at the correct still-pending family
pair:

* `V44` for doctrinal structure
* `V46` for benchmark substrate and projection implementation

But the imported narrative over-claims some delivered surfaces. The stronger record of
what was actually imported is the unpacked source payload in this intake pack, not the
claim text alone.
