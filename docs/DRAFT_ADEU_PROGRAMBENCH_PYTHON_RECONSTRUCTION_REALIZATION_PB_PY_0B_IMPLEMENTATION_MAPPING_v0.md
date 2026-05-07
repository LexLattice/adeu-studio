# Draft ADEU ProgramBench Python Reconstruction Realization PB-PY-0-B Implementation Mapping v0

Status: support / slice mapping for planned `PB-PY-0-B`.

Authority layer: support.

This note is not a starter lock. `PB-PY-0-B` should activate only after
`PB-PY-0-A` closes on `main` and a later canonical starter lock selects this
slice.

`PB-PY-0-B` should select only concept-to-Python realization overlay records,
Python reconstruction planning records, and witness-template rows. It should
not implement a local fixture, generate Python code, run ProgramBench, execute
official tasks, handle hidden tests, score benchmarks, rank models, or select a
future family.

## Selected Surfaces

- `concept_realization_record@1`
- `python_reconstruction_realization_pack@1`
- `python_reconstruction_plan@1`
- `python_realization_witness_template@1`

## Package Scope

Expected implementation files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/cleanroom_reconstruction.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`

Expected schema files:

- `packages/adeu_benchmarking/schema/concept_realization_record.v1.json`
- `packages/adeu_benchmarking/schema/python_reconstruction_realization_pack.v1.json`
- `packages/adeu_benchmarking/schema/python_reconstruction_plan.v1.json`
- `packages/adeu_benchmarking/schema/python_realization_witness_template.v1.json`
- `spec/concept_realization_record.schema.json`
- `spec/python_reconstruction_realization_pack.schema.json`
- `spec/python_reconstruction_plan.schema.json`
- `spec/python_realization_witness_template.schema.json`

Expected tests and fixtures:

- `packages/adeu_benchmarking/tests/test_cleanroom_reconstruction_pb_py_0b.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus243/concept_realization_record_v243_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus243/python_reconstruction_realization_pack_v243_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus243/python_reconstruction_plan_v243_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus243/python_realization_witness_template_v243_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus243/programbench_python_realization_v243_reject_*.json`

The `vNext+243` number is a planning placeholder only. A later starter lock
must bind the actual arc number.

## Consumed Released Basis

`PB-PY-0-B` should consume released `PB-PY-0-A` rows:

- `programbench_cleanroom_reconstruction_profile@1`
- `program_odeu_concept_boundary_seed@1`
- `programbench_cleanroom_evidence_source_index@1`
- `programbench_reconstruction_non_authority_guardrail@1`
- `programbench_local_cleanroom_fixture_contract@1`

No A-row becomes implementation authority, fixture authority, benchmark truth,
or code-generation authority by being consumed.

## Concept Realization Record

Minimum `concept_realization_record@1` fields:

- `realization_ref`
- `concept_seed_ref`
- `concept_id`
- `target_language`
- `realization_role`
- `canonical_instruction`
- `preferred_stdlib_surfaces`
- `implementation_patterns`
- `contraindicated_patterns`
- `boundary_conditions`
- `failure_modes`
- `required_witness_refs`
- `probe_template_refs`
- `example_snippets_advisory`
- `concept_definition_posture`
- `implementation_authority_posture`
- `limitation_note`

Minimum `target_language` values for this slice:

- `python`

Minimum `realization_role` values:

- `cli_argument_parsing`
- `stdin_stdout_stderr_io`
- `file_path_io`
- `config_data_loading`
- `environment_variable_loading`
- `precedence_resolution`
- `exit_code_behavior`
- `deterministic_output_ordering`
- `error_diagnostic_behavior`
- `generated_artifact_behavior`
- `filesystem_side_effect_behavior`

Required posture:

```text
concept_definition_posture = realization_option_not_concept_definition
implementation_authority_posture = no_implementation_authority_granted_by_pb_py_0b
```

## Python Realization Pack

Minimum `python_reconstruction_realization_pack@1` fields:

- `pack_ref`
- `target_language`
- `source_profile_refs`
- `concept_seed_refs`
- `realization_record_refs`
- `stdlib_surface_rows`
- `boundary_condition_rows`
- `failure_mode_rows`
- `witness_template_refs`
- `contraindicated_pattern_rows`
- `pack_scope_posture`
- `fixture_authority_posture`
- `benchmark_truth_posture`
- `implementation_authority_posture`
- `limitation_note`

Minimum stdlib surface vocabulary:

- `argparse`
- `sys_argv`
- `sys_stdin`
- `sys_stdout`
- `sys_stderr`
- `pathlib`
- `open`
- `json`
- `csv`
- `configparser`
- `tomllib`
- `os_environ`
- `glob`
- `text_binary_mode`
- `subprocess_for_probe_only`

`subprocess_for_probe_only` may appear only as a witness/probe surface. It must
not become ProgramBench execution authority or arbitrary command authority.
Stdlib surface rows and implementation-pattern rows should remain distinct:
stdlib rows name lawful Python library surfaces, while implementation patterns
describe advisory realization options for already-bounded concepts.

## Python Reconstruction Plan

Minimum `python_reconstruction_plan@1` fields:

- `plan_ref`
- `source_profile_refs`
- `realization_pack_refs`
- `concept_realization_refs`
- `planned_obligation_rows`
- `planned_witness_refs`
- `plan_scope_posture`
- `code_generation_posture`
- `execution_authority_posture`
- `fixture_authority_posture`
- `benchmark_truth_posture`
- `limitation_note`

Required posture:

```text
code_generation_posture = no_code_generated_by_pb_py_0b
execution_authority_posture = no_execution_authority_granted_by_pb_py_0b
fixture_authority_posture = no_fixture_implemented_by_pb_py_0b
benchmark_truth_posture = not_benchmark_truth
```

Validation rule:

```text
python_reconstruction_plan@1 MUST NOT contain source code, executable file
paths, shell commands, command invocations, generated implementation artifacts,
or fixture implementation payloads.
```

The plan may contain planned obligation rows, planned witness refs,
realization-pack refs, concept-realization refs, and limitations. Advisory code
snippets, if any, remain bounded inside realization records and must not be
treated as generated implementation.

## Witness Template

Minimum `python_realization_witness_template@1` fields:

- `witness_template_ref`
- `concept_id`
- `target_language`
- `realization_refs`
- `probe_kind`
- `probe_command_shape`
- `expected_observation_kind`
- `positive_witness_requirement`
- `negative_witness_requirement`
- `stdout_stderr_split_required`
- `exit_code_required`
- `filesystem_observation_required`
- `hidden_test_equivalence_posture`
- `execution_authority_posture`
- `limitation_note`

Minimum `probe_kind` values:

- `help_probe`
- `missing_value_probe`
- `invalid_flag_probe`
- `repeated_flag_probe`
- `stdin_stdout_probe`
- `stderr_diagnostic_probe`
- `exit_code_probe`
- `missing_file_probe`
- `malformed_config_probe`
- `deterministic_sorting_probe`
- `generated_file_probe`
- `directory_side_effect_probe`

Required posture:

```text
hidden_test_equivalence_posture = local_probe_not_hidden_test_equivalence
execution_authority_posture = probe_template_only_no_execution_by_pb_py_0b
```

## Required Reject Fixtures

Reject fixtures should include:

- realization record treating Python stdlib surface as the canonical concept;
- example snippet marked canonical implementation;
- reconstruction plan with generated code;
- reconstruction plan with executable file paths or shell commands;
- reconstruction plan with generated implementation artifacts;
- reconstruction plan granting execution authority;
- witness template claiming hidden-test equivalence;
- `subprocess_for_probe_only` used as arbitrary command execution authority;
- fixture implementation claimed in `PB-PY-0-B`;
- official ProgramBench runner integration claimed;
- benchmark score or model ranking claimed;
- hidden tests listed as inference evidence.

## Deferred To Later Slice Or Family

- `PB-PY-0-C`:
  - local cleanroom fixture instance;
  - A/B/C comparison packet;
  - local probe equivalence audit;
  - family closeout alignment.
- later family:
  - official ProgramBench participation;
  - hidden evaluator result governance;
  - broader conceptual broker implementation;
  - V86/V87/V88 meta-loop continuations.
