# Draft ADEU ProgramBench Python Reconstruction Realization PB-PY-0-A Implementation Mapping v0

Status: support / slice mapping for planned `PB-PY-0-A`.

Authority layer: support.

This note is not a starter lock. The future active `PB-PY-0-A` starter should
come from the canonical `vNext+242` trio if no intervening arc claims that
number:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS242.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS242.md`
- `docs/ASSESSMENT_vNEXT_PLUS242_EDGES.md`

`PB-PY-0-A` should select only cleanroom reconstruction profile intake, concept
boundary seed rows, evidence source indexing, non-benchmark-truth guardrails,
and a local fixture contract. It should not create Python realization records,
generate code, run ProgramBench, instantiate a fixture, integrate an official
runner, handle hidden tests, score benchmarks, rank models, or select a later
family.

## Selected Surfaces

- `programbench_cleanroom_reconstruction_profile@1`
- `program_odeu_concept_boundary_seed@1`
- `programbench_cleanroom_evidence_source_index@1`
- `programbench_reconstruction_non_authority_guardrail@1`
- `programbench_local_cleanroom_fixture_contract@1`

## Package Scope

Expected implementation files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/cleanroom_reconstruction.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`

Expected schema files:

- `packages/adeu_benchmarking/schema/programbench_cleanroom_reconstruction_profile.v1.json`
- `packages/adeu_benchmarking/schema/program_odeu_concept_boundary_seed.v1.json`
- `packages/adeu_benchmarking/schema/programbench_cleanroom_evidence_source_index.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_non_authority_guardrail.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_cleanroom_fixture_contract.v1.json`
- `spec/programbench_cleanroom_reconstruction_profile.schema.json`
- `spec/program_odeu_concept_boundary_seed.schema.json`
- `spec/programbench_cleanroom_evidence_source_index.schema.json`
- `spec/programbench_reconstruction_non_authority_guardrail.schema.json`
- `spec/programbench_local_cleanroom_fixture_contract.schema.json`

Expected tests and fixtures:

- `packages/adeu_benchmarking/tests/test_cleanroom_reconstruction_pb_py_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus242/programbench_cleanroom_reconstruction_profile_v242_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus242/program_odeu_concept_boundary_seed_v242_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus242/programbench_cleanroom_evidence_source_index_v242_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus242/programbench_reconstruction_non_authority_guardrail_v242_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus242/programbench_local_cleanroom_fixture_contract_v242_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus242/programbench_cleanroom_reconstruction_v242_reject_*.json`

## Output Contract

`PB-PY-0-A` outputs:

1. cleanroom reconstruction profile;
2. program ODEU concept boundary seed;
3. evidence source index with cleanroom visibility classes;
4. non-authority / non-benchmark-truth guardrail;
5. local cleanroom fixture contract, but no fixture implementation;
6. deferred handoff notes for `PB-PY-0-B` and `PB-PY-0-C`.

`PB-PY-0-A` non-outputs:

- `ConceptRealizationRecord@1`;
- `PythonReconstructionPlan@1`;
- generated Python code;
- local fixture implementation;
- official ProgramBench runner integration;
- official ProgramBench task execution;
- hidden-test handling;
- original-source stores, decompilation stores, internet stores, or external
  repository stores;
- benchmark scoring, model ranking, or benchmark truth.

## Cleanroom Reconstruction Profile

Minimum profile fields:

- `profile_ref`
- `profile_kind`
- `program_family_ref`
- `source_index_refs`
- `concept_boundary_seed_refs`
- `phase_rows`
- `cleanroom_visibility_posture`
- `public_descriptor_observation_refs`
- `allowed_inference_source_refs`
- `forbidden_inference_source_refs`
- `worker_probe_posture`
- `local_development_posture`
- `evaluation_oracle_posture`
- `postmortem_posture`
- `benchmark_truth_posture`
- `implementation_authority_posture`
- `limitation_note`

Minimum `benchmark_truth_posture` values:

- `not_benchmark_truth`
- `public_descriptor_context_only`
- `local_fixture_research_only`
- `official_benchmark_authority_required`

## Concept Boundary Seed

Minimum seed row fields:

- `concept_seed_ref`
- `concept_id`
- `concept_label`
- `concept_boundary_posture`
- `concept_role`
- `boundary_outline_advisory`
- `positive_example_labels`
- `negative_example_labels`
- `nearest_confusable_concept_ids`
- `required_witness_kind_refs`
- `invalid_witness_kind_refs`
- `distinguishing_question_rows`
- `source_refs`
- `later_realization_posture`
- `implementation_authority_posture`
- `limitation_note`

Minimum seed concept ids:

- `program_behavior`
- `command`
- `subcommand`
- `cli_flag`
- `positional_argument`
- `stdin_input`
- `stdout_output`
- `stderr_diagnostic`
- `exit_code`
- `config_file`
- `environment_variable`
- `default_value`
- `precedence_rule`
- `parser_error`
- `runtime_error`
- `generated_output_artifact`
- `filesystem_side_effect`
- `probe_log`

Minimum `concept_boundary_posture` values:

- `boundary_seeded_incomplete`
- `boundary_context_only`
- `boundary_requires_later_realization`
- `boundary_not_claimed_for_task`

Seed rows are review inventory pressure only. They do not prove a task contains
the concept and do not authorize Python realization.

The boundary-outline fields are advisory seed material, not a full
`ConceptBoundary@1` implementation. They should still provide enough shape for
later `PB-PY-0-B` realization rows to distinguish nearby concepts. For example,
`stderr_diagnostic` may list normal stdout output, parser errors, and runtime
errors as confusables, require stdout/stderr split and exit-code witnesses, and
ask whether diagnostic text is observed on stderr rather than stdout.

## Evidence Source Index

Minimum source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `phase_visibility`
- `cleanroom_visibility_class`
- `source_currentness`
- `source_presence_posture`
- `source_access_posture`
- `worker_visibility_posture`
- `inference_admissibility_posture`
- `postmortem_admissibility_posture`
- `benchmark_truth_posture`
- `limitation_note`

Minimum `cleanroom_visibility_class` values:

- `cleanroom_visible`
- `worker_generated_probe`
- `worker_generated_submission`
- `evaluation_oracle_hidden`
- `forbidden_original_source`
- `forbidden_decompilation`
- `forbidden_internet_lookup`
- `forbidden_external_repo`
- `forbidden_host_secret`
- `forbidden_docker_socket`
- `support_context_only`
- `public_descriptor_context`
- `postmortem_only`

Validation rule:

```text
if cleanroom_visibility_class starts with forbidden_:
  worker_visibility_posture == not_worker_visible
  inference_admissibility_posture == forbidden_for_inference
  source_access_posture != registered_or_mounted_for_worker
```

Forbidden inference stores must be operationally unreachable during
`inference_phase`, not merely classified after exposure. Reject rows where a
forbidden source is registered, mounted, queried, worker-visible, or otherwise
available to the worker during inference.

Public ProgramBench descriptor rows must include source URL / retrieval posture
and remain `public_descriptor_context` with advisory-only,
not-used-as-evaluation-truth benchmark posture.

## Fixture Contract

Minimum fixture contract fields:

- `fixture_id`
- `reference_executable_ref`
- `usage_docs_ref`
- `allowed_inference_sources`
- `forbidden_inference_sources`
- `worker_visible_files`
- `worker_hidden_files`
- `probe_allowed_commands`
- `network_policy`
- `source_visibility_policy`
- `expected_submission_shape`
- `evaluation_oracle_posture`
- `non_benchmark_truth_posture`
- `fixture_implementation_posture`
- `limitation_note`

Required posture:

```text
fixture_implementation_posture = contract_only_no_fixture_implemented_by_pb_py_0a
non_benchmark_truth_posture = local_fixture_contract_not_benchmark_truth
```

## Guardrail

Minimum guardrail fields:

- `guardrail_ref`
- `source_refs`
- `forbidden_inference_actions`
- `forbidden_downstream_actions`
- `required_later_authority_refs`
- `benchmark_truth_posture`
- `implementation_posture`
- `python_realization_posture`
- `fixture_implementation_posture`
- `official_programbench_posture`
- `future_family_selection_posture`
- `limitation_note`

Reference rows should use:

- `benchmark_truth_posture = no_benchmark_truth_claimed_by_pb_py_0a`
- `implementation_posture = no_implementation_performed_by_pb_py_0a`
- `python_realization_posture = no_python_realization_records_created_by_pb_py_0a`
- `fixture_implementation_posture = no_fixture_implemented_by_pb_py_0a`
- `official_programbench_posture = no_official_programbench_participation_by_pb_py_0a`
- `future_family_selection_posture = no_future_family_selected_by_pb_py_0a`

## Required Reject Fixtures

Reject fixtures should include:

- hidden tests listed as inference evidence;
- forbidden original source marked worker-visible;
- forbidden evidence registered, mounted, queried, or exposed during inference;
- public ProgramBench descriptor marked benchmark truth;
- public descriptor row missing advisory/context-only posture;
- local probe pass marked hidden-test equivalence;
- inference, local development, evaluation, and postmortem phases collapsed into
  one visibility posture;
- fixture contract row that instantiates a fixture;
- concept seed row treated as Python realization authority;
- `ConceptRealizationRecord@1` shipped inside `PB-PY-0-A`;
- `python_reconstruction_plan@1` shipped inside `PB-PY-0-A`;
- `python_realization_witness_template@1` shipped inside `PB-PY-0-A`;
- `programbench_local_cleanroom_fixture@1` shipped inside `PB-PY-0-A`;
- `programbench_reconstruction_comparison_packet@1` shipped inside `PB-PY-0-A`;
- `programbench_probe_equivalence_audit@1` shipped inside `PB-PY-0-A`;
- official ProgramBench runner integration claimed;
- generated Python code claimed;
- benchmark score or model ranking claimed.

## Deferred To Later Slice Or Family

- `PB-PY-0-B`:
  - concept realization records;
  - Python realization overlay;
  - Python reconstruction plan;
  - witness templates.
- `PB-PY-0-C`:
  - local fixture instance;
  - A/B/C comparison packet;
  - probe equivalence audit;
  - family closeout alignment.
- Later family:
  - official ProgramBench participation;
  - hidden evaluator result governance;
  - broad conceptual broker implementation;
  - V86/V87/V88 meta-loop continuations.
