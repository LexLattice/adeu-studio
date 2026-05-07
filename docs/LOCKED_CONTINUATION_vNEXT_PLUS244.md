# LOCKED_CONTINUATION_vNEXT_PLUS244

## Status

Bounded starter lock draft for `PB-PY-0-C` (one local cleanroom fixture,
controlled A/B/C reconstruction comparison packet, local probe audit, and
family closeout alignment).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`PB-PY-0-C` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-PY-0`
- slice: `PB-PY-0-C`
- branch-local execution target: `arc/pb-py-0-c`

## Purpose

Freeze the bounded `PB-PY-0-C` starter slice so the repo can instantiate one
local cleanroom fixture under the released `PB-PY-0-A` fixture contract,
consume released `PB-PY-0-B` Python realization overlay rows, and compare
three local reconstruction lanes without claiming official ProgramBench truth.

`vNext+244` authorizes docs plus the next implementation path over the existing
repo-owned `adeu_benchmarking` package. It does not authorize official
ProgramBench tasks, official runner integration, benchmark submission,
benchmark scoring, benchmark truth, model ranking, hidden-test handling,
hidden-test inference, original source lookup, decompilation, internet lookup
inside ProgramBench tasks, external repository lookup, target mutation outside
the local fixture artifacts selected here, runtime transition, product
authorization, graph-memory authority, recursive policy amendment, or
future-family selection.

Controlling invariant:

```text
PB-PY-0-C may instantiate one synthetic/local cleanroom fixture and compare
local reconstruction lanes under same-condition controls, but a local fixture
is not official ProgramBench participation, a local probe pass is not
hidden-test equivalence, and a comparison packet is not model ranking or
benchmark truth.
```

## Instantiated Here

- `PB-PY-0-C` instantiates one bounded local fixture and comparison seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released A basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS242.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS242.md`
    - `docs/ASSESSMENT_vNEXT_PLUS242_EDGES.md`
    - `artifacts/agent_harness/v242/evidence_inputs/pb_py_0a_cleanroom_reconstruction_closeout_evidence_v242.json`
    - `apps/api/fixtures/benchmarking/vnext_plus242/programbench_cleanroom_reconstruction_profile_v242_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus242/program_odeu_concept_boundary_seed_v242_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus242/programbench_cleanroom_evidence_source_index_v242_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus242/programbench_reconstruction_non_authority_guardrail_v242_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus242/programbench_local_cleanroom_fixture_contract_v242_reference.json`
  - consumed released B basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS243.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS243.md`
    - `docs/ASSESSMENT_vNEXT_PLUS243_EDGES.md`
    - `artifacts/agent_harness/v243/evidence_inputs/pb_py_0b_python_realization_overlay_closeout_evidence_v243.json`
    - `apps/api/fixtures/benchmarking/vnext_plus243/concept_realization_record_v243_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus243/python_reconstruction_realization_pack_v243_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus243/python_reconstruction_plan_v243_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus243/python_realization_witness_template_v243_reference.json`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v76.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
  - emitted third-slice record shapes:
    - `programbench_local_cleanroom_fixture@1`
    - `programbench_reconstruction_comparison_packet@1`
    - `programbench_probe_equivalence_audit@1`
    - `programbench_realization_family_closeout_alignment@1`

## Required Starter Vocabulary

Minimum `programbench_local_cleanroom_fixture@1` fields:

- `fixture_ref`
- `fixture_contract_ref`
- `reference_executable_ref`
- `usage_docs_ref`
- `worker_visible_file_refs`
- `worker_hidden_file_refs`
- `allowed_probe_command_rows`
- `forbidden_source_rows`
- `fixture_origin_posture`
- `network_policy`
- `source_visibility_policy`
- `expected_submission_shape`
- `evaluation_oracle_rows`
- `local_fixture_scope_posture`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `limitation_note`

Required fixture posture:

```text
local_fixture_scope_posture = one_local_cleanroom_fixture_only
official_programbench_posture = no_official_programbench_participation_by_pb_py_0c
benchmark_truth_posture = local_fixture_research_only_not_benchmark_truth
```

Minimum `fixture_origin_posture` values:

- `synthetic_local_fixture`
- `repo_internal_fixture`
- `toy_cleanroom_fixture`
- `official_programbench_task_forbidden_in_pb_py_0c`

The fixture may include a local reference executable and local oracle rows only
if the released fixture contract authorizes them. It must not include official
ProgramBench tasks, hidden tests, original source, decompilation artifacts, or
external source repositories.

Minimum `programbench_reconstruction_comparison_packet@1` fields:

- `comparison_packet_ref`
- `fixture_ref`
- `comparison_control_rows`
- `comparison_lane_rows`
- `profile_refs`
- `realization_pack_refs`
- `witness_template_refs`
- `local_probe_refs`
- `comparison_scope_posture`
- `comparison_contamination_status`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `limitation_note`

Required comparison posture:

```text
comparison_scope_posture = local_fixture_research_comparison_only
comparison_contamination_status = same_condition_controls_closed
benchmark_truth_posture = not_benchmark_truth
model_ranking_posture = no_model_ranking_claimed_by_pb_py_0c
```

Required lane ids:

- `base_adeu_harness`
- `adeu_plus_conceptual_profile`
- `adeu_plus_conceptual_profile_plus_python_overlay`

Minimum `comparison_control_rows` fields:

- `shared_fixture_ref`
- `shared_model_or_worker_profile_ref`
- `shared_budget_policy`
- `shared_allowed_tool_policy`
- `shared_cleanroom_policy`
- `shared_probe_budget`
- `shared_submission_shape`
- `shared_evaluation_oracle_rows`
- `lane_difference_declaration`

The intended lane delta is only:

- `base_adeu_harness`: no conceptual profile and no Python overlay;
- `adeu_plus_conceptual_profile`: conceptual profile only;
- `adeu_plus_conceptual_profile_plus_python_overlay`: conceptual profile plus
  Python overlay.

If model, worker profile, budget, tool access, probe allowance, fixture,
submission shape, or evaluation oracle differs across lanes, the comparison
packet must mark the result contaminated or non-comparable rather than making a
clean lane-value claim.

Minimum `programbench_probe_equivalence_audit@1` fields:

- `audit_ref`
- `fixture_ref`
- `comparison_packet_ref`
- `local_probe_rows`
- `positive_observation_rows`
- `negative_observation_rows`
- `stdout_stderr_observation_rows`
- `exit_code_observation_rows`
- `filesystem_observation_rows`
- `known_limitation_rows`
- `hidden_test_equivalence_posture`
- `benchmark_truth_posture`
- `postmortem_feedback_posture`
- `limitation_note`

Required audit posture:

```text
hidden_test_equivalence_posture = local_probe_pass_not_hidden_test_equivalence
benchmark_truth_posture = local_audit_not_benchmark_truth
postmortem_feedback_posture = no_hidden_test_feedback_used_for_inference
```

Minimum `programbench_realization_family_closeout_alignment@1` fields:

- `family_closeout_ref`
- `family`
- `closed_slice_refs`
- `released_profile_refs`
- `released_source_index_refs`
- `released_concept_seed_refs`
- `released_fixture_contract_refs`
- `released_realization_pack_refs`
- `released_fixture_refs`
- `released_comparison_packet_refs`
- `released_audit_refs`
- `family_alignment_posture`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `future_family_selection_status`
- `limitation_note`

Required closeout-alignment posture:

```text
family_alignment_posture = pb_py_0_closed_local_research_fixture_only
official_programbench_posture = no_official_programbench_participation_by_pb_py_0
benchmark_truth_posture = no_benchmark_truth_claimed_by_pb_py_0
future_family_selection_status = no_future_family_selected_by_pb_py_0
```

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_cleanroom_fixture@1`
  - `programbench_reconstruction_comparison_packet@1`
  - `programbench_probe_equivalence_audit@1`
  - `programbench_realization_family_closeout_alignment@1`
- deterministic reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus244/`;
- validators that prove:
  - released `PB-PY-0-A` and `PB-PY-0-B` refs are required and resolve;
  - the fixture origin is synthetic, repo-internal, or toy local only;
  - official ProgramBench task refs, hidden tests, original source,
    decompilation artifacts, external repos, and internet lookup are rejected;
  - forbidden evidence is not worker-visible or inference-admissible;
  - comparison packets require same-condition controls;
  - contaminated comparison conditions are marked contaminated or
    non-comparable;
  - lane ids and lane-difference declarations preserve the intended A/B/C
    experimental delta;
  - local probe passes do not become hidden-test equivalence, benchmark truth,
    official score, or model ranking;
  - family closeout alignment closes only `PB-PY-0` as a local research
    fixture family and does not select official ProgramBench participation,
    V86, V87, V88, product, graph, release, or recursive-policy work.

## Deferred To Later Slice Or Family

- official ProgramBench participation and result governance;
- hidden evaluator feedback governance;
- broader conceptual broker implementation;
- multi-language realization overlays beyond Python;
- V86 obligation expansion / evidence contract / edge probe planning;
- V87 reviewer / auditor taskpacks;
- V88 deterministic closeout transition / remand routing;
- product, graph-memory, release, or recursive-policy work.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS244.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+244",
  "target_path": "PB-PY-0-C",
  "slice": "PB-PY-0-C",
  "family": "PB-PY-0",
  "branch_local_execution_target": "arc/pb-py-0-c",
  "target_scope": "one_local_cleanroom_fixture_and_controlled_comparison_slice",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "api_surfaces": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS242.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS243.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS242.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS243.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS242_EDGES.md",
    "docs/ASSESSMENT_vNEXT_PLUS243_EDGES.md"
  ],
  "planning_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v76.md",
    "docs/ARCHITECTURE_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_FAMILY_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0C_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "consumed_record_shapes": [
    "programbench_cleanroom_reconstruction_profile@1",
    "program_odeu_concept_boundary_seed@1",
    "programbench_cleanroom_evidence_source_index@1",
    "programbench_reconstruction_non_authority_guardrail@1",
    "programbench_local_cleanroom_fixture_contract@1",
    "concept_realization_record@1",
    "python_reconstruction_realization_pack@1",
    "python_reconstruction_plan@1",
    "python_realization_witness_template@1"
  ],
  "emitted_record_shapes": [
    "programbench_local_cleanroom_fixture@1",
    "programbench_reconstruction_comparison_packet@1",
    "programbench_probe_equivalence_audit@1",
    "programbench_realization_family_closeout_alignment@1"
  ],
  "forbidden_claims": [
    "official_programbench_task_used_as_local_fixture",
    "official_programbench_runner_integrated",
    "official_programbench_task_executed",
    "hidden_test_visible_to_worker",
    "hidden_test_inference",
    "hidden_test_equivalence_claimed",
    "original_source_lookup",
    "decompilation",
    "internet_lookup_for_task",
    "external_repo_lookup_for_task",
    "comparison_missing_same_condition_controls",
    "contaminated_comparison_marked_clean",
    "model_ranking_claimed",
    "benchmark_score_created",
    "benchmark_truth_claimed",
    "future_family_selection"
  ],
  "local_gate": "make arc-start-check ARC=244"
}
```
