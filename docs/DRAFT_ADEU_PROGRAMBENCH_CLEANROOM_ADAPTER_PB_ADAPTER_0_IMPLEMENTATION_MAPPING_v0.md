# Draft ADEU ProgramBench Cleanroom Adapter PB-ADAPTER-0 Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-ADAPTER-0`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`PB-ADAPTER-0` family into likely package, schema, validator, fixture, and
evidence work so the family can be reviewed before the first active slice lock
is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v77.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`

## 1. Family Intent

`PB-ADAPTER-0` should add a ProgramBench-style cleanroom task adapter without
turning it into:

- official ProgramBench participation, official task execution, official
  runner integration, benchmark submission, benchmark scoring, benchmark
  truth, hidden-test inference, or model ranking;
- original source lookup, decompilation, internet lookup, external source
  repository lookup, Docker socket access, or host-secret access;
- implementation generation, generated official submissions, command
  execution authority, tool invocation authority, target mutation, or runtime
  transition;
- product authority, graph-memory authority, recursive policy amendment, PR
  creation, commit, merge, or release;
- `V86`, `V87`, `V88`, canonical implementation-lock review, official
  ProgramBench participation, or any other future-family selection.

The implementation target is a typed adapter family that can represent:

- task intake rows;
- task artifact manifests with stable identity witnesses;
- task visibility manifests;
- worker access contracts;
- adapter non-authority guardrails;
- later probe plans and observation logs;
- later reconstruction case packets and adapter readiness summaries.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_benchmarking`
  - benchmark-world cleanroom adapter models, enums, validators, and schema
    exports.
- logical module:
  - `adeu_benchmarking.programbench_cleanroom_adapter`
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity.
- `apps/api/fixtures/benchmarking/vnext_plus245/`
  - likely future reference and reject fixtures for `PB-ADAPTER-0-A`, if that
    slice is selected after review.

Avoid `programbench_runner`, `programbench_eval`, `programbench_solver`, and
`programbench_submitter` names in this family. Those names imply official
benchmark, solving, evaluation, or submission authority that the adapter does
not select.

Expected starter implementation surfaces, when the first slice begins:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_adapter.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_adapter_pb_adapter_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`

## 3. Candidate Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `programbench_cleanroom_task_intake@1` | `PB-ADAPTER-0-A` | ProgramBench-style task intake and origin posture without task execution |
| `programbench_task_artifact_manifest@1` | `PB-ADAPTER-0-A` | stable identity witnesses for task-visible artifacts, snapshots, and source set |
| `programbench_task_visibility_manifest@1` | `PB-ADAPTER-0-A` | source/file/store visibility and cleanroom exposure posture |
| `programbench_adapter_worker_access_contract@1` | `PB-ADAPTER-0-A` | worker-visible source, network, command, and forbidden-store access law |
| `programbench_adapter_non_authority_guardrail@1` | `PB-ADAPTER-0-A` | guardrail preventing adapter rows from becoming official benchmark authority |
| `programbench_adapter_probe_plan@1` | `PB-ADAPTER-0-B` | allowed local/reference probe plan under the access contract |
| `programbench_probe_observation_log@1` | `PB-ADAPTER-0-B` | CLI/help/stdio/exit-code observation rows |
| `programbench_io_artifact_observation_index@1` | `PB-ADAPTER-0-B` | generated files, stdout/stderr artifacts, and directory output observations |
| `programbench_filesystem_side_effect_observation@1` | `PB-ADAPTER-0-B` | filesystem side-effect observation rows |
| `programbench_reconstruction_case_packet@1` | `PB-ADAPTER-0-C` | bundled task intake, visibility, access, guardrail, and observation refs |
| `programbench_adapter_readiness_summary@1` | `PB-ADAPTER-0-C` | readiness / blocker / warning summary for later reconstruction review |
| `programbench_adapter_handoff@1` | `PB-ADAPTER-0-C` | post-adapter handoff pressure without selecting execution or evaluation |
| `programbench_cleanroom_adapter_family_closeout_alignment@1` | `PB-ADAPTER-0-C` | family closeout alignment without official benchmark authority |

`PB-ADAPTER-0-A` should ship only intake, manifest, access-contract,
guardrail, schema export, validators, and fixtures. It should not ship probe
observation rows, reconstruction case packets, readiness summaries, official
runner integration, hidden-test handling, benchmark scoring, generated
submissions, or model ranking.

## 4. Source Classes

The family should consume concrete source refs from:

- `PB-PY-0` family closeout:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
  - `apps/api/fixtures/benchmarking/vnext_plus244/programbench_realization_family_closeout_alignment_v244_reference.json`
  - `artifacts/agent_harness/v244/evidence_inputs/pb_py_0c_local_fixture_comparison_closeout_evidence_v244.json`
- `PB-PY-0` architecture and mapping:
  - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_FAMILY_v0.md`
  - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_IMPLEMENTATION_MAPPING_v0.md`
- post-`PB-PY-0` planning:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v77.md`
- support doctrine:
  - `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
  - `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
  - `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
  - `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
  - `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`
  - `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- public descriptor observations, if recorded:
  - advisory context only;
  - not benchmark truth;
  - not task truth;
  - not hidden-test evidence.

Globs are discovery instructions, not evidence sources. Only observed concrete
files or explicitly recorded descriptor observations may become source rows.

## 5. Shared Visibility Vocabulary

Minimum visibility classes:

- `cleanroom_visible`
- `worker_generated_probe`
- `worker_generated_submission`
- `reference_executable_observation`
- `public_descriptor_context`
- `support_context_only`
- `postmortem_only`
- `evaluation_oracle_hidden`
- `forbidden_original_source`
- `forbidden_decompilation`
- `forbidden_internet_lookup`
- `forbidden_external_repo`
- `forbidden_host_secret`
- `forbidden_docker_socket`

Minimum visibility basis values:

- `known_visible`
- `known_hidden`
- `known_forbidden`
- `known_support_only`
- `unknown_not_indexed`
- `declared_absent`

Operational rule:

```text
forbidden_* and evaluation_oracle_hidden stores must not be worker-visible
during inference_phase and must not be converted into cleanroom-visible
summaries for the worker.
```

## 6. Shared Phase Vocabulary

Minimum phase values:

- `intake_phase`
- `inference_phase`
- `probe_observation_phase`
- `evaluation_phase`
- `postmortem_phase`

Minimum phase laws:

- `intake_phase` records visibility and access policy only;
- `inference_phase` uses only cleanroom-visible sources authorized by the
  worker access contract;
- `probe_observation_phase` records allowed local/reference observations but
  does not claim hidden-test equivalence;
- `evaluation_phase` may be represented only as external court posture unless
  a later family authorizes more;
- `postmortem_phase` cannot retroactively admit hidden evidence into inference.

## 7. Cross-Slice Validation Expectations

The family should validate:

- all adapter rows share consistent candidate and task intake lineage;
- task artifact manifests bind reference executable, usage docs, visible input
  artifacts, source-set hash, observed-at or snapshot refs, origin posture, and
  ingestion method;
- `PB-ADAPTER-0-A` rejects `PB-ADAPTER-0-B/C` artifact kinds;
- `PB-ADAPTER-0-A` rejects manifests where forbidden stores are worker-visible
  during inference;
- `PB-ADAPTER-0-A` rejects hidden or forbidden evidence summarized into
  cleanroom-visible worker advisory text;
- `PB-ADAPTER-0-A` rejects worker access contracts that grant command execution
  or probe authority;
- `PB-ADAPTER-0-B` requires released `PB-ADAPTER-0-A` refs;
- `PB-ADAPTER-0-B` requires argv-shaped command contracts unless shell wrapping
  is explicitly declared with a reason;
- `PB-ADAPTER-0-B` rejects observation rows that cite hidden evaluator output
  as inference evidence;
- `PB-ADAPTER-0-C` requires released `PB-ADAPTER-0-A/B` refs;
- `PB-ADAPTER-0-C` rejects case packets that omit access contract or
  visibility manifest refs;
- local probe observations cannot be claimed as benchmark scores or hidden-test
  equivalence;
- readiness summaries with contamination status other than `clean` cannot be
  marked ready for later cleanroom reconstruction review;
- reconstruction case packets cannot include generated official submissions;
- readiness summaries cannot select official ProgramBench participation,
  implementation-lock review, or model ranking;
- command execution, tool invocation, target mutation, official runner
  integration, hidden-test handling, benchmark scoring, product authority,
  graph authority, release, recursive policy amendment, and future-family
  selection remain absent unless later selected by a separate lock.
