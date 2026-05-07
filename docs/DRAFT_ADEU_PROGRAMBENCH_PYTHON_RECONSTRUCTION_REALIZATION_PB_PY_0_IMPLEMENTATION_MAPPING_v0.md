# Draft ADEU ProgramBench Python Reconstruction Realization PB-PY-0 Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-PY-0`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`PB-PY-0` family into likely package, schema, validator, fixture, and evidence
work so the family can be reviewed before the first active slice lock is
accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v76.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V85_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/ADEU Conceptual-First Retrieval Pipeline v1.md`
- `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
- `artifacts/agent_harness/meta_loop_probes/SERIES_INTERPRETATION_v0.md`

## 1. Family Intent

`PB-PY-0` should add ProgramBench-shaped cleanroom reconstruction review
records without turning them into:

- official ProgramBench participation, benchmark submission, benchmark truth,
  hidden-test inference, or model ranking;
- original source lookup, decompilation, internet lookup, external source
  repository lookup, Docker socket access, or host-secret access;
- Python implementation generation, command execution, tool invocation,
  target mutation, or runtime transition;
- product authority, graph-memory authority, recursive policy amendment, PR
  creation, commit, merge, or release;
- `V86`, `V87`, `V88`, canonical implementation-lock review, or any other
  future-family selection.

The implementation target is a typed local cleanroom reconstruction family that
can represent:

- cleanroom reconstruction profiles;
- evidence source indexes with cleanroom visibility classes;
- concept boundary seed rows;
- non-authority / non-benchmark-truth guardrails;
- local cleanroom fixture contracts;
- later Python realization overlays;
- later local fixture and comparison packets.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_benchmarking`
  - benchmark-world / local fixture substrate, models, enums, validators, and
    schema exports for cleanroom reconstruction records.
- logical submodule:
  - `adeu_benchmarking.cleanroom_reconstruction`
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity.
- `apps/api/fixtures/benchmarking/vnext_plus242/`
  - reference and reject fixtures for the first bounded slice.

Avoid `programbench_runner`, `programbench_eval`, and `programbench_solver`
names in `PB-PY-0-A`. Those names imply official benchmark or solving
authority that the starter does not select.

Expected starter implementation surfaces, when the implementation slice begins:

- `packages/adeu_benchmarking/src/adeu_benchmarking/cleanroom_reconstruction.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_cleanroom_reconstruction_pb_py_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`

Expected starter schema files:

- `packages/adeu_benchmarking/schema/programbench_cleanroom_reconstruction_profile.v1.json`
- `packages/adeu_benchmarking/schema/program_odeu_concept_boundary_seed.v1.json`
- `packages/adeu_benchmarking/schema/programbench_cleanroom_evidence_source_index.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_non_authority_guardrail.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_cleanroom_fixture_contract.v1.json`

Expected mirror schema files follow the same names under `spec/`.

Expected later schema files:

- `packages/adeu_benchmarking/schema/concept_realization_record.v1.json`
- `packages/adeu_benchmarking/schema/python_reconstruction_realization_pack.v1.json`
- `packages/adeu_benchmarking/schema/python_reconstruction_plan.v1.json`
- `packages/adeu_benchmarking/schema/python_realization_witness_template.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_cleanroom_fixture.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_comparison_packet.v1.json`
- `packages/adeu_benchmarking/schema/programbench_probe_equivalence_audit.v1.json`
- `packages/adeu_benchmarking/schema/programbench_realization_family_closeout_alignment.v1.json`

## 3. Candidate Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `programbench_cleanroom_reconstruction_profile@1` | `PB-PY-0-A` | cleanroom-visible program behavior profile and phase posture |
| `program_odeu_concept_boundary_seed@1` | `PB-PY-0-A` | O-lane seed rows for program behavior concepts before language realization |
| `programbench_cleanroom_evidence_source_index@1` | `PB-PY-0-A` | row-shaped source visibility, currentness, allowed/forbidden inference source posture |
| `programbench_reconstruction_non_authority_guardrail@1` | `PB-PY-0-A` | guardrail preventing profile, public descriptor, fixture contract, and local probes from becoming benchmark truth or implementation authority |
| `programbench_local_cleanroom_fixture_contract@1` | `PB-PY-0-A` | law for a later local fixture without building the fixture instance |
| `concept_realization_record@1` | `PB-PY-0-B` | concept-to-language realization records |
| `python_reconstruction_realization_pack@1` | `PB-PY-0-B` | Python stdlib realization overlay |
| `python_reconstruction_plan@1` | `PB-PY-0-B` | later plan packet, not execution authority |
| `python_realization_witness_template@1` | `PB-PY-0-B` | witness templates for Python realization options |
| `programbench_local_cleanroom_fixture@1` | `PB-PY-0-C` | one local cleanroom fixture instance |
| `programbench_reconstruction_comparison_packet@1` | `PB-PY-0-C` | A/B/C local comparison packet |
| `programbench_probe_equivalence_audit@1` | `PB-PY-0-C` | local probe/equivalence audit, not hidden-test equivalence |
| `programbench_realization_family_closeout_alignment@1` | `PB-PY-0-C` | family closeout alignment without official benchmark authority |

`PB-PY-0-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement Python realization records,
generate code, run ProgramBench, run hidden tests, integrate an official
evaluator, mount original source stores, or create benchmark scores.

## 4. Source Classes

The family should consume concrete source refs from:

- `V85` family closeout:
  - `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v241/evidence_inputs/v85c_semantic_declaration_closeout_evidence_v241.json`
  - `apps/api/fixtures/repo_description/vnext_plus241/repo_semantic_declaration_family_closeout_alignment_v241_reference.json`
- V85 probe corpus:
  - `artifacts/agent_harness/meta_loop_probes/SERIES_INTERPRETATION_v0.md`
- post-`V85` planning:
  - `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V85_v0.md`
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v76.md`
- support doctrine:
  - `docs/support/ADEU Conceptual-First Retrieval Pipeline v1.md`
  - `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
  - `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
  - `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
  - `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
  - `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`
  - `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- public descriptor observations:
  - `https://benchlm.ai/blog/posts/programbench-cleanroom-coding-benchmark`
  - `https://benchlm.ai/benchmarks/programBench`

Globs are discovery instructions, not evidence sources. Only observed concrete
files or explicitly recorded public descriptor observations may become source
rows. Public ProgramBench descriptors are advisory context only.

## 5. Shared Phase Vocabulary

Minimum phase values:

- `inference_phase`
- `local_development_phase`
- `evaluation_phase`
- `postmortem_phase`

Minimum phase laws:

- `inference_phase` uses cleanroom-visible evidence only;
- `local_development_phase` may use worker-generated probes and tests, still
  without forbidden evidence;
- `evaluation_phase` may let hidden tests judge an artifact, but hidden tests
  remain external court and not inference evidence;
- `postmortem_phase` may inform harness research under development posture but
  may not retroactively admit hidden-test evidence into inference.

## 6. Shared Evidence Visibility Vocabulary

Minimum evidence visibility classes:

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

Operational rule:

```text
forbidden_* source rows must not be registered, mounted, queried, or exposed to
the worker during inference_phase.
```

## 7. Validation Expectations

The family should validate:

- all profile, source-index, seed, guardrail, and fixture-contract rows share
  consistent package / candidate lineage;
- public descriptors are advisory-only and include retrieval/source posture;
- forbidden inference stores are not worker-visible during inference;
- `PB-PY-0-A` rejects any `PB-PY-0-B` or `PB-PY-0-C` artifact kind;
- `PB-PY-0-B` requires released `PB-PY-0-A` refs;
- `PB-PY-0-B` rejects local fixture instances and any
  `python_reconstruction_plan@1` containing source code, executable file paths,
  shell commands, generated implementation artifacts, or fixture payloads;
- `PB-PY-0-C` requires released `PB-PY-0-A` and `PB-PY-0-B` refs;
- `PB-PY-0-C` rejects official ProgramBench source, evaluator, task, or hidden
  test refs as local fixture inputs;
- `PB-PY-0-C` marks comparisons contaminated or non-comparable when shared
  fixture, worker/model profile, budget, tool policy, cleanroom policy, probe
  budget, submission shape, or evaluation oracle differs outside the declared
  lane delta;
- hidden tests cannot appear as inference evidence;
- local probes cannot be claimed as hidden-test equivalence;
- fixture contract rows do not instantiate a fixture;
- Python realization rows do not ship before `PB-PY-0-B`;
- implementation, code generation, official runner integration, benchmark
  scoring, model ranking, release, graph authority, recursive policy amendment,
  and future-family selection remain absent.
