# Draft ADEU ProgramBench Local Cleanroom Case Matrix PB-MATRIX-0 Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-MATRIX-0`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`PB-MATRIX-0` family into likely package, schema, validator, fixture, artifact,
and evidence work so the family can be reviewed before the first active slice
lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v82.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`

## 1. Family Intent

`PB-MATRIX-0` should add a local cleanroom case-matrix governance layer over
released local case lineages without turning it into:

- official ProgramBench participation, official task execution, official
  runner integration, official evaluator integration, benchmark submission,
  benchmark scoring, benchmark truth, hidden-test inference,
  hidden-test equivalence, model ranking, or leaderboard standing;
- batch execution over local cases;
- second retry authority or retry-chain authority;
- original source lookup, decompilation, internet lookup, external source
  repository lookup, Docker socket access, or host-secret access;
- generated official submissions or official solver outputs;
- arbitrary command execution outside a released local sandbox;
- product authority, graph-memory authority, recursive policy amendment, PR
  creation, commit, merge, or release;
- `V86`, `V87`, `V88`, canonical implementation-lock review, official
  ProgramBench participation, or any other future-family selection.

The implementation target is a typed local matrix family that can represent:

- local case matrix requests;
- case inclusion manifests;
- case lineage eligibility reviews;
- local matrix control contracts;
- local matrix non-authority guardrails;
- later case result projections;
- later local matrix observation ledgers;
- later matrix coverage registers;
- later matrix contamination registers;
- later local matrix summaries;
- later post-matrix handoffs;
- later matrix family closeout alignment.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_benchmarking`
  - ProgramBench-shaped local cleanroom case-matrix models, enums,
    validators, and schema exports.
- logical module:
  - `adeu_benchmarking.programbench_cleanroom_matrix`
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity.
- `apps/api/fixtures/benchmarking/vnext_plus260/`
  - likely future reference and reject fixtures for `PB-MATRIX-0-A`, if that
    slice is selected after review.

Avoid `programbench_runner`, `programbench_eval`, `programbench_solver`,
`programbench_submitter`, `programbench_scoreboard`,
`programbench_leaderboard`, and `programbench_batch_runner` names in this
family. Those names imply official benchmark, solving, evaluation, submission,
ranking, or execution authority that the local matrix family does not select.

Expected starter implementation surfaces, when the first slice begins:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_matrix.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_pb_matrix_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`

If later slices need generic benchmark suite orchestration beyond
ProgramBench-shaped local cleanroom matrices, that split should be selected by
a future family.

## 3. Candidate Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `programbench_local_case_matrix_request@1` | `PB-MATRIX-0-A` | one local matrix candidate over released case lineages |
| `programbench_local_case_inclusion_manifest@1` | `PB-MATRIX-0-A` | row-shaped candidate case list, origin posture, released lineage refs, boundary hashes, and exclusion posture |
| `programbench_local_case_lineage_eligibility_review@1` | `PB-MATRIX-0-A` | inclusion eligibility / blocker review for each case lineage |
| `programbench_local_case_matrix_control_contract@1` | `PB-MATRIX-0-A` | shared controls for profile, tools, probes, visibility, sandbox/write scope, comparability, aggregate counts, and non-ranking posture |
| `programbench_local_case_matrix_non_authority_guardrail@1` | `PB-MATRIX-0-A` | guardrail preventing matrix rows from becoming official benchmark, ranking, execution, or retry-chain authority |
| `programbench_local_case_matrix_result_projection@1` | `PB-MATRIX-0-B` | projection of released per-case local trial/retry/attempt/workbench posture into matrix vocabulary |
| `programbench_local_case_matrix_observation_ledger@1` | `PB-MATRIX-0-B` | local observation rows across included cases without benchmark score or model ranking |
| `programbench_local_case_matrix_coverage_register@1` | `PB-MATRIX-0-B` | local coverage / missing evidence register for included cases |
| `programbench_local_case_matrix_contamination_register@1` | `PB-MATRIX-0-B` | contamination, exclusion, and forbidden-source exposure register |
| `programbench_local_case_matrix_summary@1` | `PB-MATRIX-0-C` | local-only matrix summary with no benchmark truth |
| `programbench_post_case_matrix_handoff@1` | `PB-MATRIX-0-C` | pressure-only handoff to later review surfaces |
| `programbench_local_case_matrix_family_closeout_alignment@1` | `PB-MATRIX-0-C` | family closeout alignment without future-family authority |

`PB-MATRIX-0-A` should ship only matrix request, inclusion manifest, lineage
eligibility review, control contract, guardrail, schema export, validators,
and fixtures. It should not ship result projections, observation ledgers,
coverage registers, contamination registers, matrix summaries, handoffs,
family closeout, benchmark scores, model rankings, hidden-test handling,
official runner integration, generated official submissions, batch execution,
or second retry authority.

## 4. Source Classes

The family should consume concrete source refs from:

- `PB-RETRY-0` family closeout and implementation surfaces:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_FAMILY_CLOSEOUT_v0.md`
  - `apps/api/fixtures/benchmarking/vnext_plus259/programbench_local_retry_family_closeout_alignment_v259_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus259/programbench_local_retry_outcome_audit_v259_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus259/programbench_local_retry_delta_observation_summary_v259_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus259/programbench_local_retry_remand_settlement_v259_reference.json`
- `PB-TRIAL-0` family closeout and implementation surfaces:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
  - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_family_closeout_alignment_v256_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_outcome_audit_v256_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_observation_summary_v256_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_remand_decision_v256_reference.json`
- earlier ProgramBench family closeouts as lineage context:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
  - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
  - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
  - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- support doctrine:
  - `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
  - `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
  - `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
  - `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
  - `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`
  - `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`

Globs are discovery instructions, not evidence sources. Only observed
concrete files or explicitly recorded descriptor observations may become
source rows.

## 5. Shared Matrix Vocabulary

Minimum matrix phases:

- `matrix_request_phase`
- `case_inclusion_phase`
- `lineage_eligibility_phase`
- `control_contract_phase`
- `result_projection_phase`
- `observation_ledger_phase`
- `coverage_register_phase`
- `contamination_register_phase`
- `matrix_summary_phase`
- `post_matrix_handoff_phase`

Minimum case inclusion postures:

- `eligible_for_local_matrix_inclusion`
- `blocked_unreleased_lineage`
- `blocked_missing_family_closeout`
- `blocked_by_contamination`
- `blocked_by_hidden_or_forbidden_source`
- `blocked_by_official_evaluator_source`
- `blocked_by_source_lookup_or_decompilation`
- `blocked_by_model_ranking_claim`
- `support_context_only`
- `future_family_only`

Minimum matrix horizons:

- `local_smoke_matrix`
- `local_regression_matrix`
- `local_coverage_probe_matrix`
- `local_research_matrix`
- `not_representative_benchmark_sample`

Minimum aggregate count postures:

- `local_inventory_count_only`
- `local_case_posture_count_only`
- `coverage_accounting_only`
- `not_benchmark_score`

Forbidden aggregate postures:

- `benchmark_score`
- `pass_rate`
- `model_score`
- `leaderboard_metric`
- `official_success_rate`

Minimum matrix result postures:

- `local_case_resolved`
- `local_case_remanded`
- `local_case_retry_settled`
- `local_case_retry_unresolved`
- `local_case_blocked`
- `local_case_inconclusive`
- `local_case_not_projected`
- `not_benchmark_truth`

## 6. Cross-Slice Validation Expectations

The family should validate:

- `PB-MATRIX-0-A` requires released `PB-RETRY-0` and `PB-TRIAL-0` family
  closeout alignment refs before any retry/trial lineage can be matrix-ready;
- every A bundle resolves to one `case_matrix_ref`;
- A matrix request declares `matrix_horizon`, `matrix_max_case_count`, and
  non-representative / non-benchmark posture;
- case inclusion manifests list concrete case candidate refs and released
  lineage refs, not globs;
- case inclusion manifests use row-shaped `matrix_case_candidate_row` entries
  with lineage refs and cleanroom boundary hashes;
- every included case resolves to released local cleanroom lineage from
  adapter, workbench, attempt, trial, and optional retry surfaces;
- unreleased, contaminated, hidden-test-derived, official-evaluator-derived,
  original-source-derived, decompilation-derived, internet-derived,
  external-repo-derived, postmortem-only, and support-only cases cannot be
  marked eligible;
- inclusion manifests separate included cases, blocked cases, deferred cases,
  and support-only cases;
- matrix control contracts bind worker profile, tool policy, probe basis,
  sandbox/write scope, cleanroom visibility, and non-ranking posture;
- matrix control contracts include aggregate count posture and
  representativeness posture;
- matrix requests using multiple worker/model profiles require explicit
  non-ranking and comparability-control posture and still cannot emit ranking;
- A rejects B/C artifact kinds;
- B requires released A refs;
- B result projections require released per-case source rows and cannot invent
  outcome posture;
- B result projections carry source result refs, source result hashes,
  projection rule refs, currentness, and `projection_is_not_new_truth_posture`;
- B observation ledgers reject benchmark score, hidden-test equivalence,
  official score, leaderboard, model-ranking, and cross-worker superiority
  language;
- B coverage registers distinguish local coverage from hidden-test coverage;
- B coverage registers include coverage denominator posture and local basis
  scope;
- B contamination registers fail closed on any hidden/forbidden exposure;
- B contamination registers include redaction policy and contamination detail
  posture that prevent source-identifying leakage;
- C requires released A/B refs;
- C summaries carry aggregate count posture, representativeness posture,
  matrix scope statement, and not-benchmark-score statement;
- C summaries cannot mark the matrix as official benchmark success;
- C handoffs are pressure-only and cannot select official participation,
  hidden evaluator governance, model ranking, batch execution, or future
  family;
- C family closeout closes exactly `PB-MATRIX-0-A/B/C`.

## 7. Validation And Fixture Strategy

For `PB-MATRIX-0-A`, reference fixtures should include:

- one matrix request over released local trial/retry lineage;
- one inclusion manifest with an eligible local case and one blocked/support
  row;
- one lineage eligibility review carrying local-only eligibility;
- one matrix control contract preserving shared controls and non-ranking
  posture;
- one non-authority guardrail.

Reject fixtures should include:

- hidden-test-derived case marked eligible;
- official-evaluator-derived case marked eligible;
- unreleased case lineage marked eligible;
- contaminated case marked eligible;
- model-ranking claim in control contract;
- benchmark-score claim in matrix request;
- representative benchmark subset claim from a local smoke/research matrix;
- multiple model profiles without comparability controls;
- support-only case counted as included;
- B/C artifact shape present in A fixture.

For `PB-MATRIX-0-B`, later fixtures should include:

- result projection over released A matrix case refs;
- observation ledger rows without ranking language;
- coverage register with local coverage only;
- contamination register with clean and blocked examples.

Reject fixtures should include:

- pass rate, solve rate, success rate, model wins, beats baseline,
  leaderboard-like, official-like score, or representative benchmark subset
  language;
- hidden/forbidden source exposed through contamination row details;
- hidden-test coverage counted as local coverage;

For `PB-MATRIX-0-C`, later fixtures should include:

- local matrix summary;
- pressure-only post-matrix handoff;
- family closeout alignment;
- rejects for benchmark score, model ranking, official success, and future
  family selection;
- rejects for aggregate local counts phrased as pass rate, solve rate, success
  rate, benchmark-like result, or representative ProgramBench subset.

## 8. Non-Outputs

`PB-MATRIX-0` must not output:

- official ProgramBench runner/evaluator integration;
- hidden-test handling or hidden-test inference;
- official benchmark submission;
- benchmark score, leaderboard, or model-ranking surfaces;
- generated official submissions;
- batch command execution over cases;
- second retry or retry-chain authority;
- source lookup, decompilation, internet lookup, external repo lookup, Docker
  socket, or host-secret access;
- product, graph-memory, release, or recursive-policy authority;
- future-family selection.

## 9. Recommended Slice Order

1. `PB-MATRIX-0-A`: matrix request, case inclusion, eligibility, controls,
   guardrail.
2. `PB-MATRIX-0-B`: per-case result projection, observation ledger, coverage,
   contamination.
3. `PB-MATRIX-0-C`: matrix summary, pressure-only handoff, family closeout.

Proceed to `PB-MATRIX-0-A` only after this family mapping is reviewed.
