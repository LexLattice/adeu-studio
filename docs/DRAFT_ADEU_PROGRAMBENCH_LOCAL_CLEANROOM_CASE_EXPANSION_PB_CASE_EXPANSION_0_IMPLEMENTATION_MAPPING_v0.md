# Draft ADEU ProgramBench Local Cleanroom Case Expansion PB-CASE-EXPANSION-0 Implementation Mapping v0

Status: support / implementation mapping record for planned
`PB-CASE-EXPANSION-0`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`PB-CASE-EXPANSION-0` family into likely package, schema, validator, fixture,
artifact, and evidence work so the family can be reviewed before the first
active slice lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v83.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_FAMILY_CLOSEOUT_v0.md`
- earlier ProgramBench family closeouts from `PB-PY-0` through `PB-RETRY-0`

## 1. Family Intent

`PB-CASE-EXPANSION-0` should add local cleanroom case-expansion governance
over released ProgramBench substrate without turning it into:

- official ProgramBench participation, official task execution, official
  runner integration, official evaluator integration, benchmark submission,
  benchmark scoring, benchmark truth, hidden-test inference,
  hidden-test equivalence, model ranking, leaderboard standing, pass rate,
  solve rate, success rate, or baseline-relative scoring;
- batch execution over local cases;
- local trial dispatch;
- candidate implementation materialization;
- original source lookup, decompilation, internet lookup, external source
  repository lookup, Docker socket access, or host-secret access;
- generated official submissions or official solver outputs;
- arbitrary command execution outside a released local sandbox;
- product authority, graph-memory authority, recursive policy amendment, PR
  creation, commit, merge, or release;
- any future-family selection.

The implementation target is a typed local case-expansion family that can
represent:

- local case expansion requests;
- source pool manifests;
- expansion eligibility reviews;
- expansion control contracts;
- expansion non-authority guardrails;
- later local case blueprints;
- later cleanroom evidence packs;
- later local probe contracts;
- later oracle boundaries;
- later contamination screens;
- later local case lineage registrations;
- later expansion readiness summaries;
- later matrix candidate handoffs;
- later family closeout alignment.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_benchmarking`
  - ProgramBench-shaped local cleanroom case-expansion models, enums,
    validators, and schema exports.
- logical module:
  - `adeu_benchmarking.programbench_cleanroom_case_expansion`
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity.
- `apps/api/fixtures/benchmarking/vnext_plus263/`
  - likely future reference and reject fixtures for `PB-CASE-EXPANSION-0-A`,
    if that slice is selected after review.

Avoid `programbench_runner`, `programbench_eval`, `programbench_solver`,
`programbench_submitter`, `programbench_scoreboard`,
`programbench_leaderboard`, `programbench_batch_runner`, and
`programbench_baseline_scorer` names in this family.

Expected starter implementation surfaces, when the first slice begins:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_case_expansion.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_case_expansion_pb_case_expansion_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`

If later slices need generic benchmark suite orchestration, that split should
be selected by a future family.

## 3. Candidate Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `programbench_local_case_expansion_request@1` | `PB-CASE-EXPANSION-0-A` | one local case expansion candidate over released substrate |
| `programbench_local_case_source_pool_manifest@1` | `PB-CASE-EXPANSION-0-A` | row-shaped allowed/forbidden source pool inventory with identity and visibility posture |
| `programbench_local_case_expansion_eligibility_review@1` | `PB-CASE-EXPANSION-0-A` | eligibility / blocker review for candidate case ideas and source pools |
| `programbench_local_case_expansion_control_contract@1` | `PB-CASE-EXPANSION-0-A` | controls for source visibility, derivation, candidate count, blueprinting, execution deferral, and non-ranking posture |
| `programbench_local_case_expansion_non_authority_guardrail@1` | `PB-CASE-EXPANSION-0-A` | guardrail preventing expansion rows from becoming execution, scoring, official, or ranking authority |
| `programbench_local_case_blueprint@1` | `PB-CASE-EXPANSION-0-B` | bounded blueprint for one local cleanroom case candidate |
| `programbench_local_case_cleanroom_evidence_pack@1` | `PB-CASE-EXPANSION-0-B` | cleanroom evidence rows, source witnesses, and derivation hashes |
| `programbench_local_case_probe_contract@1` | `PB-CASE-EXPANSION-0-B` | local probe plan/expectation contract without execution authority |
| `programbench_local_case_oracle_boundary@1` | `PB-CASE-EXPANSION-0-B` | local oracle boundary and non-hidden-test equivalence posture |
| `programbench_local_case_contamination_screen@1` | `PB-CASE-EXPANSION-0-B` | hidden/forbidden/source-derived/evaluator-derived contamination screen |
| `programbench_local_case_lineage_registration@1` | `PB-CASE-EXPANSION-0-C` | registration of validated local case lineage for later review |
| `programbench_local_case_expansion_readiness_summary@1` | `PB-CASE-EXPANSION-0-C` | summary of ready, blocked, and deferred expanded cases |
| `programbench_local_case_matrix_candidate_handoff@1` | `PB-CASE-EXPANSION-0-C` | pressure-only handoff toward later local matrix inclusion or batch governance |
| `programbench_local_case_expansion_family_closeout_alignment@1` | `PB-CASE-EXPANSION-0-C` | family closeout alignment without future-family authority |

`PB-CASE-EXPANSION-0-A` should ship only request, source pool manifest,
eligibility review, control contract, guardrail, schema export, validators,
and fixtures. It should not ship blueprints, evidence packs, probe contracts,
oracle boundaries, contamination screens, lineage registrations, readiness
summaries, handoffs, family closeout, benchmark scores, baseline comparisons,
model rankings, hidden-test handling, official runner integration, generated
official submissions, batch execution, or trial execution.

## 4. Source Classes

The family should consume concrete source refs from:

- `PB-MATRIX-0` family closeout and implementation surfaces:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_FAMILY_CLOSEOUT_v0.md`
  - `apps/api/fixtures/benchmarking/vnext_plus262/programbench_local_case_matrix_family_closeout_alignment_v262_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus262/programbench_local_case_matrix_summary_v262_reference.json`
  - `apps/api/fixtures/benchmarking/vnext_plus262/programbench_post_case_matrix_handoff_v262_reference.json`
- `PB-TRIAL-0` and `PB-RETRY-0` family closeouts as released local case
  lineage substrate;
- `PB-ATTEMPT-0`, `PB-RECON-0`, `PB-ADAPTER-0`, and `PB-PY-0` family
  closeouts as inherited cleanroom law;
- support doctrine:
  - `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
  - `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
  - `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
  - `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
  - `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`

Globs are discovery instructions, not evidence sources. Only observed
concrete files, hash-bound local source rows, or explicitly recorded
descriptor observations may become source rows.

## 5. Shared Vocabulary

Minimum expansion phases:

- `expansion_request_phase`
- `source_pool_phase`
- `eligibility_review_phase`
- `control_contract_phase`
- `case_blueprint_phase`
- `cleanroom_evidence_pack_phase`
- `probe_contract_phase`
- `oracle_boundary_phase`
- `contamination_screen_phase`
- `case_lineage_registration_phase`
- `readiness_summary_phase`
- `matrix_candidate_handoff_phase`

Minimum source pool visibility postures:

- `cleanroom_visible`
- `support_context_only`
- `auditor_only_exclusion`
- `hidden_or_forbidden`
- `postmortem_only`
- `unknown_not_indexed`
- `declared_absent`

Minimum candidate case eligibility postures:

- `eligible_for_later_blueprint_review`
- `blocked_missing_source_identity`
- `blocked_support_context_only`
- `blocked_hidden_or_forbidden_source`
- `blocked_official_evaluator_source`
- `blocked_source_lookup_or_decompilation`
- `blocked_internet_or_external_repo_source`
- `blocked_postmortem_only`
- `blocked_by_contamination`
- `blocked_by_execution_authority_claim`
- `blocked_by_benchmark_score_claim`
- `blocked_duplicate_existing_lineage_without_rationale`
- `future_family_only`

Minimum expansion horizons:

- `local_smoke_case_expansion`
- `local_regression_case_expansion`
- `local_coverage_probe_case_expansion`
- `local_research_case_expansion`
- `not_representative_benchmark_sample`

## 6. Cross-Slice Validation Expectations

The family should validate:

- A requires released `PB-MATRIX-0` closeout lineage before any matrix-driven
  expansion pressure can be accepted;
- A source pool manifests list concrete source refs and hashes, not globs;
- A requires case selection horizon, selection rationale rows, bias posture,
  diversity posture, dedupe policy, and non-representative posture;
- A rejects hidden, forbidden, postmortem-only, source-derived,
  decompilation-derived, internet-derived, external-repo-derived, and
  official-evaluator-derived sources as expansion evidence;
- A rejects hidden/forbidden source names, paths, excerpts, test names,
  semantic summaries, or derived facts in visible advisory rows;
- A rejects derived-summary laundering from forbidden, hidden,
  postmortem-only, source-derived, evaluator-derived, or auditor-only sources
  into visible labels, case ideas, obligations, probe expectations, or oracle
  claims;
- A rejects candidate case ideas that duplicate existing released local case
  lineages unless duplication is explicitly allowed by the expansion horizon;
- A controls cannot grant blueprint authority beyond later B review, local
  execution, batch execution, scoring, baseline comparison, model ranking, or
  official ProgramBench authority;
- A rejects B/C artifact kinds;
- B requires released A refs;
- B blueprints must trace to A-eligible candidate case ideas;
- B evidence packs must contain cleanroom-visible witnesses and derivation
  hashes;
- B evidence packs must bind behavior obligations to source witnesses through
  obligation basis rows with support strength and unresolved counterevidence;
- B probe contracts are plan-only and cannot execute commands;
- B probe contracts use argv-shaped planned command templates, still with
  execution deferred;
- B oracle boundaries must distinguish local expected behavior from
  hidden-test equivalence;
- B oracle boundaries carry local-oracle-not-task-truth posture and scope
  hashes;
- B contamination screens fail closed on any hidden/forbidden/source-derived
  exposure;
- C requires released A/B refs;
- C lineage registration requires passed contamination screen and complete
  evidence pack/probe/oracle rows;
- C lineage registration carries component hashes for blueprint, evidence
  pack, probe contract, oracle boundary, and contamination screen;
- C readiness summaries cannot mark a case ready with unresolved blockers,
  contamination, missing source identity, missing probe contract, or missing
  oracle boundary;
- C readiness summaries carry ready-count, denominator, and
  non-representativeness posture;
- C handoffs are pressure-only and cannot select matrix inclusion, batch
  execution, official participation, scoring, or future family;
- C family closeout closes exactly `PB-CASE-EXPANSION-0-A/B/C`.

## 7. Validation And Fixture Strategy

For `PB-CASE-EXPANSION-0-A`, reference fixtures should include:

- one expansion request with a local smoke expansion horizon;
- one source pool manifest with cleanroom-visible and excluded rows;
- one eligibility review with eligible and blocked candidate case ideas;
- one control contract preserving source visibility and execution deferral;
- one non-authority guardrail.

Reject fixtures should include:

- hidden-test-derived source marked eligible;
- official-evaluator-derived source marked eligible;
- support-only source marked eligible;
- source pool row with hidden/forbidden path or test name in visible summary;
- request that authorizes local execution or batch execution;
- request that claims baseline score, pass rate, solve rate, success rate, or
  model ranking;
- case idea using globs rather than concrete source refs;
- duplicate "new" case without explicit smoke/regression rationale;
- candidate label revealing a hidden test name or original source function
  name;
- B/C artifact shape present in A fixture.

For `PB-CASE-EXPANSION-0-B`, later fixtures should include:

- one local case blueprint from an A-eligible case idea;
- one cleanroom evidence pack with source witnesses and hashes;
- one probe contract with no execution authority;
- one oracle boundary with local-only expectation posture;
- one contamination screen.

Reject fixtures should include:

- blueprint from an A-blocked source;
- evidence pack with forbidden source names, paths, excerpts, test names, or
  derived facts;
- behavior obligation without source-witness basis rows;
- probe contract that runs commands;
- probe contract with free-form shell string instead of argv-shaped template;
- oracle boundary claiming hidden-test equivalence;
- oracle boundary claiming local oracle as official ProgramBench task truth;
- contamination screen marked clean despite hidden/source exposure.

For `PB-CASE-EXPANSION-0-C`, later fixtures should include:

- one lineage registration for a validated expanded local case;
- one readiness summary;
- one pressure-only matrix candidate handoff;
- one family closeout alignment.

Reject fixtures should include:

- lineage registration without passed B contamination screen;
- readiness marked ready with missing probe contract or oracle boundary;
- ready count phrased as pass rate, solve rate, success rate, or benchmark
  subset coverage;
- handoff that directly includes the case in a matrix;
- handoff that grants batch execution, scoring, official participation, or
  future-family selection.

## 8. Non-Outputs

`PB-CASE-EXPANSION-0` must not output:

- official ProgramBench runner/evaluator integration;
- hidden-test handling or hidden-test inference;
- official benchmark submission;
- benchmark score, baseline result, leaderboard, or model-ranking surfaces;
- generated official submissions;
- batch command execution over cases;
- local trial dispatch;
- candidate implementation materialization;
- second retry or retry-chain authority;
- source lookup, decompilation, internet lookup, external repo lookup, Docker
  socket, or host-secret access;
- product, graph-memory, release, or recursive-policy authority;
- future-family selection.

## 9. Recommended Slice Order

1. `PB-CASE-EXPANSION-0-A`: expansion request, source pool, eligibility,
   controls, guardrail.
2. `PB-CASE-EXPANSION-0-B`: blueprint, evidence pack, probe contract, oracle
   boundary, contamination screen.
3. `PB-CASE-EXPANSION-0-C`: lineage registration, readiness summary,
   pressure-only handoff, family closeout.

Proceed to `PB-CASE-EXPANSION-0-A` only after this family mapping is reviewed.
