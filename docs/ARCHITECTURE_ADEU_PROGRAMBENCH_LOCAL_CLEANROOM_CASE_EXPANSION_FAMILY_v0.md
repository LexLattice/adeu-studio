# Architecture ADEU ProgramBench Local Cleanroom Case Expansion Family v0

Status: architecture / decomposition note for planned
`PB-CASE-EXPANSION-0`.

Authority layer: architecture / decomposition.

This architecture note does not authorize official ProgramBench participation,
official task execution, official runner integration, official evaluator
integration, hidden-test handling, hidden-test inference, hidden-test
equivalence, original source lookup, decompilation, internet lookup inside
ProgramBench tasks, external repository lookup, benchmark submission,
benchmark scoring, benchmark truth, pass rate, solve rate, success rate,
baseline-relative result claims, model ranking, leaderboard standing,
generated official submissions, official submission authority, second retry
authority, retry-chain authority, batch command execution, target mutation
outside a released local sandbox/write scope, runtime transition, product
authority, graph-memory authority, recursive policy amendment, PR creation,
commit, merge, release, or future-family selection by itself.

## Family Thesis

`PB-MATRIX-0` created the typed lifecycle for local matrix accounting over
released local cleanroom case lineages:

```text
released local cleanroom case lineages
  -> matrix request
  -> case inclusion manifest
  -> lineage eligibility review
  -> matrix control contract
  -> local result projection
  -> observation ledger
  -> coverage register
  -> contamination register
  -> local matrix summary
  -> pressure-only handoff
  -> family closeout alignment
```

The next bottleneck is not benchmark scoring. It is increasing the small local
case supply without violating the cleanroom boundary:

```text
released ProgramBench cleanroom substrate
  -> case expansion request
  -> source pool manifest
  -> expansion eligibility review
  -> expansion control contract
  -> later case blueprint
  -> later cleanroom evidence pack
  -> later probe contract / oracle boundary
  -> later contamination screen
  -> later case lineage registration
  -> later matrix-candidate handoff
```

Controlling invariant:

```text
PB-CASE-EXPANSION-0 may govern new local cleanroom case lineages. It may not
run the cases, score them, compare them to baselines, claim official
ProgramBench standing, infer hidden-test behavior, rank models, or select a
future family.
```

## Relationship To `PB-MATRIX-0`

`PB-CASE-EXPANSION-0` consumes `PB-MATRIX-0` as the local matrix accounting
substrate:

- `programbench_local_case_matrix_request@1`
- `programbench_local_case_inclusion_manifest@1`
- `programbench_local_case_lineage_eligibility_review@1`
- `programbench_local_case_matrix_control_contract@1`
- `programbench_local_case_matrix_non_authority_guardrail@1`
- `programbench_local_case_matrix_result_projection@1`
- `programbench_local_case_matrix_observation_ledger@1`
- `programbench_local_case_matrix_coverage_register@1`
- `programbench_local_case_matrix_contamination_register@1`
- `programbench_local_case_matrix_summary@1`
- `programbench_post_case_matrix_handoff@1`
- `programbench_local_case_matrix_family_closeout_alignment@1`

The matrix lifecycle remains local accounting. It can exert pressure for local
case expansion, but it cannot by itself create new cases, execute cases,
score cases, compare models, or claim benchmark coverage.

## Relationship To Earlier ProgramBench Families

`PB-CASE-EXPANSION-0` inherits:

- cleanroom fixture and concept/realization substrate from `PB-PY-0`;
- task intake, visibility, probe observation, and case-packet law from
  `PB-ADAPTER-0`;
- workbench and local evidence law from `PB-RECON-0`;
- attempt lifecycle law from `PB-ATTEMPT-0`;
- single-trial specimen law from `PB-TRIAL-0`;
- retry governance law from `PB-RETRY-0`;
- matrix accounting law from `PB-MATRIX-0`.

These inputs constrain local case expansion. They do not grant official
benchmark authority, hidden-test inference authority, wider source
visibility, model ranking, baseline scoring, official submission authority, or
batch execution authority.

## Family Slices

### `PB-CASE-EXPANSION-0-A`: Expansion Intake And Source Pool Controls

Starter surfaces:

- `programbench_local_case_expansion_request@1`
- `programbench_local_case_source_pool_manifest@1`
- `programbench_local_case_expansion_eligibility_review@1`
- `programbench_local_case_expansion_control_contract@1`
- `programbench_local_case_expansion_non_authority_guardrail@1`

Purpose:

- record a request to expand the local cleanroom case supply;
- identify source pools and candidate case ideas;
- decide whether each source pool and case idea is eligible for later
  blueprinting;
- define shared controls for source visibility, source derivation, candidate
  selection, cleanroom boundaries, and non-authority posture;
- preserve that slice A does not create case blueprints, materialize fixture
  files, execute cases, run probes, score benchmarks, compare baselines, rank
  models, or select a future family.

Forbidden:

- official ProgramBench participation;
- official task execution;
- benchmark score or baseline-relative result;
- hidden-test handling;
- local trial execution;
- batch execution;
- case blueprint or case lineage registration;
- model ranking;
- second retry or retry-chain authority.

### `PB-CASE-EXPANSION-0-B`: Blueprint And Cleanroom Evidence Pack

Later surfaces:

- `programbench_local_case_blueprint@1`
- `programbench_local_case_cleanroom_evidence_pack@1`
- `programbench_local_case_probe_contract@1`
- `programbench_local_case_oracle_boundary@1`
- `programbench_local_case_contamination_screen@1`

Purpose:

- convert eligible A source pools and candidate ideas into bounded local case
  blueprints;
- preserve cleanroom evidence rows and source identity hashes;
- define local probe contracts without executing them;
- define oracle boundaries and expected local observations without claiming
  hidden-test equivalence;
- screen for hidden, forbidden, postmortem-only, source-derived,
  decompilation-derived, internet-derived, external-repo-derived, or
  official-evaluator-derived contamination.

Forbidden:

- local trial dispatch;
- command execution;
- batch execution;
- candidate implementation materialization;
- benchmark scoring;
- baseline comparison;
- model ranking;
- official evaluator contact;
- hidden-test inference.

### `PB-CASE-EXPANSION-0-C`: Case Lineage Registration And Handoff

Later surfaces:

- `programbench_local_case_lineage_registration@1`
- `programbench_local_case_expansion_readiness_summary@1`
- `programbench_local_case_matrix_candidate_handoff@1`
- `programbench_local_case_expansion_family_closeout_alignment@1`

Purpose:

- register validated local case lineages created by the expansion family;
- summarize readiness and blockers for later local matrix inclusion or later
  batch-execution governance;
- emit pressure-only handoff rows;
- close only `PB-CASE-EXPANSION-0`.

Forbidden:

- direct matrix inclusion authority;
- local trial dispatch;
- batch execution;
- benchmark score;
- official ProgramBench participation;
- baseline-relative result;
- model ranking;
- hidden evaluator governance;
- future-family selection.

## Cleanroom Source Law

`PB-CASE-EXPANSION-0` must keep these distinctions machine-checkable:

- cleanroom-visible source pool is not hidden-test evidence;
- source pool eligibility is not case blueprint readiness;
- case selection is not representative benchmark construction;
- duplicate smoke/regression case supply is not new benchmark coverage;
- case blueprint is not executed trial;
- local probe contract is not executed probe evidence;
- expected local output is not hidden-test equivalence;
- case lineage registration is not matrix inclusion authority;
- matrix candidate handoff is not batch execution authority;
- local case count is not benchmark coverage or score.

Named cleanroom law:

```text
No derived-summary laundering:
  forbidden, hidden, postmortem-only, source-derived, evaluator-derived,
  or auditor-only sources may not be transformed into visible advisory facts,
  candidate labels, behavior obligations, probe expectations, oracle boundary
  claims, or case-selection rationale.
```

Selection-governance law:

```text
New local case supply must declare selection horizon, rationale, bias posture,
diversity posture, dedupe policy, and overlap with existing released local
case lineages. Smoke/regression duplicates may be allowed only when declared
as such; they must not become representative benchmark coverage.
```

## Deferred Seams

The following seams remain future-family-only unless separately selected:

- local batch execution over expanded cases;
- baseline-relative local result governance;
- benchmark-result and benchmark-score governance;
- official ProgramBench participation;
- official runner/evaluator integration;
- hidden evaluator result governance;
- model-ranking or leaderboard governance;
- second retry or retry-chain governance;
- generated official submission review;
- natural task-to-program-profile inference;
- broader conceptual broker implementation;
- multi-language realization overlays;
- product, graph-memory, release, or recursive-policy work.
