# Architecture ADEU ProgramBench Local Cleanroom Matrix Inclusion Family v0

Status: architecture / decomposition note for planned
`PB-MATRIX-INCLUSION-0`.

Authority layer: architecture / decomposition.

This note decomposes the local matrix-inclusion family after
`PB-CASE-EXPANSION-0`. It does not authorize implementation, local execution,
batch execution, scoring, official ProgramBench participation, hidden-test
handling, model ranking, submission, commit, merge, release, or future-family
selection by itself.

## Family Thesis

`PB-CASE-EXPANSION-0` created a local cleanroom case-supply lifecycle:

```text
case expansion request
  -> source pool manifest
  -> local blueprint / evidence / probe / oracle / contamination rows
  -> local case lineage registration
  -> readiness summary
  -> pressure-only matrix candidate handoff
```

`PB-MATRIX-INCLUSION-0` asks the next bounded question:

```text
Can a ready expanded local case lineage be admitted into a local matrix
revision as an accounting member, without running the case or interpreting
any result?
```

The family exists because matrix inclusion is a distinct authority step. A
ready local case lineage is not automatically a matrix member, and a matrix
member is not automatically executed, scored, projected, submitted, or treated
as benchmark evidence.

## Relationship To Prior Families

`PB-MATRIX-INCLUSION-0` consumes prior families only as released lineage and
constraint:

- `PB-PY-0`: cleanroom concept / Python realization substrate;
- `PB-ADAPTER-0`: task-visible evidence and access membrane;
- `PB-RECON-0`: local reconstruction workbench law;
- `PB-ATTEMPT-0`: attempt lifecycle law;
- `PB-TRIAL-0`: single local trial specimen law;
- `PB-RETRY-0`: one bounded retry governance;
- `PB-MATRIX-0`: local matrix accounting doctrine and non-score posture;
- `PB-CASE-EXPANSION-0`: ready local case lineage supply and pressure-only
  matrix candidate handoff.

It may constrain matrix inclusion based on that lineage. It may not mint
execution, scoring, benchmark truth, baseline comparison, model ranking,
official participation, or future-family authority.

## Authority Boundary

`PB-MATRIX-INCLUSION-0` may govern:

- local matrix inclusion request posture;
- candidate intake from released case-expansion handoff rows;
- candidate lineage eligibility for matrix revision;
- matrix control continuity;
- inclusion/amendment planning;
- local matrix case delta accounting;
- comparability and contamination delta reviews;
- inclusion decision records for local accounting only;
- matrix revision registration;
- readiness and handoff pressure after inclusion;
- family closeout alignment.

`PB-MATRIX-INCLUSION-0` may not govern:

- local case execution;
- probe execution;
- batch command execution;
- local trial dispatch;
- retry dispatch;
- candidate implementation materialization;
- result projection;
- matrix result summary;
- benchmark score, pass rate, solve rate, success rate, or official success
  rate;
- baseline comparison;
- model ranking or leaderboard standing;
- official ProgramBench runner/evaluator integration;
- hidden-test handling, inference, or equivalence;
- official submission authority;
- future-family selection.

## Core Circuit

```text
released case-expansion handoff
  -> matrix inclusion request
  -> candidate intake
  -> lineage eligibility review
  -> inclusion control contract
  -> matrix amendment plan
  -> case delta manifest
  -> comparability delta review
  -> contamination delta review
  -> inclusion decision record
  -> matrix revision registration
  -> revision readiness summary
  -> pressure-only post-inclusion handoff
  -> family closeout alignment
```

## Slice A: Intake And Eligibility

`PB-MATRIX-INCLUSION-0-A` should make candidate inclusion reviewable without
including cases yet.

Selected surfaces:

- `programbench_local_matrix_inclusion_request@1`
- `programbench_local_matrix_candidate_intake@1`
- `programbench_local_matrix_inclusion_eligibility_review@1`
- `programbench_local_matrix_inclusion_control_contract@1`
- `programbench_local_matrix_inclusion_non_authority_guardrail@1`

The slice should answer:

```text
Which released local case lineages are recordable and eligible candidates for
later local matrix revision review?
```

It should not answer:

```text
Which cases are included in a revised matrix?
What result did any case get?
Should any worker run?
What benchmark score did the matrix achieve?
```

## Slice B: Amendment And Inclusion Decision

`PB-MATRIX-INCLUSION-0-B` should create the local matrix amendment basis.

Selected surfaces:

- `programbench_local_matrix_amendment_plan@1`
- `programbench_local_matrix_case_delta_manifest@1`
- `programbench_local_matrix_comparability_delta_review@1`
- `programbench_local_matrix_contamination_delta_review@1`
- `programbench_local_matrix_inclusion_decision_record@1`

The slice should decide inclusion only as local accounting membership for a
declared matrix revision. It should not run cases, project outcomes, summarize
results, or score anything.

## Slice C: Revision Registration And Closeout

`PB-MATRIX-INCLUSION-0-C` should register the revised local matrix membership
and close the family.

Selected surfaces:

- `programbench_local_matrix_revision_registration@1`
- `programbench_local_matrix_revision_readiness_summary@1`
- `programbench_local_matrix_post_inclusion_handoff@1`
- `programbench_local_matrix_inclusion_family_closeout_alignment@1`

The slice should emit pressure-only handoff rows for later families, such as
future batch execution governance or future local result projection review,
without selecting those families.

## Invariants

- A ready expanded local case lineage is not automatically a matrix member.
- A local matrix member is not automatically executed.
- A local matrix member is not a result projection.
- Matrix inclusion is an amendment to exactly one released base matrix
  revision and exactly one proposed revision candidate.
- The base revision, proposed revision, prior membership manifest, proposed
  membership manifest, and revision delta must be hash-bound.
- Local matrix membership is not benchmark score, solve rate, pass rate,
  success rate, official success rate, model score, leaderboard standing, or
  baseline comparison.
- Matrix inclusion must preserve the released cleanroom source boundary,
  contamination posture, oracle/probe coverage, and non-representative
  benchmark posture of every included case.
- Matrix inclusion must preserve or explicitly account for matrix-control
  continuity: horizon, worker/model profile posture, tool policy, probe
  basis, sandbox/write-scope posture, and non-ranking posture.
- Inclusion counts are inventory/accounting only.
- Handoff pressure is not future-family selection.

## Matrix Identity Discipline

`PB-MATRIX-INCLUSION-0` should treat matrix identity as force-bearing. An
inclusion request that says only "add these cases" is under-specified. It
must bind:

```text
base_matrix_ref
base_matrix_revision_ref
base_matrix_revision_hash
target_matrix_revision_candidate_ref
target_matrix_revision_candidate_hash
prior_membership_manifest_hash
proposed_membership_manifest_hash
revision_delta_hash
```

This keeps inclusion from becoming a floating list of case lineages. Every
later amendment plan, inclusion decision, and revision registration should
trace back to the same base revision and proposed revision candidate.

## Inclusion Reason Discipline

Inclusion decisions can silently encode performance strategy if their reasons
are unconstrained. This family should allow governance/accounting reasons such
as:

- `lineage_eligible`
- `dedupe_blocked`
- `contamination_blocked`
- `comparability_blocked`
- `matrix_capacity_deferred`
- `horizon_mismatch_deferred`
- `missing_readiness_refs_blocked`

It should reject performance-selection reasons such as:

- `expected_to_pass`
- `expected_failure`
- `model_performs_well`
- `improves_score`
- `benchmark_representative`
- `leaderboard_relevant`
- `baseline_improving`

The same doctrine applies to rationale rows, summaries, and handoff rows.

## No Contamination Transfer By Summary

Hidden, forbidden, postmortem-only, evaluator-derived, source-derived,
decompilation-derived, internet-derived, or external-repo-derived material
must not enter the matrix through labels, rationale rows, decision rows,
summaries, handoff pressure, or redacted rows that preserve identifying
details.

## Deferred Seams

The following seams remain future-family-only unless separately selected:

- executing included cases;
- batch execution over a revised matrix;
- local result projection for included cases;
- local matrix summary after execution;
- benchmark-result and benchmark-score governance;
- baseline comparison governance;
- model-ranking or leaderboard governance;
- official ProgramBench participation;
- official runner/evaluator integration;
- hidden evaluator result governance;
- generated official submission review;
- second retry or retry-chain governance;
- natural task-to-program-profile inference;
- generalized conceptual broker implementation;
- multi-language realization overlays;
- V86, V87, and V88 continuations;
- product, graph-memory, release, or recursive-policy work.
