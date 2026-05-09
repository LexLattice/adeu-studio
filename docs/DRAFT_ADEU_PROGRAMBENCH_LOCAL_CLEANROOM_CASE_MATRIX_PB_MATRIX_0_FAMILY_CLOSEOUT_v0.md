# Draft ADEU ProgramBench Local Cleanroom Case Matrix PB-MATRIX-0 Family Closeout v0

Status: family closeout record after `vNext+262` / `PB-MATRIX-0-C` merged on
`main`.

Authority layer: closeout evidence on `main`.

This note closes `PB-MATRIX-0` as the local cleanroom case-matrix accounting
family. It does not authorize local case execution, batch command execution,
candidate materialization, official ProgramBench participation, official task
execution, official runner integration, official evaluator integration,
hidden-test handling, hidden-test inference, hidden-test equivalence, original
source lookup, decompilation, internet lookup inside ProgramBench tasks,
external repository lookup, benchmark submission, benchmark scoring, benchmark
truth, pass rate, solve rate, success rate, model ranking, leaderboard
standing, generated official submissions, official submission authority,
second retry authority, retry-chain authority, runtime transition, product
authorization, graph-memory authority, release authority, recursive policy
amendment, or future-family selection.

## Family-State Marker

```json
{
  "schema": "pb_matrix_0_family_closeout_state@1",
  "family": "PB-MATRIX-0",
  "phase": "family_closed_on_main",
  "closed_by_arc": "vNext+262",
  "closed_by_merge_commit": "93f80ea35618fac3a428fb954d8afa37410a60f6",
  "family_alignment_artifact": "apps/api/fixtures/benchmarking/vnext_plus262/programbench_local_case_matrix_family_closeout_alignment_v262_reference.json",
  "authoritative_scope": "local_programbench_cleanroom_case_matrix_accounting_only",
  "future_family_authority": "none"
}
```

## Closed Slice Ladder

| Slice | Global arc | Closed surface | Closeout evidence |
|---|---|---|---|
| `PB-MATRIX-0-A` | `vNext+260` | matrix request, inclusion manifest, lineage eligibility review, control contract, and non-authority guardrail | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS260.md`; `artifacts/agent_harness/v260/evidence_inputs/pb_matrix_0a_matrix_intake_closeout_evidence_v260.json` |
| `PB-MATRIX-0-B` | `vNext+261` | result projection, observation ledger, coverage register, and contamination register | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS261.md`; `artifacts/agent_harness/v261/evidence_inputs/pb_matrix_0b_projection_closeout_evidence_v261.json` |
| `PB-MATRIX-0-C` | `vNext+262` | local matrix summary, post-matrix handoff, and family closeout alignment | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS262.md`; `artifacts/agent_harness/v262/evidence_inputs/pb_matrix_0c_matrix_closeout_evidence_v262.json` |

## Shipped Surface Set

`PB-MATRIX-0` shipped these `adeu_benchmarking` local cleanroom case-matrix
surfaces:

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

The family stayed in `packages/adeu_benchmarking` and did not become an
official ProgramBench runner, solver, evaluator integration, hidden-test
interface, benchmark submission path, benchmark scoring path, model-ranking
system, batch execution system, product runtime surface, graph-memory
authority surface, release authority lane, or recursive-policy amendment path.

## Alignment Judgment

`PB-MATRIX-0-A` created the non-executing matrix intake boundary:

- one matrix request over released local cleanroom case lineages;
- case candidate rows with explicit trial/retry lineage refs and boundary
  hashes;
- lineage eligibility review;
- matrix control contract;
- non-authority guardrail.

It kept matrix inclusion distinct from local execution, benchmark scoring, or
model ranking. It rejected unreleased, support-only, contaminated,
hidden-test-derived, official-evaluator-derived, original-source-derived,
decompilation-derived, internet-derived, external-repo-derived, and
postmortem-only cases. It kept aggregate count posture as inventory/accounting
only and defaulted the matrix to non-representative local smoke/accounting
scope.

`PB-MATRIX-0-B` projected released local outcomes into a common local matrix
vocabulary:

- per-case result projection from released trial/retry rows;
- observation ledger;
- coverage register;
- contamination register.

It kept projection derived from released local evidence rather than new
outcome truth. Review hardening bound retry-settlement projections to the
settlement refs admitted by A, required gap refs to match row order without
runtime sorting normalization, partitioned blocked and local observation rows,
kept coverage local-only, and redacted contamination detail.

`PB-MATRIX-0-C` summarized and closed the local matrix:

- local matrix summary;
- post-matrix handoff;
- family closeout alignment.

Review hardening kept closeout field names aligned with the locked
`programbench_post_case_matrix_handoff@1` surface, removed redundant
summary/contamination overlap checks, and required family closeout to account
for the exact A/B/C closed slice sequence and shipped record shapes.

The three slices align:

- only released local cleanroom trial/retry case lineages can enter the matrix;
- A inclusion is not execution, batch execution, benchmark scoring, or model
  ranking authority;
- B projection derives from released local rows and cannot mint new outcome
  truth;
- every A-included case must have one B projection row or an explicit
  projection gap;
- coverage denominator remains declared local matrix cases only;
- contamination rows remain redacted and fail closed;
- C summary consumes released A/B basis before validating;
- local complete posture requires no projection gaps, clean contamination, no
  missing local coverage, and no unresolved blockers;
- aggregate counts remain local accounting only and cannot become pass rate,
  solve rate, success rate, benchmark score, official success rate, model
  score, or leaderboard metric;
- post-matrix handoff rows are pressure-only and non-selecting;
- family closeout closes exactly `PB-MATRIX-0-A/B/C`;
- official ProgramBench participation, official runner/evaluator integration,
  hidden tests, source lookup, benchmark submission, benchmark scoring, model
  ranking, generated official submissions, unbounded command execution, batch
  execution authority, second retry authority, retry-chain authority, runtime
  transition, product authority, graph-memory authority, release authority,
  recursive-policy authority, and future-family selection remain unselected.

## Closed Boundary

The family now gives the repo a bounded local case-matrix accounting lifecycle:

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

That lifecycle is local only. It does not grant local case execution authority,
batch execution authority, benchmark truth, benchmark score, pass rate, solve
rate, success rate, model ranking, official submission authority, official
ProgramBench runner/evaluator integration, hidden-test handling, hidden-test
equivalence, future-family selection, product authority, graph-memory
authority, release authority, or recursive-policy authority.

## Deferred Seams

The following seams remain deliberately unselected by this closeout:

- local case expansion governance;
- batch execution governance;
- model comparison and model-ranking governance;
- benchmark-result and benchmark-score governance;
- official ProgramBench participation governance;
- official runner/evaluator integration;
- hidden evaluator result governance;
- generated official submission review;
- second retry authority and retry-chain governance;
- natural task-to-program-profile inference;
- broader conceptual broker implementation;
- multi-language realization overlays;
- V86/V87/V88 continuations;
- product, graph-memory, release, or recursive-policy work.

## Final Family Decision

- family decision:
  - `PB_MATRIX_0_CLOSED_LOCAL_CLEANROOM_CASE_MATRIX_ACCOUNTING_ONLY`
- rationale:
  - `PB-MATRIX-0` now has a complete A/B/C ladder on `main`;
  - the family consumes released local cleanroom case lineages from prior
    adapter/workbench/attempt/trial/retry law without widening their
    authority;
  - the shipped lifecycle can select eligible local cases, preserve shared
    controls, project released local outcomes, account for local observations,
    coverage, and contamination, summarize the declared local matrix, and
    emit pressure-only handoff rows;
  - the shipped lifecycle cannot claim benchmark truth, official ProgramBench
    success, hidden-test equivalence, model ranking, official submission
    authority, batch execution authority, retry-chain authority, or
    future-family selection;
  - future work requires a new selector or canonical lock.
