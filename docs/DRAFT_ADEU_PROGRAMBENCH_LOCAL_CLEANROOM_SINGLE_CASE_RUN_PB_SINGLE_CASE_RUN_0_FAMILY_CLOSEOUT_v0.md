# Draft ADEU ProgramBench Local Cleanroom Single Case Run PB-SINGLE-CASE-RUN-0 Family Closeout v0

Status: family closeout record after `vNext+271` / `PB-SINGLE-CASE-RUN-0-C`
merged on `main`.

Authority layer: closeout evidence on `main`.

This note closes `PB-SINGLE-CASE-RUN-0` as the local cleanroom single-case run
governance family. It does not authorize additional local case execution,
probe execution outside the captured specimen, batch command execution,
matrix execution, benchmark scoring, official ProgramBench participation,
official task execution, official runner integration, official evaluator
integration, hidden-test handling, hidden-test inference, hidden-test
equivalence, original source lookup, decompilation, internet lookup inside
ProgramBench tasks, external repository lookup, benchmark submission,
benchmark truth, pass rate, solve rate, success rate, baseline comparison,
model ranking, leaderboard standing, generated official submissions,
official submission authority, retry authority, second retry authority,
retry-chain authority, runtime transition, product authorization,
graph-memory authority, release authority, recursive policy amendment, or
future-family selection.

## Family-State Marker

```json
{
  "schema": "pb_single_case_run_0_family_closeout_state@1",
  "family": "PB-SINGLE-CASE-RUN-0",
  "phase": "family_closed_on_main",
  "closed_by_arc": "vNext+271",
  "closed_by_merge_commit": "7cb3ae5f8bd6f0e21b6e18e2823b9f15d828ee37",
  "family_alignment_artifact": "apps/api/fixtures/benchmarking/vnext_plus271/programbench_single_case_run_family_closeout_alignment_v271_reference.json",
  "authoritative_scope": "local_programbench_cleanroom_single_case_run_governance_only",
  "future_family_authority": "none"
}
```

## Closed Slice Ladder

| Slice | Global arc | Closed surface | Closeout evidence |
|---|---|---|---|
| `PB-SINGLE-CASE-RUN-0-A` | `vNext+269` | single-case run request, target selection, execution preflight, run control contract, and non-authority guardrail | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS269.md`; `artifacts/agent_harness/v269/evidence_inputs/pb_single_case_run_0a_closeout_evidence_v269.json` |
| `PB-SINGLE-CASE-RUN-0-B` | `vNext+270` | worker dispatch specimen, execution trace, probe observation bundle, candidate artifact capture, and lifecycle projection | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS270.md`; `artifacts/agent_harness/v270/evidence_inputs/pb_single_case_run_0b_closeout_evidence_v270.json` |
| `PB-SINGLE-CASE-RUN-0-C` | `vNext+271` | local outcome audit, observation summary, remand/acceptance decision, pressure-only handoff, and family closeout alignment | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS271.md`; `artifacts/agent_harness/v271/evidence_inputs/pb_single_case_run_0c_closeout_evidence_v271.json` |

## Shipped Surface Set

`PB-SINGLE-CASE-RUN-0` shipped these `adeu_benchmarking` local cleanroom
single-case run surfaces:

- `programbench_single_case_run_request@1`
- `programbench_single_case_target_selection@1`
- `programbench_single_case_execution_preflight@1`
- `programbench_single_case_run_control_contract@1`
- `programbench_single_case_run_non_authority_guardrail@1`
- `programbench_single_case_worker_dispatch_specimen@1`
- `programbench_single_case_execution_trace@1`
- `programbench_single_case_probe_observation_bundle@1`
- `programbench_single_case_candidate_artifact_capture@1`
- `programbench_single_case_lifecycle_projection@1`
- `programbench_single_case_local_outcome_audit@1`
- `programbench_single_case_run_observation_summary@1`
- `programbench_single_case_remand_or_acceptance_decision@1`
- `programbench_single_case_run_handoff@1`
- `programbench_single_case_run_family_closeout_alignment@1`

The family stayed in `packages/adeu_benchmarking` and did not become an
official ProgramBench runner, solver, evaluator integration, hidden-test
interface, benchmark submission path, benchmark scoring path, model-ranking
system, batch execution system, retry dispatcher, product runtime surface,
graph-memory authority surface, release authority lane, or recursive-policy
amendment path.

## Alignment Judgment

`PB-SINGLE-CASE-RUN-0-A` created the non-executing target-selection and
preflight boundary:

- one single-case run request;
- target selection bound to matrix-member, ready-expanded-case-lineage, or
  explicitly exceptional direct-adapter route;
- execution preflight;
- run control contract;
- non-authority guardrail.

It kept target selection and run controls separate from dispatch, command
execution, probe execution, candidate materialization, official ProgramBench
participation, benchmark scoring, baseline comparison, model ranking, and
future-family selection. It required matrix-origin targets to be included
members and kept direct adapter routes exceptional.

`PB-SINGLE-CASE-RUN-0-B` recorded the one bounded local specimen capture:

- worker dispatch specimen;
- execution trace;
- probe observation bundle;
- candidate artifact capture;
- lifecycle projection.

It required B-slice dispatch authority, exactly one dispatch specimen,
argv-shaped command rows, sandbox/tool/write-scope witness refs, passed
forbidden-content screening before candidate artifact capture, generated
artifact hash consistency, and lifecycle projection that remains non-new-truth
and non-hidden-test-equivalence.

`PB-SINGLE-CASE-RUN-0-C` audited and classified the captured specimen:

- local outcome audit;
- observation summary;
- remand/acceptance decision;
- pressure-only handoff;
- family closeout alignment.

Review hardening required blocked outcome postures to bind to matching blocked
statuses and matching blocker refs, added an artifact-capture blocker channel,
and expanded benchmark-language rejection for official-like-result and
hidden-test-equivalence phrases. Redundant-check removal suggestions were not
applied because the explicit bundle gates preserve cross-record fail-closed
acceptance semantics.

The three slices align:

- A target selection and preflight are not dispatch or execution authority;
- B consumes released A rows and requires B-slice dispatch authority before a
  specimen can be recorded;
- B specimen capture and lifecycle projection are not local outcome audit,
  acceptance, remand, retry, benchmark truth, or hidden-test equivalence;
- C consumes released A/B rows before it can audit the specimen;
- C local acceptance requires clean contamination/sandbox posture, valid
  lifecycle projection, captured output and artifact rows, candidate artifact
  inside released write scope, passed required probes, and satisfied
  stdout/stderr/exit-code/filesystem expectations;
- C blocked outcome postures must be supported by their matching status and
  blocker refs;
- C observation summaries are local-only and reject benchmark, ranking,
  baseline, leaderboard, official-like-result, and hidden-test-equivalence
  language;
- C remand and handoff rows are pressure-only and cannot grant retry,
  official submission, batch execution, benchmark, model-ranking, or
  future-family authority;
- C family closeout closes exactly `PB-SINGLE-CASE-RUN-0-A/B/C`;
- official ProgramBench participation, official runner/evaluator integration,
  hidden tests, source lookup, benchmark submission, benchmark scoring,
  baseline comparison, model ranking, generated official submissions,
  unbounded command execution, batch execution authority, retry authority,
  retry-chain authority, runtime transition, product authority, graph-memory
  authority, release authority, recursive-policy authority, and future-family
  selection remain unselected.

## Closed Boundary

The family now gives the repo a bounded local cleanroom single-case run
lifecycle:

```text
released local case lineage / matrix member
  -> single-case run request
  -> target selection
  -> execution preflight
  -> run control contract
  -> one local worker dispatch specimen
  -> execution trace
  -> local probe observation bundle
  -> candidate artifact capture
  -> lifecycle projection
  -> local outcome audit
  -> observation summary
  -> remand / acceptance decision
  -> pressure-only handoff
  -> family closeout alignment
```

That lifecycle is local only. It does not grant additional execution
authority, retry authority, batch execution authority, benchmark truth,
benchmark score, pass rate, solve rate, success rate, baseline comparison
authority, model ranking, official submission authority, official ProgramBench
runner/evaluator integration, hidden-test handling, hidden-test equivalence,
future-family selection, product authority, graph-memory authority, release
authority, or recursive-policy authority.

## Deferred Seams

The following seams remain deliberately unselected by this closeout:

- running more than one local single-case specimen;
- executing a revised matrix or a batch of local cases;
- retry governance after a single-case remand;
- comparing single-case outcomes across workers, models, baselines, or
  attempts;
- benchmark-result and benchmark-score governance;
- official ProgramBench participation governance;
- official runner/evaluator integration;
- hidden evaluator result governance;
- generated official submission review;
- broader case expansion or matrix inclusion beyond previously selected
  families;
- natural task-to-program-profile inference;
- broader conceptual broker implementation;
- multi-language realization overlays;
- V86/V87/V88 continuations;
- product, graph-memory, release, or recursive-policy work.

## Final Family Decision

- family decision:
  - `PB_SINGLE_CASE_RUN_0_CLOSED_LOCAL_CLEANROOM_SINGLE_CASE_RUN_GOVERNANCE_ONLY`
- rationale:
  - `PB-SINGLE-CASE-RUN-0` now has a complete A/B/C ladder on `main`;
  - the family governs one selected local cleanroom case-lineage run without
    turning that run into official ProgramBench participation, benchmark
    truth, scoring, baseline comparison, or model ranking;
  - the shipped lifecycle can select one target, preflight run controls,
    record one local specimen, capture local probes/artifacts, project into
    prior lifecycle vocabulary, audit the local outcome, summarize local
    observations, record local-only acceptance or remand pressure, and close
    the family;
  - the shipped lifecycle cannot run additional specimens, execute a matrix,
    grant retry authority, claim benchmark truth, claim official ProgramBench
    success, infer hidden tests, compare baselines, rank models, authorize
    official submissions, authorize batch execution, authorize retry-chain
    continuation, or select a future family;
  - future work requires a new selector or canonical lock.
