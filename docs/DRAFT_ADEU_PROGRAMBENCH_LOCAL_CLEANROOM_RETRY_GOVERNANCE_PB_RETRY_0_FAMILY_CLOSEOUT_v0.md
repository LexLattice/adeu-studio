# Draft ADEU ProgramBench Local Cleanroom Retry Governance PB-RETRY-0 Family Closeout v0

Status: family closeout record after `vNext+259` / `PB-RETRY-0-C` merged on
`main`.

Authority layer: closeout evidence on `main`.

This note closes `PB-RETRY-0` as the local cleanroom retry-governance family.
It does not authorize a second retry request, retry-chain authority, official
ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, generated official submissions, official submission authority,
unbounded command execution, target mutation outside released local
sandbox/write scope, runtime transition, product authorization, graph-memory
authority, release authority, recursive policy amendment, or future-family
selection.

## Family-State Marker

```json
{
  "schema": "pb_retry_0_family_closeout_state@1",
  "family": "PB-RETRY-0",
  "phase": "family_closed_on_main",
  "closed_by_arc": "vNext+259",
  "closed_by_merge_commit": "0b1fb5d55e343b12405595563c16ef0ba37fbe20",
  "family_alignment_artifact": "apps/api/fixtures/benchmarking/vnext_plus259/programbench_local_retry_family_closeout_alignment_v259_reference.json",
  "authoritative_scope": "single_local_programbench_cleanroom_retry_governance_only",
  "future_family_authority": "none"
}
```

## Closed Slice Ladder

| Slice | Global arc | Closed surface | Closeout evidence |
|---|---|---|---|
| `PB-RETRY-0-A` | `vNext+257` | retry request, lineage registry, remand source index, eligibility review, scope contract, and non-authority guardrail | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS257.md`; `artifacts/agent_harness/v257/evidence_inputs/pb_retry_0a_retry_intake_closeout_evidence_v257.json` |
| `PB-RETRY-0-B` | `vNext+258` | retry dispatch record, execution capture, candidate delta snapshot, lifecycle projection, and sandbox trace | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS258.md`; `artifacts/agent_harness/v258/evidence_inputs/pb_retry_0b_dispatch_specimen_closeout_evidence_v258.json` |
| `PB-RETRY-0-C` | `vNext+259` | retry outcome audit, same-lineage delta observation summary, remand settlement, and family closeout alignment | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS259.md`; `artifacts/agent_harness/v259/evidence_inputs/pb_retry_0c_retry_closeout_evidence_v259.json` |

## Shipped Surface Set

`PB-RETRY-0` shipped these `adeu_benchmarking` local cleanroom retry surfaces:

- `programbench_local_retry_request@1`
- `programbench_local_retry_lineage_registry@1`
- `programbench_trial_remand_source_index@1`
- `programbench_local_retry_eligibility_review@1`
- `programbench_local_retry_scope_contract@1`
- `programbench_local_retry_non_authority_guardrail@1`
- `programbench_local_retry_dispatch_record@1`
- `programbench_local_retry_execution_capture@1`
- `programbench_local_retry_candidate_delta_snapshot@1`
- `programbench_local_retry_lifecycle_projection@1`
- `programbench_local_retry_sandbox_application_trace@1`
- `programbench_local_retry_outcome_audit@1`
- `programbench_local_retry_delta_observation_summary@1`
- `programbench_local_retry_remand_settlement@1`
- `programbench_local_retry_family_closeout_alignment@1`

The family stayed in `packages/adeu_benchmarking` and did not become an
official ProgramBench runner, solver, evaluator integration, hidden-test
interface, benchmark submission path, benchmark scoring path, model-ranking
system, retry-chain dispatcher, product runtime surface, graph-memory
authority surface, release authority lane, or recursive-policy amendment path.

## Alignment Judgment

`PB-RETRY-0-A` created the non-executing retry-governance boundary:

- one retry request over one released `PB-TRIAL-0` remand decision;
- retry lineage registry with uniqueness over the source trial remand;
- remand source index limited to local cleanroom remand sources;
- eligibility review;
- scope contract with unchanged worker-visible, forbidden, tool, sandbox,
  write-scope, and network-policy hashes;
- non-authority guardrail.

It kept remand pressure distinct from retry dispatch authority, rejected
locally accepted, contaminated, sandbox-blocked, official-evaluator, hidden
test, source lookup, decompilation, internet, external repo, benchmark-score,
and model-ranking retry rationales, and prevented many separate
`retry_depth = 1` requests from laundering an unbounded retry loop.

`PB-RETRY-0-B` recorded one bounded local retry dispatch specimen:

- one dispatch record per retry request;
- retry depth fixed to one;
- B-lock dispatch authority;
- hash-bound retry input packet, worker-visible context, scope contract, tool
  manifests, sandbox policy, run budget, and source trial continuity;
- execution capture with screened output hashes and bounded excerpts;
- candidate delta snapshot inside released write scope and only after passed
  forbidden-content screening;
- lifecycle projection without new evidence law;
- sandbox application trace with network, Docker socket, host secret, source
  lookup, decompilation, write scope, resource, and tool-manifest witnesses.

It kept retry dispatch local-only and B-lock-bound, rejected hidden/source,
internet, decompilation, external-repo, official runner/evaluator,
benchmark-score, model-ranking, official-submission, and second-retry
authority, and did not emit outcome audit, delta summary, remand settlement,
or family closeout rows.

`PB-RETRY-0-C` audited, summarized, settled, and closed the retry:

- outcome audit over released A/B rows;
- same-lineage delta observation summary;
- local remand settlement;
- family closeout alignment.

Review hardening in `vNext+259` closed the important remand-accounting and
settlement edges:

- remand satisfaction rows must reference declared outcome-audit local remands;
- satisfaction source refs are scanned for hidden/forbidden categories;
- settlement must account for all outcome-audit local remands through settled
  or unresolved refs;
- resolved retry outcomes require settled remand settlement posture;
- settled, unresolved, and new local remand refs are mutually exclusive;
- family closeout validates `closed_slice_refs` and closes exactly
  `PB-RETRY-0-A/B/C`.

The three slices align:

- released `PB-TRIAL-0` local remand pressure is required before retry intake;
- remand pressure remains pressure only until A eligibility and scope rows
  validate;
- A eligibility remains non-dispatching and cannot run the retry;
- retry uniqueness is enforced by lineage and source remand decision;
- retry scope cannot widen evidence sources, tool policy, sandbox policy,
  write scope, network posture, source visibility, or forbidden-evidence
  posture;
- B dispatch is one local retry specimen, hash-bound, sandbox-witnessed,
  and B-lock-bound;
- candidate delta snapshots require passed forbidden-content screening,
  screened-output hash linkage, and released write scope;
- lifecycle projection maps only to released trial/attempt lifecycle refs and
  cannot define new evidence law;
- C outcome audit consumes released A/B rows and cannot hide blockers;
- delta observations are same-lineage-only and local-only;
- remand settlement accounts for all local remands without granting second
  retry authority;
- family closeout closes `PB-RETRY-0` only and does not select the next family;
- official ProgramBench participation, official runner/evaluator integration,
  hidden tests, source lookup, benchmark submission, benchmark scoring, model
  ranking, generated official submissions, unbounded command execution, second
  retry authority, retry-chain authority, runtime transition, product
  authority, graph-memory authority, release authority, recursive-policy
  authority, and future-family selection remain unselected.

## Closed Boundary

The family now gives the repo a bounded local retry-governance lifecycle:

```text
released local trial remand decision
  -> retry request and retry lineage registry
  -> local-only remand source index
  -> retry eligibility review
  -> unchanged-boundary retry scope contract
  -> one local retry dispatch specimen
  -> retry execution capture
  -> candidate delta snapshot
  -> lifecycle projection
  -> sandbox application trace
  -> local retry outcome audit
  -> same-lineage delta observation summary
  -> local remand settlement
  -> family closeout alignment
```

That lifecycle is local only. It does not grant second-retry authority,
retry-chain authority, hidden-test equivalence, benchmark truth, benchmark
score, model ranking, official submission authority, official ProgramBench
runner/evaluator integration, hidden-test handling, future-family selection,
product authority, graph-memory authority, release authority, or
recursive-policy authority.

## Deferred Seams

The following seams remain deliberately unselected by this closeout:

- second retry authority and retry-chain governance;
- multi-attempt comparison and model-ranking governance;
- official ProgramBench participation governance;
- official runner/evaluator integration;
- hidden evaluator result governance;
- benchmark-result and benchmark-score governance;
- generated official submission review;
- larger local cleanroom fixture matrices;
- natural task-to-program-profile inference;
- broader conceptual broker implementation;
- multi-language realization overlays;
- V86/V87/V88 continuations;
- product, graph-memory, release, or recursive-policy work.

## Final Family Decision

- family decision:
  - `PB_RETRY_0_CLOSED_SINGLE_LOCAL_CLEANROOM_RETRY_GOVERNANCE_ONLY`
- rationale:
  - `PB-RETRY-0` now has a complete A/B/C ladder on `main`;
  - the family consumes the prior `PB-TRIAL-0` local remand pressure without
    widening its authority;
  - the shipped lifecycle can intake one local remand, review retry
    eligibility, preserve cleanroom scope, record one local retry dispatch,
    capture retry execution, snapshot a candidate delta, project lifecycle
    evidence, audit the local retry outcome, summarize same-lineage deltas,
    and settle local remands;
  - the shipped lifecycle cannot claim benchmark truth, official ProgramBench
    success, hidden-test equivalence, model ranking, official submission
    authority, second retry authority, retry-chain authority, or future-family
    selection;
  - future work requires a new selector or canonical lock.
