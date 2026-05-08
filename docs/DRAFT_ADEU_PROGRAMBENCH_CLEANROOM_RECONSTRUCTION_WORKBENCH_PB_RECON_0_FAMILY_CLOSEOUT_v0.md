# Draft ADEU ProgramBench Cleanroom Reconstruction Workbench PB-RECON-0 Family Closeout v0

Status: family closeout record for `PB-RECON-0` after `vNext+250` merged on
`main`.

Authority layer: closeout evidence on `main`.

## Closeout-State Marker

```json
{
  "schema": "pb_recon_0_family_closeout_state@1",
  "family": "PB-RECON-0",
  "phase": "family_closed_on_main",
  "closed_by_arc": "vNext+250",
  "closed_by_merge_commit": "ddb9af7e8d7a2cc50d297e109b673dbfe5430562",
  "family_alignment_artifact": "apps/api/fixtures/benchmarking/vnext_plus250/programbench_reconstruction_workbench_family_closeout_alignment_v250_reference.json",
  "authoritative_scope": "local_programbench_cleanroom_reconstruction_workbench_only",
  "future_family_authority": "none"
}
```

## Closed Slice Ladder

| Slice | Arc | Merge Commit | Closeout Evidence |
|---|---|---|---|
| `PB-RECON-0-A` | `vNext+248` | `b1ccc81b26e9e8c8dee8dc1cf5085522b22ebfb4` | `artifacts/agent_harness/v248/evidence_inputs/pb_recon_0a_work_order_closeout_evidence_v248.json` |
| `PB-RECON-0-B` | `vNext+249` | `1493e44993d8911817ada6b02cd8122730abf5f7` | `artifacts/agent_harness/v249/evidence_inputs/pb_recon_0b_local_evidence_closeout_evidence_v249.json` |
| `PB-RECON-0-C` | `vNext+250` | `ddb9af7e8d7a2cc50d297e109b673dbfe5430562` | `artifacts/agent_harness/v250/evidence_inputs/pb_recon_0c_local_audit_closeout_evidence_v250.json` |

## Shipped Surface Set

`PB-RECON-0` shipped the following local cleanroom reconstruction workbench
record shapes:

- `programbench_reconstruction_work_order@1`
- `programbench_reconstruction_worker_context_packet@1`
- `programbench_reconstruction_context_exclusion_manifest@1`
- `programbench_reconstruction_sandbox_policy@1`
- `programbench_reconstruction_run_budget@1`
- `programbench_reconstruction_workbench_non_authority_guardrail@1`
- `programbench_reconstruction_candidate_artifact_manifest@1`
- `programbench_reconstruction_local_run_trace@1`
- `programbench_reconstruction_probe_result_log@1`
- `programbench_reconstruction_remand_correction_record@1`
- `programbench_reconstruction_equivalence_audit@1`
- `programbench_reconstruction_result_summary@1`
- `programbench_reconstruction_handoff@1`
- `programbench_reconstruction_workbench_family_closeout_alignment@1`

All implementation stayed in `packages/adeu_benchmarking`. The family did not
create a ProgramBench runner, solver, evaluator, submitter, hidden-test
interface, benchmark score surface, model-ranking surface, product runtime
surface, graph-memory surface, release surface, or future-family selector.

## Alignment Judgment

`PB-RECON-0-A` established the workbench boundary:

- cleanroom reconstruction work order;
- worker-visible context packet;
- auditor-only exclusion manifest;
- sandbox policy;
- run budget;
- non-authority guardrail.

`PB-RECON-0-B` captured local evidence inside that boundary:

- candidate artifact manifest;
- sandbox/budget-bound local run traces;
- local probe result logs;
- remand/correction records bound to local cleanroom evidence only.

`PB-RECON-0-C` audited and summarized the local evidence:

- local equivalence audit;
- local reconstruction result summary;
- post-reconstruction handoff pressure;
- family closeout alignment.

The C reference path records a local remand requirement, not a local accepted
or benchmark-success claim. The review hardening in `vNext+250` added the
important final gates:

- every declared expected and observed behavior ref must be covered by local
  audit coverage rows;
- probe audit refs must be unique across positive, negative, and regression
  categories;
- rejected, remanded, and missing-evidence blocked summaries require carried
  blockers;
- non-accepted summaries cannot hand off as reconstruction-ready.

## Closed Boundary

The family now gives the repo a bounded bridge:

```text
ready cleanroom case packet
  -> reconstruction work order and worker-visible context
  -> sandbox and run-budget law
  -> local candidate artifact / run / probe / remand evidence
  -> local equivalence audit
  -> local result summary and handoff pressure
```

That bridge is local only. It does not grant hidden-test equivalence,
benchmark truth, benchmark score, model ranking, official submission
authority, official ProgramBench runner/evaluator integration, hidden-test
handling, worker dispatch authority, or future-family selection.

## Deferred Seams

The following seams remain deliberately unselected by this closeout:

- larger local cleanroom fixture matrices;
- actual local reconstruction worker execution;
- official ProgramBench participation governance;
- hidden evaluator result governance;
- benchmark-result and model-ranking governance;
- generated official submission review;
- natural task-to-program-profile inference;
- broader conceptual broker implementation;
- multi-language realization overlays;
- V86/V87/V88 continuations;
- product, graph-memory, release, or recursive-policy work.

## Final Family Decision

- family decision:
  - `PB_RECON_0_CLOSED_LOCAL_CLEANROOM_RECONSTRUCTION_WORKBENCH_ONLY`
- rationale:
  - `PB-RECON-0` now has a complete A/B/C ladder on `main`;
  - the family consumes the prior `PB-PY-0` realization substrate and
    `PB-ADAPTER-0` cleanroom case-packet membrane without widening their
    authority;
  - the shipped workbench can define a bounded reconstruction attempt,
    capture local candidate and probe evidence, and summarize local audit
    posture;
  - the shipped workbench cannot claim benchmark truth or official
    ProgramBench success;
  - future work requires a new selector or canonical lock.
