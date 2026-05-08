# Draft ADEU ProgramBench Cleanroom Reconstruction Attempt PB-ATTEMPT-0 Family Closeout v0

Status: family closeout record after `vNext+253` / `PB-ATTEMPT-0-C` merged on
`main`.

Authority layer: closeout evidence on `main`.

This note closes `PB-ATTEMPT-0` as the local cleanroom reconstruction attempt
lifecycle family. It does not authorize official ProgramBench participation,
official task execution, official runner integration, official evaluator
integration, hidden-test handling, hidden-test inference, hidden-test
equivalence, original source lookup, decompilation, internet lookup inside
ProgramBench tasks, external repository lookup, benchmark submission,
benchmark scoring, benchmark truth, model ranking, generated official
submissions, official submission authority, retry dispatch authority,
unbounded command execution, target mutation outside released local sandbox
write scope, runtime transition, product authorization, graph-memory
authority, recursive policy amendment, or future-family selection.

## Family-State Marker

```json
{
  "schema": "pb_attempt_0_family_closeout_state@1",
  "family": "PB-ATTEMPT-0",
  "phase": "family_closed_on_main",
  "closed_by_arc": "vNext+253",
  "closed_by_merge_commit": "1fb5f8ea792ff38281da462ed17c40864c81a438",
  "family_alignment_artifact": "apps/api/fixtures/benchmarking/vnext_plus253/programbench_reconstruction_attempt_family_closeout_alignment_v253_reference.json",
  "authoritative_scope": "local_programbench_cleanroom_reconstruction_attempt_lifecycle_only",
  "future_family_authority": "none"
}
```

## Closed Slice Ladder

| Slice | Global arc | Closed surface | Closeout evidence |
|---|---|---|---|
| `PB-ATTEMPT-0-A` | `vNext+251` | attempt request, worker input packet, dispatch preflight, and non-authority guardrail | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS251.md`; `artifacts/agent_harness/v251/evidence_inputs/pb_attempt_0a_attempt_preflight_closeout_evidence_v251.json` |
| `PB-ATTEMPT-0-B` | `vNext+252` | worker invocation record, output capture, candidate materialization, and sandbox application trace | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS252.md`; `artifacts/agent_harness/v252/evidence_inputs/pb_attempt_0b_invocation_capture_closeout_evidence_v252.json` |
| `PB-ATTEMPT-0-C` | `vNext+253` | workbench evidence export, attempt result review, remand queue, and family closeout alignment | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS253.md`; `artifacts/agent_harness/v253/evidence_inputs/pb_attempt_0c_attempt_closeout_evidence_v253.json` |

## Shipped Surface Set

`PB-ATTEMPT-0` shipped these `adeu_benchmarking` local cleanroom attempt
surfaces:

- `programbench_reconstruction_attempt_request@1`
- `programbench_reconstruction_attempt_worker_input_packet@1`
- `programbench_reconstruction_attempt_dispatch_preflight@1`
- `programbench_reconstruction_attempt_non_authority_guardrail@1`
- `programbench_reconstruction_attempt_worker_invocation_record@1`
- `programbench_reconstruction_attempt_output_capture@1`
- `programbench_reconstruction_attempt_candidate_materialization@1`
- `programbench_reconstruction_attempt_sandbox_application_trace@1`
- `programbench_reconstruction_attempt_workbench_evidence_export@1`
- `programbench_reconstruction_attempt_result_review@1`
- `programbench_reconstruction_attempt_remand_queue@1`
- `programbench_reconstruction_attempt_family_closeout_alignment@1`

The family stayed in `packages/adeu_benchmarking` and did not become an
official ProgramBench runner, solver, evaluator integration, hidden-test
interface, benchmark submission path, benchmark scoring path, model-ranking
system, product runtime surface, graph-memory authority surface, release
authority lane, or recursive-policy amendment path.

## Alignment Judgment

`PB-ATTEMPT-0-A` created the local attempt preflight boundary:

- attempt request over released `PB-RECON-0` workbench state;
- exact worker-visible input packet;
- eligibility-only dispatch preflight;
- non-authority guardrail.

It kept hidden, forbidden, auditor-only, postmortem-only, original-source,
decompilation, internet, external-repo, host-secret, and Docker-socket refs
out of the worker-visible packet. Exclusion summaries remained
non-content-bearing and could not launder source names, paths, excerpts,
semantic summaries, test names, hidden artifact ids, or original-source clues.
Preflight remained eligibility review only and did not invoke a worker,
execute commands, run probes, materialize candidates, or grant official
ProgramBench authority.

`PB-ATTEMPT-0-B` captured one bounded local worker invocation under the
released A packet:

- one invocation per attempt request;
- hash-bound input packet, worker-visible context, and tool manifests;
- output capture with hashes and bounded excerpts;
- forbidden-content screening before materialization;
- candidate materialization inside released write scope;
- sandbox application trace with network, secret, Docker socket, and source
  lookup absence attestations.

It kept invocation and materialization local-only and rejected hidden-test
access, original-source lookup, internet/decompilation/external-repo access,
official runner/evaluator contact, benchmark score, model ranking, benchmark
truth, and official submission posture.

`PB-ATTEMPT-0-C` exported and reviewed the captured local attempt:

- workbench evidence export into released `PB-RECON-0` evidence vocabulary;
- attempt result review;
- pressure-only remand queue;
- family closeout alignment.

Review hardening in `vNext+253` closed the important export and posture
edges:

- exported candidate, local-run, probe-log, and remand-record refs must match
  released `PB-RECON-0` evidence rows;
- exported evidence rows must align with the released PB-RECON result summary,
  not merely name the summary;
- valid export requires PB-RECON validator binding refs and validation result
  refs for every mapped evidence row;
- `attempt_locally_accepted` requires an exported PB-RECON `local_accepted`
  result summary and valid workbench export;
- contamination-blocked and sandbox-violation-blocked workbench summaries
  require matching attempt result postures;
- export gaps remain blocked and cannot be remanded away or accepted;
- remand rows cite local attempt/workbench evidence only and do not grant retry
  authority;
- family closeout alignment closes exactly `PB-ATTEMPT-0-A/B/C`.

The three slices align:

- released `PB-RECON-0` workbench state is required before an attempt request
  can be packaged;
- worker-visible input is hash-bound and cleanroom-visible only;
- dispatch preflight is eligibility-only, not dispatch authority;
- invocation is local, bounded, and single-attempt unless a later family adds
  retry authority;
- output capture and materialization are hash-bound and screened;
- sandbox traces carry absence attestations rather than narrative trust;
- attempt evidence export maps into released PB-RECON workbench law instead
  of defining new evidence law;
- local attempt acceptance remains local-only and does not claim hidden-test
  equivalence, benchmark truth, benchmark score, or model ranking;
- remand remains pressure-only and cannot dispatch retries;
- family closeout closes `PB-ATTEMPT-0` only and does not select the next
  family;
- official ProgramBench participation, official runner/evaluator integration,
  hidden tests, source lookup, benchmark submission, benchmark scoring, model
  ranking, generated official submissions, unbounded command execution, tool
  invocation authority beyond the recorded local attempt, runtime transition,
  product authority, graph-memory authority, recursive-policy authority, and
  future-family selection remain unselected.

## Closed Boundary

The family now gives the repo a bounded local attempt lifecycle:

```text
released local cleanroom workbench
  -> attempt request and worker-visible input packet
  -> eligibility-only dispatch preflight
  -> one bounded local worker invocation
  -> bounded output capture and screened candidate materialization
  -> sandbox application trace
  -> workbench evidence export
  -> local attempt result review
  -> pressure-only remand queue
  -> family closeout alignment
```

That lifecycle is local only. It does not grant hidden-test equivalence,
benchmark truth, benchmark score, model ranking, official submission
authority, official ProgramBench runner/evaluator integration, hidden-test
handling, retry dispatch authority, future-family selection, product
authority, graph-memory authority, release authority, or recursive-policy
authority.

## Deferred Seams

The following seams remain deliberately unselected by this closeout:

- actual next reconstruction attempt execution using the lifecycle;
- retry dispatch authority and multi-attempt comparison;
- larger local cleanroom fixture matrices;
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
  - `PB_ATTEMPT_0_CLOSED_LOCAL_CLEANROOM_RECONSTRUCTION_ATTEMPT_LIFECYCLE_ONLY`
- rationale:
  - `PB-ATTEMPT-0` now has a complete A/B/C ladder on `main`;
  - the family consumes the prior `PB-RECON-0` local workbench substrate
    without widening its authority;
  - the shipped lifecycle can package an attempt, record one bounded local
    invocation, capture and screen output, materialize a local candidate,
    trace sandbox posture, export local workbench evidence, review local
    attempt posture, and queue remand pressure;
  - the shipped lifecycle cannot claim benchmark truth, official ProgramBench
    success, hidden-test equivalence, model ranking, official submission
    authority, retry dispatch authority, or future-family selection;
  - future work requires a new selector or canonical lock.
