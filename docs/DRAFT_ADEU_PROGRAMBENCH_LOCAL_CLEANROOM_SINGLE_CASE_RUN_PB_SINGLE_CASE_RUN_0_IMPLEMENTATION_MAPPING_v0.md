# Draft ADEU ProgramBench Local Cleanroom Single Case Run PB-SINGLE-CASE-RUN-0 Implementation Mapping v0

Status: support / implementation mapping record for planned
`PB-SINGLE-CASE-RUN-0`.

Authority layer: support.

This note maps the likely implementation for the `PB-SINGLE-CASE-RUN-0`
family into package, schema, validator, fixture, and slice surfaces. It does
not authorize implementation by itself and does not replace a future
`vNext+<n>` lock, stop-gate decision, or edge assessment.

## Family Scope

`PB-SINGLE-CASE-RUN-0` should add one-specimen local cleanroom execution
governance for a selected ProgramBench-style local case lineage. It should
not run an official ProgramBench task, contact an official evaluator, infer
hidden tests, use original source, decompile, submit artifacts, score
benchmarks, compare baselines, rank models, execute batches, or select a
future family.

It is not a second copy of `PB-TRIAL-0`. It is a selected
matrix/case-lineage run wrapper that binds one released case lineage to the
already-established attempt/trial/workbench evidence vocabulary.

The family should answer:

```text
Can we run one selected local cleanroom case specimen under released sandbox,
worker-visible packet, local probe, and lifecycle law, and capture what
happened?
```

It must not answer:

```text
What is our ProgramBench score?
Is this better than the baseline?
Which model is better?
Should this be submitted officially?
How will hidden tests behave?
```

## Likely Package Ownership

Keep the family in `packages/adeu_benchmarking` while it remains
ProgramBench-shaped local cleanroom execution substrate.

Likely files for later implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_single_case_run.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/*.v1.json`
- `spec/*.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_single_case_run_pb_single_case_run_0a.py`
- `packages/adeu_benchmarking/tests/test_programbench_single_case_run_pb_single_case_run_0b.py`
- `packages/adeu_benchmarking/tests/test_programbench_single_case_run_pb_single_case_run_0c.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus269/`
- `apps/api/fixtures/benchmarking/vnext_plus270/`
- `apps/api/fixtures/benchmarking/vnext_plus271/`

Avoid package or schema names that imply official benchmark execution,
evaluation, scoring, submission, leaderboard, baseline comparison, or model
ranking.

## Planned Record Shapes

| Shape | Slice | Purpose |
|---|---|---|
| `programbench_single_case_run_request@1` | `PB-SINGLE-CASE-RUN-0-A` | one request to prepare a local cleanroom run over exactly one case lineage |
| `programbench_single_case_target_selection@1` | `PB-SINGLE-CASE-RUN-0-A` | selected target case lineage, artifact hashes, and cleanroom boundary identity |
| `programbench_single_case_execution_preflight@1` | `PB-SINGLE-CASE-RUN-0-A` | non-executing preflight over sandbox, tools, worker input, runbook, budget, and probe basis |
| `programbench_single_case_run_control_contract@1` | `PB-SINGLE-CASE-RUN-0-A` | run controls for one later local specimen |
| `programbench_single_case_run_non_authority_guardrail@1` | `PB-SINGLE-CASE-RUN-0-A` | guardrail preventing A rows from becoming dispatch, scoring, ranking, or official authority |
| `programbench_single_case_worker_dispatch_specimen@1` | `PB-SINGLE-CASE-RUN-0-B` | exactly one local worker dispatch specimen under released A controls and B authority |
| `programbench_single_case_execution_trace@1` | `PB-SINGLE-CASE-RUN-0-B` | stdout/stderr/exit/duration/timeout/tool/filesystem execution capture |
| `programbench_single_case_probe_observation_bundle@1` | `PB-SINGLE-CASE-RUN-0-B` | declared local probe observations, not hidden-test equivalence |
| `programbench_single_case_candidate_artifact_capture@1` | `PB-SINGLE-CASE-RUN-0-B` | generated candidate artifacts captured inside released write scope |
| `programbench_single_case_lifecycle_projection@1` | `PB-SINGLE-CASE-RUN-0-B` | projection back into released attempt/trial/workbench evidence vocabulary |
| `programbench_single_case_local_outcome_audit@1` | `PB-SINGLE-CASE-RUN-0-C` | audit of one local specimen against declared local probes and lifecycle projection |
| `programbench_single_case_run_observation_summary@1` | `PB-SINGLE-CASE-RUN-0-C` | local-only summary without benchmark or model-comparison language |
| `programbench_single_case_remand_or_acceptance_decision@1` | `PB-SINGLE-CASE-RUN-0-C` | local accepted / remand required / blocked / inconclusive posture |
| `programbench_single_case_run_handoff@1` | `PB-SINGLE-CASE-RUN-0-C` | pressure-only handoff, not retry or future-family authority |
| `programbench_single_case_run_family_closeout_alignment@1` | `PB-SINGLE-CASE-RUN-0-C` | family closeout alignment without widening into scoring or official participation |

`PB-SINGLE-CASE-RUN-0-A` should ship only request, target selection,
execution preflight, control contract, and guardrail rows.
`PB-SINGLE-CASE-RUN-0-B` and `PB-SINGLE-CASE-RUN-0-C` should remain deferred
until their own canonical starter locks.

## Consumed Lineage

`PB-SINGLE-CASE-RUN-0-A` should require released lineage from one of these
lawful local sources:

- a released `PB-MATRIX-INCLUSION-0-C` local matrix revision member;
- a released `PB-CASE-EXPANSION-0-C` ready local case lineage;
- a released `PB-ADAPTER-0-C` reconstruction case packet, if the family lock
  explicitly selects direct single-case intake rather than matrix-member
  intake.

The selected case must also resolve through released substrate as applicable:

- `PB-PY-0` concept / realization constraints;
- `PB-ADAPTER-0` visibility and access membrane;
- `PB-RECON-0` workbench rows;
- `PB-ATTEMPT-0` worker input and attempt lifecycle rows;
- `PB-TRIAL-0` trial runbook / sandbox readiness rows;
- optional `PB-RETRY-0` settlement rows if the chosen lineage is retry-derived.

The default target-origin route should be `matrix_member`. Other routes are
exception paths and require explicit posture:

- `target_origin_route = matrix_member`:
  selected case must be included in a released matrix revision and bind
  `source_matrix_ref`, `source_matrix_revision_ref`,
  `source_matrix_revision_hash`, `matrix_membership_row_ref`, and
  `matrix_membership_status = included`.
- `target_origin_route = ready_expanded_case_lineage`:
  selected case must have released readiness and no contamination blockers.
- `target_origin_route = direct_adapter_case_exception`:
  explicit exception posture and non-matrix-lineage warning are required.

## Cross-Slice Validation Spine

The future implementation should validate:

- A rejects B/C artifact kinds;
- A selects exactly one target case lineage;
- A records `single_case_run_relation_to_prior_lifecycle` as
  `matrix_member_run`, `expanded_case_lineage_run`, or
  `direct_adapter_case_run_exception`;
- A requires route-specific target-origin refs and rejects a deferred or
  rejected matrix-inclusion candidate as a target;
- A target selection must resolve to released cleanroom lineage and clean
  contamination posture;
- A must bind worker-visible packet hash, runbook hash, sandbox policy hash,
  run budget hash, tool manifest hash, write-scope hash, probe-basis hash,
  and target case lineage hash;
- A preflight cannot grant worker dispatch, command execution, candidate
  materialization, local acceptance, benchmark scoring, or future-family
  authority;
- B requires released A refs and B lock dispatch authority;
- B emits exactly one worker dispatch specimen per run request;
- B requires `dispatch_specimen_index = 1`,
  `single_case_dispatch_cardinality_posture =
  exactly_one_dispatch_specimen`, and `dispatch_authority_kind =
  b_slice_lock_local_single_specimen_only`;
- B execution trace must bind to the A hashes and sandbox witness bundle;
- B execution trace must declare `execution_trace_kind`;
- B command rows must be argv-shaped and raw shell strings are forbidden
  unless a later explicit authority grants and justifies shell wrapping;
- B candidate artifact capture requires forbidden-content screening pass and
  released write-scope match;
- B probe observations are local declared probes only and cannot cite hidden
  tests or official evaluator feedback;
- C requires released A/B refs;
- C local accepted posture requires valid execution trace, valid local probe
  observation bundle, candidate artifact capture inside write scope, and valid
  lifecycle projection;
- C local accepted posture also requires no contamination, sandbox, output
  capture, lifecycle projection, or required local probe blockers;
- C remand pressure cannot grant retry authority by itself;
- no slice may create official ProgramBench participation, hidden-test
  inference, benchmark score, baseline comparison, model ranking, batch
  execution, official submission, or future-family selection.

## Reference Fixture Plan

For `PB-SINGLE-CASE-RUN-0-A`, reference fixtures should include:

- one run request over a released local case lineage;
- one target selection with stable lineage and artifact hashes;
- one execution preflight with ready-for-later-execution-review posture;
- one run control contract binding sandbox, tool, budget, write scope, and
  probe basis;
- one non-authority guardrail.

Reject fixtures should include:

- multiple target case lineages in one request;
- target case without released cleanroom lineage;
- target case with contamination blocker;
- preflight granting dispatch authority;
- control contract with open network or source lookup;
- control contract with non-closed tool manifest;
- request containing benchmark score, baseline comparison, or model-ranking
  language.

For `PB-SINGLE-CASE-RUN-0-B`, later fixtures should include:

- one worker dispatch specimen;
- one execution trace;
- one local probe observation bundle;
- one candidate artifact capture;
- one lifecycle projection.

Reject fixtures should include:

- B dispatch without released A preflight;
- more than one dispatch specimen for a request;
- execution trace missing sandbox attestation;
- candidate artifact capture outside write scope;
- output capture with forbidden-content screen failure;
- hidden-test or official-evaluator observation.

For `PB-SINGLE-CASE-RUN-0-C`, later fixtures should include:

- one local outcome audit;
- one observation summary;
- one remand-or-acceptance decision;
- one pressure-only handoff;
- one family closeout alignment.

Reject fixtures should include:

- local accepted without valid B trace/probe/candidate/projection refs;
- observation summary using pass-rate, solve-rate, success-rate, baseline,
  model-ranking, or leaderboard language;
- remand decision granting retry authority;
- handoff selecting official participation or benchmark scoring.

## Non-Outputs

`PB-SINGLE-CASE-RUN-0` must not output:

- official ProgramBench runner integration;
- official evaluator integration;
- hidden-test observation or inference rows;
- benchmark scores;
- pass rates, solve rates, success rates, or official success rates;
- baseline comparison rows;
- model rankings;
- leaderboard claims;
- official submission artifacts;
- batch execution rows;
- matrix-wide result projections;
- retry-chain authority rows;
- source lookup, decompilation, internet, or external-repo evidence rows;
- future-family selection rows.
