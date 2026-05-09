# Draft ADEU ProgramBench Local Cleanroom Matrix Inclusion PB-MATRIX-INCLUSION-0 Implementation Mapping v0

Status: support / implementation mapping record for planned
`PB-MATRIX-INCLUSION-0`.

Authority layer: support.

This note maps the likely implementation for the `PB-MATRIX-INCLUSION-0`
family into package, schema, validator, fixture, and slice surfaces. It does
not authorize implementation by itself and does not replace a future
`vNext+<n>` lock, stop-gate decision, or edge assessment.

## Family Scope

`PB-MATRIX-INCLUSION-0` should add local cleanroom matrix-inclusion governance
for ready expanded local case lineages. It should not execute cases, run
probes, materialize candidate implementations, project results, summarize
matrix outcomes, score benchmarks, compare baselines, rank models, contact
official evaluators, infer hidden tests, submit artifacts, execute batches,
or select a future family.

The family should answer:

```text
Can these released local case lineages become members of a declared local
matrix revision, under unchanged cleanroom and non-ranking controls?
```

It must not answer:

```text
Can we run the matrix now?
What score did the matrix get?
Is this better than a baseline?
Which model is better?
Should we submit officially?
```

## Likely Package Ownership

Keep the family in `packages/adeu_benchmarking` while it remains
ProgramBench-shaped local cleanroom substrate.

Likely files for later implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_matrix_inclusion.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/*.v1.json`
- `spec/*.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_inclusion_pb_matrix_inclusion_0a.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_inclusion_pb_matrix_inclusion_0b.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_inclusion_pb_matrix_inclusion_0c.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus266/`
- `apps/api/fixtures/benchmarking/vnext_plus267/`
- `apps/api/fixtures/benchmarking/vnext_plus268/`

Avoid package or schema names that imply official benchmark execution,
evaluation, scoring, submission, baseline comparison, leaderboard, or model
ranking.

## Planned Record Shapes

| Shape | Slice | Purpose |
|---|---|---|
| `programbench_local_matrix_inclusion_request@1` | `PB-MATRIX-INCLUSION-0-A` | one request to evaluate ready local case lineages for matrix revision candidacy |
| `programbench_local_matrix_candidate_intake@1` | `PB-MATRIX-INCLUSION-0-A` | row-shaped intake from case-expansion handoffs and current matrix baseline |
| `programbench_local_matrix_inclusion_eligibility_review@1` | `PB-MATRIX-INCLUSION-0-A` | eligibility / blocker review for candidate case lineages |
| `programbench_local_matrix_inclusion_control_contract@1` | `PB-MATRIX-INCLUSION-0-A` | controls for matrix horizon, profile/tool/probe continuity, and non-ranking posture |
| `programbench_local_matrix_inclusion_non_authority_guardrail@1` | `PB-MATRIX-INCLUSION-0-A` | guardrail preventing inclusion rows from becoming execution, scoring, or ranking authority |
| `programbench_local_matrix_amendment_plan@1` | `PB-MATRIX-INCLUSION-0-B` | planned local matrix membership amendment |
| `programbench_local_matrix_case_delta_manifest@1` | `PB-MATRIX-INCLUSION-0-B` | added/deferred/rejected candidate accounting with dedupe and lineage hashes |
| `programbench_local_matrix_comparability_delta_review@1` | `PB-MATRIX-INCLUSION-0-B` | review of worker/model/tool/probe/horizon continuity changes |
| `programbench_local_matrix_contamination_delta_review@1` | `PB-MATRIX-INCLUSION-0-B` | cleanroom contamination transfer and redaction review |
| `programbench_local_matrix_inclusion_decision_record@1` | `PB-MATRIX-INCLUSION-0-B` | local accounting inclusion decisions without execution or result authority |
| `programbench_local_matrix_revision_registration@1` | `PB-MATRIX-INCLUSION-0-C` | registration of revised local matrix membership |
| `programbench_local_matrix_revision_readiness_summary@1` | `PB-MATRIX-INCLUSION-0-C` | readiness / blocker / handoff summary for the revised matrix |
| `programbench_local_matrix_post_inclusion_handoff@1` | `PB-MATRIX-INCLUSION-0-C` | pressure-only handoff toward later execution/projection governance |
| `programbench_local_matrix_inclusion_family_closeout_alignment@1` | `PB-MATRIX-INCLUSION-0-C` | family closeout alignment without future-family authority |

`PB-MATRIX-INCLUSION-0-A` should ship only request, intake, eligibility,
control, and guardrail rows. `PB-MATRIX-INCLUSION-0-B` and
`PB-MATRIX-INCLUSION-0-C` should remain deferred until their own canonical
starter locks.

## Matrix Identity Hardening

All slices should preserve matrix baseline / revision identity:

- `base_matrix_ref`
- `base_matrix_revision_ref`
- `base_matrix_revision_hash`
- `target_matrix_revision_candidate_ref`
- `target_matrix_revision_candidate_hash`
- `prior_membership_manifest_hash`
- `proposed_membership_manifest_hash`
- `revision_delta_hash`

Validation should reject any A request that does not bind to exactly one
released base matrix revision and exactly one proposed revision candidate.
Later B/C rows must resolve to the same identity tuple.

## Consumed Lineage

`PB-MATRIX-INCLUSION-0-A` should require released lineage from:

- `PB-CASE-EXPANSION-0-C`:
  - local case lineage registration refs;
  - expansion readiness summary refs;
  - pressure-only matrix candidate handoff refs;
  - family closeout alignment refs.
- `PB-MATRIX-0-C`:
  - local matrix summary or closeout alignment refs;
  - matrix control/accounting posture refs.

The family should also inherit prior ProgramBench family closeouts as
cleanroom law and lineage constraints, not as new authority.

## Cross-Slice Validation Spine

The future implementation should validate:

- A rejects B/C artifact kinds;
- A requires released case-expansion lineages and pressure-only handoff refs;
- A requires a released local matrix baseline or declared local matrix target;
- A requires one released base matrix revision and one proposed revision
  candidate, both hash-bound;
- A rejects blocked, deferred, contaminated, hidden-test-derived,
  evaluator-derived, source-derived, decompilation-derived, internet-derived,
  external-repo-derived, postmortem-only, or support-only case candidates;
- A rejects candidates that lack complete local probe/oracle coverage;
- A rejects candidates already present in the base matrix unless explicit
  replacement/update posture is selected;
- A rejects candidate rows that would widen worker/model profile, tool policy,
  probe basis, write scope, network posture, or source visibility unless the
  control contract marks the matrix as non-comparable local accounting only;
- B requires released A refs;
- B cannot include A-blocked candidate rows;
- B case delta manifest must account for every A-eligible candidate as added,
  deferred, or rejected;
- B inclusion decision is local accounting membership only and cannot create
  local results, scores, or execution authority;
- B contamination delta review must preserve redaction and fail closed;
- B rejects inclusion rationales that cite likely pass/fail, score, model
  advantage, baseline improvement, hidden edge coverage, or benchmark
  relevance;
- C requires released A/B refs;
- C revision registration requires exact B inclusion decision refs and case
  delta refs;
- C readiness counts remain inventory-only;
- C readiness denominators remain local matrix denominators only, not
  official ProgramBench or benchmark denominators;
- C handoff rows are pressure-only and non-selecting;
- no slice may create official ProgramBench participation, official runner or
  evaluator integration, hidden-test inference, benchmark score, baseline
  comparison, model ranking, batch execution, official submission, or
  future-family selection.

## Reference Fixture Plan

For `PB-MATRIX-INCLUSION-0-A`, reference fixtures should include:

- one matrix inclusion request over a released case-expansion handoff;
- one candidate intake row for a ready clean case lineage;
- one eligibility review that marks the candidate eligible for later
  amendment review;
- one control contract preserving local matrix non-ranking posture;
- one non-authority guardrail.

Reject fixtures should include:

- candidate lineage without released case-expansion closeout;
- candidate lineage with blocked readiness;
- candidate lineage with contamination exposure;
- candidate lineage missing probe/oracle coverage;
- inclusion request that grants direct matrix inclusion;
- control contract that widens tool policy or write scope without explicit
  non-comparable posture;
- benchmark score, pass rate, baseline comparison, or model-ranking language.

For `PB-MATRIX-INCLUSION-0-B`, later fixtures should include:

- one amendment plan;
- one case delta manifest;
- one comparability delta review;
- one contamination delta review;
- one inclusion decision record.

Reject fixtures should include:

- B rows without released A refs;
- inclusion of A-blocked candidate;
- delta manifest that drops an eligible candidate without reason;
- contamination transfer marked clean despite exposed refs;
- inclusion decision that grants execution, result projection, scoring, or
  direct benchmark authority.

For `PB-MATRIX-INCLUSION-0-C`, later fixtures should include:

- one matrix revision registration;
- one revision readiness summary;
- one pressure-only post-inclusion handoff;
- one family closeout alignment.

Reject fixtures should include:

- revision registration without B inclusion decision;
- summary counts phrased as pass rate, solve rate, success rate, or benchmark
  coverage;
- handoff that grants batch execution or result projection authority;
- family closeout missing A, B, or C slice refs.

## Non-Outputs

`PB-MATRIX-INCLUSION-0` must not output:

- local case execution records;
- probe execution records;
- local trial dockets;
- retry request or dispatch rows;
- batch command execution records;
- candidate implementation artifacts;
- result projection rows;
- matrix result summary rows;
- benchmark scores or baseline-relative results;
- model rankings or leaderboard claims;
- official ProgramBench task execution rows;
- official runner/evaluator integration rows;
- hidden-test handling rows;
- generated official submissions;
- future-family selection.

## Recommended Slice Order

1. `PB-MATRIX-INCLUSION-0-A`: inclusion request, candidate intake,
   eligibility, control, and guardrail.
2. `PB-MATRIX-INCLUSION-0-B`: amendment plan, case delta, comparability
   delta, contamination delta, and inclusion decision.
3. `PB-MATRIX-INCLUSION-0-C`: matrix revision registration, readiness,
   pressure-only handoff, and family closeout.

Proceed to `PB-MATRIX-INCLUSION-0-A` only after this family mapping is
reviewed.
