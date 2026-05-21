# LOCKED_CONTINUATION_vNEXT_PLUS274

## Status

Bounded starter lock draft for `HOB-0-C` (delta attribution ledger,
stale-ledger invalidation report, integration handoff, and family closeout
alignment).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`HOB-0-C` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `HOB-0`
- slice: `HOB-0-C`
- branch-local execution target: `arc/hob-0-c`

## Purpose

Freeze the bounded `HOB-0-C` starter slice so the repo can attribute post-run
or post-observation pressure to numbered obligations, invalidate stale broker
ledgers when catalog/evidence identity changes, emit pressure-only integration
handoff rows, and align closeout for the `HOB-0` family.

`vNext+274` authorizes docs plus the next implementation path over the existing
repo-owned `adeu_obligation_broker` package. It does not authorize semantic
adjudication by the broker, closure recomputation outside released B records,
probe execution, command execution outside the implementation/test lane, worker
dispatch, code patch authority, product behavior claims, ProgramBench
integration, clean product truth claims, score-to-closure laundering,
future-family selection, release authority, or recursive policy amendment.

Controlling invariant:

```text
HOB-0-C may say which numbered obligations post-run pressure points at, which
ledgers are stale, and what pressure-only handoff remains.

HOB-0-C may not convert score movement, official-like failure rows, or
postmortem pressure into clean semantic evidence or product truth.
```

## Instantiated Here

- `HOB-0-C` instantiates the final deterministic broker seam:
  - existing repo-owned package:
    - `adeu_obligation_broker`
  - consumed released inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v86.md`
    - `docs/ARCHITECTURE_ADEU_HIERARCHICAL_OBLIGATION_BROKER_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_HIERARCHICAL_OBLIGATION_BROKER_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_HIERARCHICAL_OBLIGATION_BROKER_HOB_0C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS272.md`
    - `docs/ASSESSMENT_vNEXT_PLUS272_EDGES.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS273.md`
    - `docs/ASSESSMENT_vNEXT_PLUS273_EDGES.md`
    - `artifacts/agent_harness/v272/evidence_inputs/hob_0a_closeout_evidence_v272.json`
    - `artifacts/agent_harness/v273/evidence_inputs/hob_0b_closeout_evidence_v273.json`
  - consumed package surfaces:
    - `packages/adeu_obligation_broker/src/adeu_obligation_broker/hob_0a.py`
    - `packages/adeu_obligation_broker/src/adeu_obligation_broker/hob_0b.py`
    - `packages/adeu_obligation_broker/tests/test_hob_0a.py`
    - `packages/adeu_obligation_broker/tests/test_hob_0b.py`
    - `packages/adeu_obligation_broker/schema/`
  - emitted starter record shapes:
    - `repo_obligation_delta_attribution_ledger@1`
    - `repo_obligation_stale_ledger_invalidation_report@1`
    - `repo_obligation_broker_integration_handoff@1`
    - `repo_obligation_broker_family_closeout_alignment@1`

## Required Starter Vocabulary

Minimum `repo_obligation_delta_attribution_ledger@1` fields:

- `obligation_delta_attribution_ledger_ref`
- `catalog_id`
- `catalog_version`
- `catalog_hash`
- `run_before_ref`
- `run_after_ref`
- `changed_failure_rows`
- `delta_attribution_rows`
- `regression_rows`
- `rows_moved_to_other_failure_rows`
- `evidence_boundary_posture`
- `delta_authority_posture`

Delta attribution rows must include:

- `node_id`
- `macro_ref`
- `source_delta_ref`
- `attribution_kind`
- `attribution_confidence`
- `matrix_rows_green`
- `rows_moved_to_other_failure`
- `regressions`
- `interpretation`
- `closure_effect_posture`
- `evidence_boundary_posture`

Allowed per-row evidence boundary posture values:

```text
post_eval_pressure_only
local_locked_probe_delta
official_like_pressure
source_postmortem_pressure
clean_first_pass_disallowed
```

Minimum `repo_obligation_stale_ledger_invalidation_report@1` fields:

- `obligation_stale_ledger_invalidation_report_ref`
- `prior_catalog_id`
- `prior_catalog_version`
- `prior_catalog_hash`
- `current_catalog_id`
- `current_catalog_version`
- `current_catalog_hash`
- `invalidated_ledger_refs`
- `invalidated_probe_plan_refs`
- `invalidation_reason_rows`
- `stale_ledger_reuse_posture`

Minimum `repo_obligation_broker_integration_handoff@1` fields:

- `obligation_broker_integration_handoff_ref`
- `handoff_pressure_rows`
- `handoff_pressure_kind`
- `handoff_non_selection_posture`
- `programbench_integration_authority_posture`
- `semantic_compiler_integration_authority_posture`
- `probe_execution_authority_posture`
- `implementation_authority_posture`
- `future_family_selection_posture`

Allowed handoff pressure kinds:

```text
future_programbench_broker_integration_review
future_semantic_compiler_integration_review
future_probe_execution_governance_review
future_worker_taskpack_generation_review
future_implementation_authority_review
future_family_only
```

Minimum `repo_obligation_broker_family_closeout_alignment@1` fields:

- `obligation_broker_family_closeout_alignment_ref`
- `family_ref`
- `closed_slices`
- `slice_a_closeout_ref`
- `slice_b_closeout_ref`
- `slice_c_closeout_ref`
- `family_scope_posture`
- `residual_deferred_refs`
- `integration_authority_posture`
- `implementation_authority_posture`
- `future_family_selection_posture`

## Required APIs

`HOB-0-C` must provide deterministic functions or equivalent module APIs that:

- load released `HOB-0-A` and `HOB-0-B` records;
- validate catalog id/version/hash continuity before attribution;
- attribute delta pressure to known numbered node IDs only;
- reject score movement as macro closure unless released closure evidence
  supports that interpretation;
- invalidate stale ledger/probe-plan refs when catalog identity changes;
- emit pressure-only integration handoff rows without selecting future work;
- emit family closeout alignment only when A, B, and C records are accounted
  for;
- compute stable canonical hashes independent of input order.

## Required Validation

`HOB-0-C` must fail closed when:

- delta attribution rows reference unknown node IDs;
- attribution rows omit per-row evidence boundary posture;
- score movement is interpreted as macro closure without matrix closure
  evidence;
- official-like failures or post-eval pressure are labeled clean first-pass
  product truth;
- stale ledgers are reused after catalog hash changes without invalidation;
- integration handoff grants ProgramBench, semantic compiler, probe execution,
  implementation, worker dispatch, or future-family authority;
- family closeout lists slices other than `HOB-0-A`, `HOB-0-B`, and `HOB-0-C`;
- unresolved B blockers are hidden by family closeout;
- shuffled input order changes output ordering or canonical hashes.

## Required Starter Fixtures

`HOB-0-C` must include focused fixtures for:

1. local locked probe delta attributed to a terminal node without product truth;
2. official-like score movement cannot close a macro without closure evidence;
3. attribution row missing evidence boundary posture fails closed;
4. stale catalog hash invalidates prior ledger/probe-plan refs;
5. integration handoff is pressure-only and non-selecting;
6. unresolved B blocker prevents family closeout alignment;
7. family closeout rejects unknown slices;
8. shuffled input order preserves output order and canonical hashes.

## Deferred

Deferred to later families:

- actually running generated probes;
- dispatching workers;
- patching product code;
- ProgramBench integration;
- semantic compiler integration;
- implementation authority;
- official-result governance.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+274",
  "target_path": "HOB-0-C",
  "authority_layer": "lock",
  "selected_family": "HOB-0",
  "selected_slice": "HOB-0-C",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS274.md",
  "allowed_package": "packages/adeu_obligation_broker",
  "selected_record_shapes": [
    "repo_obligation_delta_attribution_ledger@1",
    "repo_obligation_stale_ledger_invalidation_report@1",
    "repo_obligation_broker_integration_handoff@1",
    "repo_obligation_broker_family_closeout_alignment@1"
  ],
  "local_gate": "make arc-start-check ARC=274",
  "non_authority_summary": "No semantic adjudication by the broker, closure recomputation outside released B records, probe execution, worker dispatch, product truth, score-to-closure laundering, ProgramBench integration, semantic compiler integration, implementation authority, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=274
```

Before opening the implementation PR:

```text
make check
```
