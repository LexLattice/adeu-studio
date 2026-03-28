# Locked Continuation vNext+94

Status: `V42-F` implementation contract.

## V94 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v42f_arc_submission_execution_contract@1",
  "target_arc": "vNext+94",
  "target_path": "V42-F",
  "target_scope": "arc_direct_submission_execution_and_bounded_orchestration_posture_over_released_scorecard",
  "task_packet_schema": "adeu_arc_task_packet@1",
  "observation_frame_schema": "adeu_arc_observation_frame@1",
  "hypothesis_frame_schema": "adeu_arc_hypothesis_frame@1",
  "action_proposal_schema": "adeu_arc_action_proposal@1",
  "rollout_trace_schema": "adeu_arc_rollout_trace@1",
  "local_eval_record_schema": "adeu_arc_local_eval_record@1",
  "scorecard_manifest_schema": "adeu_arc_scorecard_manifest@1",
  "submission_execution_record_schema": "adeu_arc_submission_execution_record@1",
  "implementation_packages": [
    "adeu_arc_agi",
    "adeu_arc_solver"
  ],
  "authoritative_upstream_source": "V42-A_V42-B_V42-C_V42-D_V42-E_released_artifacts",
  "local_first_foundation_required": true,
  "submission_lifecycle_stage_separation_required": true,
  "submission_lifecycle_transition_matrix_fail_closed_required": true,
  "submission_authorization_gate_required": true,
  "submission_execution_authority_gate_required": true,
  "submission_execution_receipt_binding_required": true,
  "result_import_authority_gate_required": true,
  "official_authority_import_required_for_result_posture": true,
  "request_receipt_result_identity_chain_binding_required": true,
  "submission_payload_lineage_binding_required": true,
  "submission_result_replay_binding_required": true,
  "deterministic_time_evidence_sourcing_required": true,
  "local_official_submission_separation_required": true,
  "deterministic_replay_scope_clarified_required": true,
  "summary_non_authoritative_required": true,
  "bounded_orchestration_constraint_register_required": true,
  "deferred_authority_assertions_non_authoritative_required": true,
  "competition_submission_claim_posture_required": true,
  "post_hoc_success_authority_laundering_forbidden": true,
  "benchmark_tournament_orchestration_execution_deferred": true,
  "api_web_operator_surfaces_deferred": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "decomposition_doc": "docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v24.md"
}
```

## Slice

- Arc label: `vNext+94`
- Family label: `V42-F`
- Scope label: ARC direct submission execution and bounded orchestration posture over released scorecard

## Objective

Introduce the first submission-execution widening for ARC participation by releasing one
canonical `adeu_arc_submission_execution_record@1` over released
`V42-A`/`V42-B`/`V42-C`/`V42-D`/`V42-E` lineage, while preserving explicit
submission-lifecycle stage separation (authorization, execution/receipt, and result
import), local-vs-official submission separation, deterministic submission/result lineage
binding, settlement-carry posture, and fail-closed anti-overclaim posture.

This slice establishes the first ADEU ARC submission-execution substrate for:

- deterministic submission execution-record emission over one released scorecard chain;
- explicit authorization gate before any submitted-execution posture is emitted;
- explicit submission payload lineage/hash binding and replay references;
- explicit submission receipt binding separate from result-import authority binding;
- explicit result-import authority validation before official-result posture is emitted;
- explicit bounded orchestration posture without tournament execution widening;
- deterministic local fixture replay for accepted and rejected submission cases.

This slice remains deliberately prior to:

- benchmark tournament orchestration execution;
- API/web operator routes and productized workbench surfaces;
- generalized multi-agent or multi-benchmark orchestration.

Its job is to prove that direct submission execution can remain explicitly constrained by
released authority posture and typed lineage before broader deployment seams are widened.

## Frozen Implementation Decisions

1. Active package strategy:
   - activate bounded `V42-F` surfaces in:
     - `packages/adeu_arc_agi` for authoritative schema ownership and submission
       execution artifact handling;
     - `packages/adeu_arc_solver` for bounded submission-execution derivation helpers;
   - no tournament-orchestration or product-surface helpers may be activated in this
     slice.
2. Upstream authority strategy:
   - `vNext+94` must consume released:
     - `adeu_arc_task_packet@1`,
     - `adeu_arc_observation_frame@1`,
     - `adeu_arc_hypothesis_frame@1`,
     - `adeu_arc_action_proposal@1`,
     - `adeu_arc_rollout_trace@1`,
     - `adeu_arc_local_eval_record@1`,
     - `adeu_arc_scorecard_manifest@1`
     as authoritative submission inputs;
   - the released scorecard manifest is an upstream authority-posture input only; by
     itself it is not sufficient to prove submission authorization or result-import
     authority for a concrete request chain;
   - it may not bypass released lineage with prompt-authored ambient reinterpretation.
3. Submission lifecycle strategy:
   - `adeu_arc_submission_execution_record@1` is authoritative for bounded submission
     lifecycle posture in this slice;
   - each record must carry released lineage refs from task packet through scorecard
     manifest plus three explicit lifecycle stages:
     - `submission_authorization_status`
     - `submission_execution_status`
     - `result_import_status`
   - stage fields are machine-checkable and may not be collapsed into one prose status.
   - each lifecycle stage must use bounded enum values:
     - `submission_authorization_status`:
       `not_authorized | deferred | authorized`
     - `submission_execution_status`:
       `not_submitted | submitted_pending_receipt | submitted_acknowledged | submission_failed`
     - `result_import_status`:
       `not_imported | deferred | official_imported | import_failed`
   - lifecycle transitions must be validated against a released transition matrix and
     fail closed on contradictory state combinations.
4. Submission authorization strategy:
   - authorization to attempt submission is distinct from execution and from official
     result import;
   - authorization posture must be typed by:
     - `submission_authorization_source_kind`
     - `submission_authorization_validity`
     - `submission_authorization_basis_refs`
   - submitted execution states are invalid unless authorization is explicitly valid;
   - local-shadow or deferred scorecard posture may be represented only as
     non-submitted/not-authorized or deferred status and may not be laundered into
     authorized submission.
5. Submission execution and receipt strategy:
   - submission execution must be bound to deterministic transport/request identity:
     - `submission_transport_profile`
     - `external_request_ref`
     - `submission_payload_ref`
     - `submission_payload_hash`
   - submission receipt is distinct from payload emission and must be typed by:
     - `submission_receipt_ref`
     - `submission_receipt_hash`
     - `submission_receipt_ts`
   - records may not claim acknowledged submission completion without explicit receipt
     binding.
6. Result-import authority strategy:
   - result import is distinct from submission execution and must be typed by:
     - `result_source_kind`
     - `result_authority_validity`
     - `result_authority_basis_refs`
     - `result_import_ref`
     - `result_import_hash`
     - `result_import_ts`
   - official-result posture may be emitted only when result import authority is valid;
   - `submission_result_summary` is descriptive-only and may not override typed status
     and authority surfaces.
7. Identity-chain binding strategy:
   - submission request, receipt, and result import must bind to one external identity
     chain for the same request lineage:
     - `external_request_ref`
     - `environment_ref`
     - `session_ref`
     - `competition_scope_ref`
   - payload, receipt, and result-import refs/hashes may not be attached across mixed
     request chains.
8. Bounded orchestration strategy:
   - this slice must represent orchestration posture as a typed constraint register, not
     a single enum value:
     - `bounded_orchestration_constraint_register`
   - constraint register entries must include at least:
     - `single_submission_only`
     - `no_tournament_execution`
     - `no_parallel_competition_fanout`
     - `deferred_multi_run`
   - benchmark-tournament orchestration execution remains deferred;
   - submission records may not mint tournament authority in `V42-F`.
9. Settlement-carry strategy:
   - settlement/ambiguity/claim-posture carry from released decomposition/action/eval/
     scorecard artifacts must remain explicit in submission outputs;
   - successful submission outcomes may not mint universal necessity or blanket
     competitiveness claims.
10. Deterministic replay and time strategy:
   - deterministic replay in `V42-F` means deterministic derivation and validation of
     submission records over fixed released lineage plus fixed receipt/result evidence;
   - `submission_request_ts`, `submission_receipt_ts`, and `result_import_ts` may not be
     synthesized at derivation time unless fixture-anchored or imported from fixed
     external evidence;
   - when present for the same request chain, timestamps must be monotonic:
     `submission_request_ts <= submission_receipt_ts <= result_import_ts`;
   - this slice does not claim deterministic reproduction of external system behavior.
11. Narrative-field non-authority strategy:
   - `submission_result_summary` and `deferred_authority_assertions` are descriptive
     only and may not override typed lifecycle or authority-validity surfaces.
12. Local-first and widening strategy:
    - `vNext+94` widens into direct submission execution posture only;
    - tournament orchestration and operator product surfaces remain deferred.
13. Path decomposition strategy:
   - `vNext+94` is the first concrete `V42-F` arc;
   - further deployment widening remains available only for later concrete arcs.

## Required Deliverables

1. New typed submission-execution surface:
   - extend bounded ARC helpers under `packages/adeu_arc_agi` and
     `packages/adeu_arc_solver` to materialize canonical submission execution records
     over released `V42-A`/`V42-B`/`V42-C`/`V42-D`/`V42-E` artifacts;
   - export schema helpers for authoritative and mirrored JSON-schema output;
   - keep tournament/API/web surfaces out of scope.
2. Canonical artifact:
   - `adeu_arc_submission_execution_record@1`
3. Deterministic entrypoints that:
   - consume one released task/observation/hypothesis/action/rollout/local-eval/scorecard chain;
   - materialize one canonical submission execution record;
   - fail closed when lineage, lifecycle-stage typing, authorization gating,
     execution/receipt binding, result-import authority, or settlement-carry posture is
     invalid.
4. Top-level schema anchors for `adeu_arc_submission_execution_record@1`:
   - `schema`
   - `submission_execution_id`
   - `task_packet_id`
   - `task_packet_ref`
   - `observation_frame_id`
   - `observation_frame_ref`
   - `hypothesis_frame_id`
   - `hypothesis_frame_ref`
   - `action_proposal_id`
   - `action_proposal_ref`
   - `rollout_trace_id`
   - `rollout_trace_ref`
   - `local_eval_record_id`
   - `local_eval_record_ref`
   - `scorecard_manifest_id`
   - `scorecard_manifest_ref`
   - `environment_ref`
   - `session_ref`
   - `competition_scope_ref`
   - `model_id`
   - `run_id`
   - `submission_authorization_status`
   - `submission_authorization_source_kind`
   - `submission_authorization_validity`
   - `submission_authorization_basis_refs`
   - `submission_execution_status`
   - `submission_transport_profile`
   - `external_request_ref`
   - `submission_payload_ref`
   - `submission_payload_hash`
   - `submission_request_ts`
   - `submission_receipt_ref`
   - `submission_receipt_hash`
   - `submission_receipt_ts`
   - `result_import_status`
   - `result_source_kind`
   - `result_authority_validity`
   - `result_authority_basis_refs`
   - `result_import_ref`
   - `result_import_hash`
   - `result_import_ts`
   - `lifecycle_transition_matrix_ref`
   - `submission_result_posture`
   - `submission_result_summary`
   - `bounded_orchestration_constraint_register`
   - `settlement_posture_carry`
   - `deferred_authority_assertions`
   - `evidence_refs`
5. Deterministic laws that fail closed on at least:
   - any submission record not lineage-bound to one released upstream chain including
     one released scorecard manifest;
   - any submission record missing lifecycle-stage fields
     (`submission_authorization_status`, `submission_execution_status`,
     `result_import_status`);
   - any lifecycle-stage value outside released enums for authorization, execution, or
     result import;
   - any lifecycle state combination or transition that violates the released transition
     matrix;
   - any submitted execution state emitted without valid submission authorization
     surfaces and basis refs;
   - any submitted-acknowledged state emitted without explicit receipt refs/hashes;
   - any result-import state emitted before submitted-acknowledged execution on the same
     request chain;
   - any submission payload emitted without deterministic payload ref/hash binding;
   - any official result-import state emitted without explicit valid result authority
     refs/hashes;
   - any request/receipt/result refs that fail to bind to one consistent external
     identity chain (`external_request_ref`, `environment_ref`, `session_ref`,
     `competition_scope_ref`);
   - any timestamp field synthesized without fixture or fixed-evidence sourcing;
   - any non-monotonic timestamp ordering when request/receipt/import timestamps are all
     present for the same request chain;
   - any local-shadow or deferred scorecard posture represented as official submission
     authority;
   - any summary field presented as authoritative over typed lifecycle and authority
     surfaces;
   - any `deferred_authority_assertions` content treated as authoritative over typed
     lifecycle and authority-validity fields;
   - any submission record that omits settlement-posture carry while claiming finality;
   - any submission record that launders one successful submission into universal necessity;
   - any submission record that mints tournament/API/web operator authority in `V42-F`.
6. Committed reference fixtures:
   - one accepted fixture ladder under `apps/api/fixtures/arc_agi/vnext_plus94/`
     covering:
     - one accepted lifecycle case: authorized-not-submitted;
     - one accepted lifecycle case: submitted and externally acknowledged (receipt bound)
       without official result import;
     - one accepted lifecycle case: official result imported with valid result authority
       refs;
     - one rejected submission record with local-shadow authority laundering;
     - one rejected submission record with missing payload lineage/hash binding;
     - one rejected submission record claiming submitted-acknowledged without receipt
       binding;
     - one rejected submission record with contradictory lifecycle stages
       (for example `result_import_status = official_imported` with
       `submission_execution_status = not_submitted`);
     - one rejected submission record claiming official result import without valid
       result authority binding;
     - one rejected submission record with request/receipt/result cross-chain identity
       mismatch;
     - one rejected submission record with tournament/API/web authority leakage.
   - accepted fixtures must prove:
     - deterministic replay;
     - explicit stage-separated lifecycle handling (authorization, execution/receipt,
       result import);
     - lifecycle transition-matrix conformance;
     - explicit payload/receipt/result lineage binding;
     - explicit request/receipt/result cross-chain identity binding;
     - explicit bounded orchestration posture;
     - no tournament/API/web authority leakage.
7. Python tests covering:
   - schema/model validation for submission execution artifacts;
   - authoritative/mirrored schema export parity;
   - deterministic replay from accepted fixture ladder;
   - acceptance of the three lifecycle authority cases above;
   - rejection of local-as-official submission authority laundering;
   - rejection of payload/receipt/result lineage omissions;
   - rejection of contradictory lifecycle stage combinations;
   - rejection of request/receipt/result cross-chain identity mismatch;
   - rejection of settlement-posture erasure;
   - rejection of tournament/API/web authority leakage in `V42-F`.

## Hard Constraints

- `vNext+94` may not reopen or redefine released `V41`, `V42-A`, `V42-B`, `V42-C`,
  `V42-D`, or `V42-E` contracts.
- `vNext+94` may not ship:
  - benchmark tournament orchestration execution,
  - API/web operator routes,
  - generalized multi-benchmark or multi-agent orchestration.
- `vNext+94` may not emit submitted-execution posture without explicit valid submission
  authorization status and basis refs.
- `vNext+94` may not emit submitted-acknowledged posture without explicit receipt refs
  and receipt hash binding.
- `vNext+94` may not emit official result-import posture unless result source kind is
  explicitly `official_imported` with valid result authority basis refs.
- `vNext+94` may not treat local-shadow or deferred scorecard posture as official
  submission authority.
- `vNext+94` may not collapse authorization/execution/result lifecycle stages into one
  summary-only status.
- `vNext+94` may not encode bounded orchestration as a single mutually-exclusive enum
  when constraints are simultaneous; it must use a typed constraint register.
- `vNext+94` may not treat `deferred_authority_assertions` as authoritative evidence.
- `vNext+94` may not mint post-hoc universal necessity or blanket competitiveness claims
  from bounded submission outcomes.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- submission-execution schema release, deterministic derivation, fixtures, and
  fail-closed authority-boundary rules are one bounded seam;
- splitting these across multiple PRs would create artificial staging within the same
  `V42-F` boundary without reducing semantic risk.
