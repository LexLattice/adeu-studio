# Locked Continuation vNext+58 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS57.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS57.md`
- `docs/ASSESSMENT_vNEXT_PLUS57_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md`
- `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 11, 2026 UTC).

## Decision Basis

- `vNext+57` (`V35-B`, `B1`/`B2`) is merged on `main` with green CI checks.
- `vNext+57` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS57.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS57_EDGES.md` marks the `V35-B` single-builder delegation and
  reconciled-handoff baseline as closed and restores eligibility for a fresh visibility
  slice.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md` now names `V35-C` as the next default candidate
  after `V35-B` closure.
- current repo reality is narrower than a full worker-visibility UX lane:
  - `packages/urm_runtime/src/urm_runtime/worker.py` and
    `packages/urm_runtime/src/urm_runtime/copilot.py` already persist deterministic
    `codex_raw.ndjson` evidence for worker and copilot runs,
  - `packages/urm_runtime/src/urm_runtime/orchestration_state.py` and
    `packages/urm_runtime/src/urm_runtime/orchestration_evidence.py` already provide
    canonical orchestration-state, handoff, transition, write-lease, continuation-bridge,
    and closeout-evidence foundations,
  - `apps/api/src/adeu_api/urm_routes.py` already exposes normalized copilot event
    streaming via `urm_copilot_events_endpoint`,
  - no released canonical `worker_visibility_state@1` artifact exists on `main`,
  - no released transcript/progress read model projects explicit epistemic lanes over the
    persisted raw/event/handoff surfaces,
  - no released divergence-state surface exists for parsing failures or aborted
    reconciliation,
  - no released continuation/compaction-aware transcript visibility surface exists on
    `main`,
  - no released `v35c_transcript_visibility_evidence@1` closeout block exists on `main`,
  - no dynamic topology UX, runtime enforcement promotion, or direct worker/user boundary
    release is present on `main`.
- `vNext+58` therefore selects one thin `V35-C` baseline slice only:
  - read-only worker transcript and progress visibility over the now-frozen v56/v57
    orchestration-state and delegation substrate,
  - explicit epistemic-lane labeling and typed divergence surfacing,
  - explicit continuation-bridge and compaction-seam visibility where present,
  - canonical closeout evidence integration plus guard coverage,
  - no topology UX, runtime enforcement, multi-writer release, or direct worker/user
    interaction in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS57.md` remain authoritative for baseline
  continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v58,
  - v58 keyset must be exactly equal to v57 keyset,
  - baseline derived cardinality at v58 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v58 is explicit and narrow:
  - this arc authorizes one `L0` transcript/progress observability lane only,
  - no `L1` or `L2` authority-surface release is authorized in this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond `main_orchestrator`,
  - no multi-builder or multi-writer release is authorized in this arc.
- `V35-A` state artifacts and `V35-B` delegation/handoff surfaces remain frozen
  prerequisites and are not redefined by this arc.
- The multi-role constitution remains a frozen prerequisite input:
  - `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json` remains the canonical draft contract
    surface,
  - `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md` and
    `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md` remain derived interpretive inputs,
  - this arc may implement the `V35-C` visibility baseline only and may not widen the
    constitutional surface beyond those draft artifacts.
- `V35-C` release-shape lock for v58 is frozen:
  - this arc is a read-only transcript/progress visibility slice only,
  - visibility logic must prefer `packages/urm_runtime` or an explicit new read-model
    surface rather than silent accretion into `packages/adeu_agent_harness`,
  - worker transcript visibility, delegated self-report visibility, and explicit
    divergence rendering remain observational only in this arc,
  - dynamic topology UX and runtime enforcement remain out of scope for this arc,
  - no direct worker-to-user authority surface is authorized in this arc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `C1` Canonical transcript/progress visibility read-model baseline (`V35-C`)
2. `C2` Transcript visibility evidence + divergence/guard suite (`V35-C`)

Out-of-scope note:

- dynamic topology/duty map UX in this arc,
- runtime enforcement of the constitutional fail-closed conditions in this arc,
- any direct user-to-worker interaction beyond orchestrator mediation in this arc,
- multi-builder or multi-writer execution in this arc,
- treating raw transcript or worker self-report text as accepted truth by visibility alone,
- closeout hardening bundle (`O1`/`O2`/`O3`) implementation in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v58)

- v59+ `V35-D` dynamic topology/duty map UX
- v60+ `V35-E` runtime enforcement and promotion hardening
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold
- multi-builder execution, direct worker/user interaction, richer topology UX, and
  stronger authority-surface hardening remain deferred follow-ons under
  `docs/FUTURE_CLEANUPS.md`

## V57 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS57.md",
  "target": "V35-C-baseline",
  "required_continuity_guards": [
    "V35_B_B1_DELEGATION_SCOPE_AND_LEASE_BASELINE_GREEN",
    "V35_B_B2_DELEGATION_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v57_v35b_delegation_and_handoff_contracts_remain_frozen_while_v35c_worker_transcript_and_progress_visibility_are_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v58.
- this narrowed machine-checkable consumption block is v57-local only and does not weaken
  the global continuity locks declared above; v36-v57 baseline continuity remains in force
  for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V35-C Transcript Visibility Contract (Machine-Checkable)

```json
{
  "schema": "v35c_transcript_visibility_contract@1",
  "target_arc": "vNext+58",
  "target_path": "V35-C",
  "preserved_authority_inputs": {
    "v35a_state_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md#v35a_orchestration_state_contract@1",
    "v35b_delegation_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS57.md#v35b_delegation_handoff_contract@1",
    "multi_role_contract_baseline": "docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json",
    "multi_role_lock_baseline": "docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md",
    "multi_role_policy_baseline": "docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md",
    "normalized_event_schema": "urm-events@1",
    "orchestration_state_snapshot_schema": "orchestration_state_snapshot@1",
    "execution_topology_state_schema": "execution_topology_state@1",
    "role_handoff_envelope_schema": "role_handoff_envelope@1",
    "copilot_raw_transcript_surface": "evidence/codex/copilot/<session>/codex_raw.ndjson",
    "child_raw_transcript_surface": "evidence/codex/agent/<child>/codex_raw.ndjson",
    "copilot_event_stream_endpoint": "apps/api/src/adeu_api/urm_routes.py::urm_copilot_events_endpoint",
    "v35b_delegation_handoff_evidence": "required_frozen_precondition"
  },
  "visibility_requirements": {
    "worker_visibility_state_schema": "worker_visibility_state@1",
    "worker_visibility_state_materializer_required": true,
    "worker_visibility_foundation_package": "packages/urm_runtime",
    "read_only_visibility_required": true,
    "orchestrator_primary_interaction_boundary_required": true,
    "epistemic_lane_enum": [
      "raw_transcript",
      "worker_self_report",
      "reconciled_handoff",
      "orchestrator_judgment"
    ],
    "epistemic_lane_label_required": true,
    "epistemic_lane_absence_policy": "explicit_status_required_not_silent_omission",
    "epistemic_lane_status_enum": [
      "available",
      "pending_parse",
      "pending_reconciliation",
      "not_available",
      "parsing_failure",
      "reconciliation_aborted"
    ],
    "divergence_state_enum": [
      "aligned",
      "raw_only",
      "worker_self_report_only",
      "lane_disagreement",
      "parsing_failure",
      "reconciliation_aborted"
    ],
    "explicit_divergence_render_required": true,
    "progress_fields_required": [
      "worker_session_id",
      "parent_session_id",
      "role",
      "requested_role",
      "granted_role",
      "delegation_task_kind",
      "status",
      "last_action",
      "blocking_state",
      "scope_owned",
      "scope_remaining",
      "latest_visible_event",
      "reconciliation_status"
    ],
    "progress_state_source_policy": "derived_from_v35a_state_v35b_handoff_and_urm_runtime_events_only_no_ad_hoc_worker_summary",
    "raw_transcript_authority_policy": "visibility_alone_confers_no_acceptance_authority",
    "worker_self_report_authority_policy": "self_report_non_authoritative_until_reconciled",
    "reconciled_handoff_surface_policy": "present_only_after_explicit_orchestrator_reconciliation",
    "orchestrator_judgment_surface_policy": "present_only_when_explicit_orchestrator_judgment_is_recorded",
    "compaction_visibility_required": true,
    "continuation_bridge_visibility_policy": "explicit_compaction_seams_and_bridge_linkage_required_not_silent_flattening",
    "deterministic_redaction_and_scope_boundary_required": true,
    "worker_direct_user_boundary_forbidden": true
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v35c_transcript_visibility_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "evidence_input_path",
      "worker_visibility_state_path",
      "worker_visibility_state_hash",
      "orchestration_state_snapshot_path",
      "orchestration_state_snapshot_hash",
      "role_handoff_envelope_path",
      "role_handoff_envelope_hash",
      "read_only_visibility_preserved",
      "epistemic_lane_labels_present",
      "explicit_lane_absence_materialized",
      "explicit_divergence_state_materialized",
      "continuation_bridge_visibility_present_when_available",
      "no_ad_hoc_progress_summary_bypass",
      "raw_transcript_non_authoritative",
      "worker_self_report_non_authoritative_until_reconciled",
      "worker_direct_user_boundary_forbidden",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v57",
      "notes"
    ]
  },
  "test_requirements": {
    "worker_visibility_state_deterministic": true,
    "raw_transcript_lane_recorded": true,
    "worker_self_report_lane_recorded_or_explicitly_absent": true,
    "reconciled_handoff_lane_explicitly_absent_or_present_with_status": true,
    "orchestrator_judgment_lane_explicitly_absent_or_present_with_status": true,
    "explicit_divergence_state_required_when_lanes_do_not_align": true,
    "progress_fields_populated_from_canonical_state": true,
    "compaction_seam_and_bridge_visibility_preserved": true,
    "no_ad_hoc_progress_summary_bypass_guarded": true,
    "raw_transcript_authority_drift_rejected": true,
    "worker_direct_user_boundary_forbidden": true
  },
  "fail_closed_conditions": [
    "worker_visibility_state_missing",
    "epistemic_lane_label_missing",
    "lane_absence_silently_omitted",
    "raw_transcript_rendered_as_authoritative",
    "worker_self_report_rendered_as_reconciled_without_explicit_reconciliation",
    "divergence_state_missing_when_lanes_do_not_align",
    "compaction_or_continuation_bridge_continuity_silently_flattened",
    "progress_fields_missing_or_derived_from_ad_hoc_summary",
    "redaction_or_scope_boundary_nondeterministic",
    "worker_direct_user_boundary_established"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

Interpretive notes:

- `worker_self_report` is observational visibility over worker-claimed state or typed
  handoff content only; it remains non-authoritative until explicit orchestrator
  reconciliation.
- `execution_topology_state@1` remains a frozen prerequisite input in v58 because the
  visibility read model still depends on canonical role/scope/edge state as source
  context even though topology UX remains explicitly out of scope.
- `reconciled_handoff` and `orchestrator_judgment` must be explicitly present or
  explicitly absent with a lane status; silent omission is invalid.
- transcript visibility must surface continuation bridges and compaction seams explicitly
  when present rather than flattening pre/post-compaction history into one uninterrupted
  conversation.
- raw transcript text, self-report text, and progress summaries remain observational only;
  visibility alone does not create accepted truth or a direct authority surface.

## C1) Canonical Transcript/Progress Visibility Read-Model Baseline (`V35-C`)

### Goal

Make `V35-C` real as a read-only worker transcript/progress visibility surface over the
now-frozen v56/v57 state and delegation substrate.

### Scope

- define a deterministic canonical `worker_visibility_state@1` artifact or equivalent
  read model that projects:
  - epistemic lanes,
  - current worker status,
  - last visible action,
  - blocking state,
  - current delegated scope,
  - latest visible event,
  - reconciliation status;
- bind transcript/progress visibility to the frozen lane taxonomy:
  - `raw_transcript`,
  - `worker_self_report`,
  - `reconciled_handoff`,
  - `orchestrator_judgment`;
- require explicit lane-status values rather than silently omitting unavailable or
  unreconciled lanes;
- render continuation-bridge and compaction-seam continuity explicitly when present;
- preserve orchestrator-centric interaction as the sole authoritative boundary;
- keep visibility derived from canonical runtime state, persisted raw/event evidence, and
  handoff surfaces rather than ad hoc summaries.

### Locks

- v58 must not release dynamic topology UX.
- v58 must not release runtime enforcement beyond read-model materialization and guard
  checks.
- raw transcript text and worker self-report text remain non-authoritative by visibility
  alone.
- transcript/progress surfaces must not collapse `raw_transcript`, `worker_self_report`,
  `reconciled_handoff`, and `orchestrator_judgment` into one undifferentiated authority
  surface.
- if visible lanes diverge or a downstream lane is unavailable, the surface must render
  explicit typed lane status or divergence state rather than imply successful parse or
  reconciliation.
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

### Acceptance

- the user can inspect builder/support worker transcript/progress visibility surfaces with:
  - explicit epistemic-lane labels,
  - explicit lane-status values,
  - explicit divergence state when lanes do not align,
  - current status, scope, and blocking context derived from canonical state,
  - explicit continuation-bridge and compaction visibility when present,
  - no authority drift.

## C2) Transcript Visibility Evidence + Divergence/Guard Suite (`V35-C`)

### Goal

Use the transcript/progress visibility surfaces as an actual closeout-grade evidence lane
and prove the observational-only constitutional invariants hold under the current narrow
scope.

### Scope

- add canonical closeout evidence for the `V35-C` visibility lane;
- add deterministic guard coverage for:
  - missing visibility artifacts,
  - missing epistemic lane labels,
  - silently omitted absent lanes,
  - missing explicit divergence state when lane data does not align,
  - flattened continuation/compaction visibility,
  - ad hoc progress-summary bypass of canonical state/event sources,
  - raw transcript or self-report authority drift,
  - worker direct user-boundary violations;
- keep the lane strictly pre-topology and pre-enforcement.

### Locks

- evidence is closeout-authoritative only via deterministic artifact hashes.
- the `V35-C` evidence lane must not redefine topology UX or runtime enforcement
  semantics.
- closeout proof must distinguish between:
  - raw transcript visibility,
  - worker self-report visibility,
  - reconciled handoff visibility,
  - orchestrator judgment visibility,
  - docs-side `v35c_transcript_visibility_evidence@1`.
- runtime-observability evidence remains required and informational-only.

### Acceptance

- closeout path emits the required `v35c_transcript_visibility_evidence@1` block;
- deterministic guard suites prove the observational-only transcript posture remains
  intact;
- explicit lane-status and divergence-state handling is required rather than silent
  omission or silent truth promotion;
- continuation/compaction visibility remains explicit where present;
- no topology UX or runtime enforcement surface is required for the arc to pass.

## Stop-Gate Impact (v58)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80`
  fail closed.
- v58 closeout must include runtime-observability comparison row against v57 baseline.
- v58 closeout must include metric-key continuity assertion against v57 baseline.
- v58 closeout must include transcript-visibility evidence block:
  - block schema is docs-only `v35c_transcript_visibility_evidence@1`,
  - schema is docs-defined, but the evidence content must be materialized as a
    deterministic JSON evidence input artifact, included in the canonical closeout path,
    and treated as closeout-authoritative only after implementation,
  - required keys are:
    - `schema`
    - `contract_source`
    - `evidence_input_path`
    - `worker_visibility_state_path`
    - `worker_visibility_state_hash`
    - `orchestration_state_snapshot_path`
    - `orchestration_state_snapshot_hash`
    - `role_handoff_envelope_path`
    - `role_handoff_envelope_hash`
    - `read_only_visibility_preserved`
    - `epistemic_lane_labels_present`
    - `explicit_lane_absence_materialized`
    - `explicit_divergence_state_materialized`
    - `continuation_bridge_visibility_present_when_available`
    - `no_ad_hoc_progress_summary_bypass`
    - `raw_transcript_non_authoritative`
    - `worker_self_report_non_authoritative_until_reconciled`
    - `worker_direct_user_boundary_forbidden`
    - `verification_passed`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v57`
    - `notes`

## Error/Exit Policy (v58)

- No new stop-gate error-code family is introduced in this arc.
- Existing component-local diagnostics remain authoritative in their respective paths.
- If v58 introduces transcript/progress visibility diagnostics, they must remain
  deterministic, error-only, and fail closed on invalid inputs.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail
  closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add v35c transcript visibility baseline`
2. `tests: add v35c transcript visibility evidence and guard suite`

## Intermediate Preconditions (for v58 start)

1. v57 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v57 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS57.md`
3. Existing `V35-B` closeout artifacts remain available at v58 start:
   - `artifacts/quality_dashboard_v57_closeout.json`
   - `artifacts/stop_gate/metrics_v57_closeout.json`
   - `artifacts/stop_gate/report_v57_closeout.md`
   - `artifacts/agent_harness/v57/evidence_inputs/v35b_delegation_handoff_evidence_v57.json`
4. Existing `urm_runtime` foundations remain available at v58 start:
   - `packages/urm_runtime/src/urm_runtime/models.py`
   - `packages/urm_runtime/src/urm_runtime/roles.py`
   - `packages/urm_runtime/src/urm_runtime/worker.py`
   - `packages/urm_runtime/src/urm_runtime/child_dispatch.py`
   - `packages/urm_runtime/src/urm_runtime/storage.py`
   - `packages/urm_runtime/src/urm_runtime/orchestration_state.py`
   - `packages/urm_runtime/src/urm_runtime/orchestration_evidence.py`
   - `packages/urm_runtime/src/urm_runtime/copilot.py`
   - `apps/api/src/adeu_api/urm_routes.py`
5. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
6. No additional `L1` or `L2` boundary release beyond v57 baseline is introduced in this
   arc.

## Exit Criteria (Draft)

- `C1` and `C2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- `V35-C` closes the read-only worker transcript/progress visibility gap without widening
  into topology UX or runtime enforcement.
- v58 closeout evidence includes runtime-observability comparison row against v57
  baseline, metric-key continuity assertion against v57 baseline, and
  `v35c_transcript_visibility_evidence@1`.
- visibility artifacts are deterministic and sufficient to reconstruct worker lanes,
  scope, status, blocking context, divergence state, and continuation/compaction
  visibility.
- raw transcript and worker self-report remain non-authoritative until explicit
  reconciliation or orchestrator judgment.
- v36-v57 continuity remains green and unreverted.
- no solver semantics contract delta and no trust-lane regression are introduced.
