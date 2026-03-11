# Draft Next Arc Options v9 (Post vNext+55, Post V34 Closure)

This document defines the post-`vNext+55` planning baseline for the next ADEU-governed
implementation family.

Status: active planning draft (`V34-A` through `V34-G` closed; next family selection in
progress).

Goal:

- carry forward the completed `V34` trust/distribution line without reopening it;
- turn the multi-role execution constitution into an actual implementation roadmap;
- make the main orchestrator the primary user-facing surface while preserving ADEU
  governance authority;
- add worker visibility and topology observability without weakening single-writer
  discipline, auditability, or closeout rigor.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior changes.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS55.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS55.md`
- `docs/ASSESSMENT_vNEXT_PLUS55_EDGES.md`
- `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

## Baseline Agreement (Current Ground Truth)

- Baseline implementation is `vNext+55` (`V34-G`) on `main`.
- `V34-A` through `V34-G` are closed.
- `stop_gate_metrics@1` remains the active stop-gate schema family.
- Stop-gate metric-key cardinality baseline remains `80` (derived from `metrics` object
  keys only).
- Determinism/replayability, canonical JSON hashing, and fail-closed posture remain
  mandatory.
- The multi-role execution bundle currently exists as a draft constitution only:
  - canonical JSON contract:
    `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json`
  - derived lock:
    `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`
  - derived policy:
    `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md`
- The closeout hardening bundle exists as a separate operational proposal only:
  - `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `packages/urm_runtime` already provides substantial sub-agent foundation for:
  - worker lifecycle,
  - roles,
  - child dispatch/workflow/recovery,
  - capability policy,
  - event tracking.
- `packages/adeu_agent_harness` is now primarily a dense artifact-pipeline package; this
  family should not silently pile orchestration governance and UX state into the largest
  existing pipeline modules without explicit decomposition.

## Planning Boundary (For This Family)

- No solver/runtime semantics contract change is authorized by this planning draft.
- No implicit `L2` boundary release is authorized by this planning draft.
- No implicit carryover of multi-writer authority is authorized.
- No worker may acquire governance authority by UI affordance, transcript visibility, or
  artifact execution side effects.
- No worker may become a user-facing authority surface by default.
- Worker transcript visibility and topology visualization must remain observational and
  non-authoritative unless explicit future lock text says otherwise.
- The closeout hardening bundle remains a separate operational track and is not implicitly
  folded into the next execution family unless explicitly locked later.
- Orchestration-state, delegation, worker observability, and role-enforcement logic should
  prefer `packages/urm_runtime` or a new dedicated orchestration surface rather than
  further accreting into `packages/adeu_agent_harness` pipeline files by default.

## Naming Convention (New Family)

- `V35-*` identifiers are reserved for single-path families in this planning cycle.
- `B35-*` identifiers are reserved for explicit multi-path bundles.
- `V34-*` remains historical/closed and is not reused.

## Family Scale Note

- `V35` currently defines `5` paths (`V35-A` through `V35-E`) with a default sequential
  planning span of `vNext+56` through `vNext+60`.
- This sequence is planning intent only; each arc still requires explicit lock/assessment/
  decision docs before implementation authority is granted.

## Vision Contract (Planning-Level)

- Authoritative sources:
  - ADEU governance docs and accepted evidence artifacts;
  - canonical execution-state artifacts, write-lease state, role-transition records, and
    reconciled handoff envelopes if this family is implemented.
- Non-authoritative sources:
  - worker prose claims before reconciliation;
  - runtime event streams before canonical reconciliation or acceptance;
  - chat visibility surfaces by themselves;
  - topology/map visualizations by themselves;
  - UI summaries that are not backed by canonical execution-state artifacts.
- Operational rule:
  - the user should be able to talk to one main orchestrator surface;
  - the orchestrator may delegate execution to workers;
  - the user may inspect worker progress and chats read-only;
  - governance authority, acceptance, and closeout remain in ADEU.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "agent_harness_planning_baseline@2",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v8.md",
  "closed_path_family": "V34",
  "closed_paths": [
    "V34-A",
    "V34-B",
    "V34-C",
    "V34-D",
    "V34-E",
    "V34-F",
    "V34-G"
  ],
  "next_path_family": "V35",
  "v35_path_count": 5,
  "v35_default_arc_span": {
    "from": "vNext+56",
    "to": "vNext+60"
  },
  "default_next_arc_candidate": "V35-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality_baseline": 80,
  "no_implicit_metric_key_expansion": true,
  "artifact_authority_model": "canonical_artifacts_only",
  "control_execution_split": {
    "control_plane": "ADEU",
    "execution_plane": "Codex"
  },
  "multi_role_contract_baseline": "docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json",
  "single_writer_default": true,
  "support_roles_non_authoritative": true,
  "worker_direct_user_boundary_forbidden": true,
  "orchestration_foundation_package": "packages/urm_runtime",
  "pipeline_package_accretion_policy": "avoid_new_multi_role_governance_logic_in_adeu_agent_harness_without_explicit_decomposition_or_lock_text",
  "canonical_orchestration_identity_fields": [
    "orchestrator_session_id",
    "worker_session_id",
    "parent_session_id",
    "event_cursor",
    "last_reconciled_event",
    "continuation_bridge_ref"
  ],
  "runtime_event_truth_policy": "runtime_events_are_source_surfaces_only_not_accepted_truth_without_canonical_reconciliation_or_explicit_governance_acceptance",
  "compaction_visibility_policy": "show_compaction_seams_and_bridge_linked_continuity_explicitly_no_silent_flattening_of_pre_post_compaction_state",
  "scope_granularity_enum": [
    "repo_wide",
    "subtree",
    "module_set",
    "file_set",
    "artifact_surface_only"
  ],
  "worker_visibility_mode_default": "read_only_observability",
  "worker_visibility_label_set": [
    "raw_transcript",
    "worker_self_report",
    "reconciled_handoff",
    "orchestrator_judgment"
  ],
  "support_worker_surface_policy": "support_workers_emit_advisory_or_scratch_surfaces_only_by_default_unless_explicitly_re_roled",
  "topology_map_authority_policy": "derived_from_canonical_execution_state_only",
  "topology_map_epistemic_markers_required": [
    "state_origin",
    "reconciliation_status",
    "last_updated_at",
    "last_reconciled_at"
  ],
  "handoff_trust_model": "self_report_non_authoritative_until_reconciled",
  "write_lease_transfer_policy": "explicit_main_orchestrator_only",
  "closeout_hardening_bundle_status": "separate_operational_proposal_only"
}
```

## Path V35-A: Orchestrator-State and Jurisdiction Baseline

Lock class: `L1`

Goal:

- make the multi-role constitution real as explicit orchestration state rather than draft
  prose only.

Scope:

- define canonical execution-state artifacts for:
  - execution topology,
  - active roles,
  - write lease,
  - role transitions,
  - worker handoff envelopes,
  - runtime/session identity;
- freeze canonical orchestration identity fields sufficient to reconnect observable worker
  state to accepted execution state:
  - `orchestrator_session_id`,
  - `worker_session_id`,
  - `parent_session_id`,
  - `event_cursor`,
  - `last_reconciled_event`,
  - `continuation_bridge_ref`;
- freeze scope granularity kinds for lease/state reporting:
  - `repo_wide`,
  - `subtree`,
  - `module_set`,
  - `file_set`,
  - `artifact_surface_only`;
- enforce the single-writer default in orchestration state;
- make `main_orchestrator` the sole user-facing command surface by default;
- keep all worker state subordinate to orchestrator-issued scope and lease;
- require canonical state to retain compaction lineage explicitly rather than flattening
  pre-compaction and post-compaction execution history into one undifferentiated thread.

Locks:

- no multi-writer release in this path;
- no worker self-upgrade into governance or write authority;
- no acceptance or closeout authority outside `main_orchestrator`;
- execution-state artifacts must be canonical and deterministic;
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

Acceptance:

- canonical orchestration state exists and is sufficient to reconstruct:
  - current roles,
  - current builder lease holder,
  - current scopes,
  - scope granularity kind,
  - current worker statuses,
  - current transition history,
  - current session/event lineage,
  - current reconciliation cursor and continuation-bridge linkage,
  - explicit compaction seams and bridge-linked continuity across recovered sessions.

## Path V35-B: Single-Builder Delegation and Reconciled Worker Handoffs

Lock class: `L1`

Goal:

- make the main orchestrator actually drive one builder plus support workers under the
  constitutional constraints.

Scope:

- support builder-task delegation from the orchestrator into an implementation repo;
- support bounded `explorer`, `validator`, and `docs_helper` workers;
- leverage existing `urm_runtime` primitives for:
  - child dispatch,
  - child workflow,
  - recovery,
  - budgeting,
  - capability policy,
  - event capture;
- require typed handoff envelopes and explicit orchestrator reconciliation before any
  support-worker claim is treated as evidence;
- require all delegated scopes to declare canonical scope kind:
  - `repo_wide`,
  - `subtree`,
  - `module_set`,
  - `file_set`,
  - `artifact_surface_only`;
- keep write authority leased to one builder by default.

Locks:

- only one authoritative implementation write lease may be active by default;
- support workers remain non-authoritative by default and may emit advisory or scratch
  surfaces only unless explicitly re-roled;
- worker outputs remain advisory until reconciled;
- lease scope must be recorded with explicit scope kind rather than free-form scope text
  only;
- no worker may directly talk to the user as an authoritative surface in this path;
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

Acceptance:

- the orchestrator can run one end-to-end delegated implementation loop with:
  - one builder,
  - at least one support worker,
  - typed handoff envelopes,
  - explicit reconciliation,
  - no authority drift.

## Path V35-C: Worker Transcript and Progress Visibility

Lock class: `L0`

Goal:

- let the user inspect worker progress and conversation state without turning workers into
  independent authority surfaces.

Scope:

- expose worker transcript visibility as read-only observability;
- expose worker status, last action, blocking state, and current scope;
- preserve orchestrator-centric interaction as the primary UX;
- make transcript visibility derived from canonical execution-state artifacts or runtime
  events, not from ad hoc summaries;
- prefer existing event/runtime surfaces in `packages/urm_runtime` as the source for
  transcript/progress state before inventing parallel visibility channels;
- treat runtime events as source surfaces only; event presence by itself does not establish
  accepted truth without canonical reconciliation or explicit governance acceptance;
- label visible worker surfaces explicitly by epistemic lane:
  - `raw_transcript`,
  - `worker_self_report`,
  - `reconciled_handoff`,
  - `orchestrator_judgment`;
- if visible epistemic layers diverge, render explicit typed divergence state rather than
  silently showing inconsistent panes:
  - `parsing_failure`
  - `reconciliation_aborted`

Locks:

- transcript visibility is observational only;
- no direct user-to-worker authority channel is released in this path;
- no worker transcript text becomes authoritative by visibility alone;
- transcript/progress surfaces must show their epistemic label explicitly and may not
  visually collapse `raw_transcript`, `worker_self_report`, `reconciled_handoff`, and
  `orchestrator_judgment` into one undifferentiated authority surface;
- if `raw_transcript` exists without a valid downstream `worker_self_report` or
  `reconciled_handoff`, the UX must render that divergence explicitly rather than imply
  successful parsing or reconciliation;
- transcript/progress surfaces must represent compaction seams and continuation-bridge
  continuity explicitly rather than silently flattening pre/post-compaction state into one
  uninterrupted conversation;
- redaction, privacy, and scope boundaries must remain deterministic if surfaced;
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

Acceptance:

- a user can inspect worker transcript/progress surfaces while the orchestrator remains the
  sole authoritative interaction boundary.

## Path V35-D: Dynamic Agent Duty Map and Topology UX

Lock class: `L0`

Goal:

- provide a high-level dynamic map of current execution topology, duties, leases, and
  dependencies.

Scope:

- render a topology view showing:
  - orchestrator,
  - builder,
  - support workers,
  - scopes and current duties,
  - current write-lease holder,
  - dependency or blocker edges,
  - blocking vs non-blocking status,
  - explicit epistemic/provenance markers per node or edge:
    - `state_origin`,
    - `reconciliation_status`,
    - `last_updated_at`,
    - `last_reconciled_at`;
- support provenance-linked inspection from topology state into the underlying canonical
  handoff and event surfaces that justify the rendered node or edge state;
- derive the map from canonical execution-state artifacts only;
- keep it non-authoritative as a visualization layer over authoritative state.

Locks:

- topology/duty map may not invent state not present in canonical execution artifacts;
- no topology UI element may silently redefine authority or lease ownership;
- map nodes and edges are explanatory surfaces, not governance authority by themselves;
- topology markers must distinguish at least:
  - self-reported state,
  - reconciled state,
  - derived state;
- topology surfaces must represent compaction boundaries and bridge-linked continuity
  explicitly where current node or edge state spans recovered sessions;
- visual encoding must distinguish authority from urgency:
  - support-role blocking state remains advisory unless elevated by `main_orchestrator`;
  - advisory blockers must not be rendered as governance-equivalent blockers;
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

Acceptance:

- the user can inspect one dynamic view that accurately reflects current roles, duties,
  leases, blocker/dependency structure, and epistemic freshness/provenance from canonical
  state.

## Path V35-E: Runtime Enforcement and Promotion Hardening

Lock class: `L1`

Goal:

- move the multi-role constitution from draft governance into bounded runtime enforcement
  where safe.

Scope:

- enforce handoff-envelope validation at orchestration boundaries;
- enforce write-lease state recording and explicit role-transition recording;
- enforce scope-kind recording and reject missing or malformed canonical scope granularity;
- reject obvious authority-drift cases at runtime:
  - missing handoff fields,
  - concurrent builders in default topology,
  - support-role self-upgrade,
  - support-role proxy authority through artifact execution if it would violate lease
    policy;
- keep acceptance and closeout authority in ADEU.

Locks:

- runtime enforcement must implement the current constitutional surface only and may not
  widen role authority;
- no automatic acceptance or closeout;
- no implicit multi-writer release;
- enforcement placement should prefer `packages/urm_runtime` or an explicit new
  orchestration package, not unbounded further accretion into large
  `adeu_agent_harness` pipeline files;
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

Acceptance:

- the most important fail-closed conditions from the draft lock become enforced runtime
  invariants without reducing auditability.

## Separate Operational Track (Non-V35)

The closeout hardening bundle remains separately named and intentionally orthogonal:

- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`

It should not be treated as implicit `V35` scope unless later formalized under its own lock
bundle. The current recommendation remains:

1. `O1` closeout orchestration extraction
2. `O2` closeout artifact index + lint
3. `O3` advisory adjudication scaffold

## Recommended Default Order

1. `V35-A`
   - make orchestration state canonical first.
2. `V35-B`
   - make one-builder delegation real under that state model.
3. `V35-C`
   - expose worker visibility once worker state is canonical.
4. `V35-D`
   - add the dynamic map once the topology/state model exists.
5. `V35-E`
   - promote bounded enforcement last, once the observable model is stable.

## Non-Goals (Current Family)

This planning draft does not recommend:

- multi-writer implementation by default;
- worker-owned governance authority;
- direct user chat with workers as co-equal authority surfaces;
- live provider expansion or remote transport as part of execution UX;
- replacement of ADEU closeout judgment with runtime summaries;
- treating transcript visibility or topology UI as a substitute for accepted artifacts.

## Recommendation

- select `V35-A` as the next default candidate after `V34` closure;
- keep the family narrow and constitutional at first:
  make role state and handoff state explicit before building richer UX on top;
- preserve the design rule established by the multi-role bundle:
  the orchestrator owns governance, the builder holds the current scoped write lease, and
  support workers remain observable but non-authoritative unless explicitly re-roled.
