# Draft ADEU Resident-Agent Continuation And Residual-Intent V60 Implementation Mapping v0

Status: support-layer implementation mapping for `V60` after `V60-B` closed on
`main` and while `V60-C` is the next starter candidate.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the `V60` family into a
repo-native implementation shape so bounded task-law compilation and continuation
identity can land over the already shipped `V56` / `V57` / `V58` / `V59` governed
stack without letting transcript, continuity state, or communication surfaces become
ambient authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v43.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V59_v0.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_V60C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`
- `docs/DRAFT_WCPGC_CORE_AND_STRICT_V0_v0.md`

## Carry Forward Nearly As-Is

- the shipped `V56-A`, `V56-B`, and `V56-C` packet / proposal / checkpoint / ticket /
  conformance / harvest surfaces
- the shipped `V57-A`, `V57-B`, and `V57-C` observation / restoration / hardening
  surfaces
- the shipped `V58-A`, `V58-B`, and `V58-C` live admission / handoff /
  reintegration / advisory surfaces
- the shipped `V59-A`, `V59-B`, and `V59-C` continuity / restoration / advisory
  surfaces
- the rule that `agentic_de_*` naming remains the lineage carrier while `V60` is the
  continuation / residual-intent family role
- the rule that hidden cognition is not the governance surface
- the rule that `V56` ticket duration remains `single_step_local`
- the rule that transcript and event stream are observability surfaces, not native
  task law or continuation identity
- the rule that prior continuity state is context at most, never standing authority

## Re-Author With Repo Alignment

- primary family package:
  - `packages/adeu_agentic_de`
- live harness/runtime package:
  - `packages/urm_runtime`
- likely API/backend surfaces:
  - `apps/api/src/adeu_api/`
  - `apps/api/scripts/`
- tests:
  - `packages/adeu_agentic_de/tests/`
  - `packages/urm_runtime/tests/`
  - `apps/api/tests/`
- likely family module split:
  - `continuation_kernel.py`
  - `continuation_decision.py`
- likely family artifact output roots:
  - `artifacts/agent_harness/v164/`
  - `artifacts/agent_harness/v165/`

The family should remain backend-first in `V60-A`:

- no product API/UI authority widening
- no governed communication packet law yet
- no connector or remote operator widening
- no repo-bound writable-surface widening
- no dispatch widening
- no execute widening

## Path Ladder Mapping

- `V60-A`
  - instantiate one typed starter seed-intent record
  - instantiate one task charter packet
  - instantiate one task residual packet
  - instantiate one loop-state ledger
  - instantiate one continuation decision record
  - bind those outputs to one already shipped exact continuity-bound exemplar path
  - keep starter ingress non-chat-native:
    - typed starter artifact only
    - not raw transcript semantics
    - not generic chat memory
    - not connector traffic
  - keep task charter compilation typed and replayable:
    - same selected seed intent
    - same frozen policy
    - same task charter
  - keep task charter compiled rather than echoed:
    - compiled bounded task law
    - not raw user request echo
  - keep `TaskResidual` derived and replayable:
    - same selected derivation basis
    - same frozen policy
    - same residual posture
  - keep continuation decision explicit and replayable:
    - same selected evidence basis
    - same frozen policy
    - same continuation posture
  - keep transcript, prior continuity success, and prior reintegration non-sovereign:
    - context-bearing at most
    - not standing authority
    - not native task law by default
  - keep the selected downstream path exact:
    - `local_write`
    - `create_new`
    - declared continuity root `artifacts/agentic_de/v59/workspace_continuity/`
    - target centered on `runtime/reference_patch_candidate.diff`
  - keep continuation-to-act descent exact:
    - if `continue_to_governed_act`
    - then selected next path equals that exact downstream path only
  - keep every externally effective act fresh-step governed:
    - no stretched `V56` ticket duration
    - no standing act authority
  - keep `emit_governed_communication` posture-only:
    - packet law deferred to `V61`
  - keep raw communication ingress, office binding, connector admission, remote
    operator surfaces, repo-bound writable authority, replay widening, execute
    widening, and dispatch widening not selected in this slice
- `V60-B`
  - add one bounded residual refresh / reproposal / escalation seam after one latest
    reintegrated governed act
  - reuse the shipped `V60-A` starter surfaces by default
  - instantiate:
    - `agentic_de_task_residual_refresh_packet@1`
    - `agentic_de_continuation_refresh_decision_record@1`
  - preserve the shipped `V60-A` loop-state ledger as the canonical stable loop
    identity anchor in this slice:
    - `V60-B` refresh artifacts advance frontier over that same loop identity
    - no loop-state refresh or replacement artifact is selected here
  - keep refresh dependent on explicit prior continuation lineage plus one latest
    reintegrated act lineage selected by explicit latest-act identity and
    fail-closed selection basis
  - keep refresh extensional and replayable:
    - same shipped loop identity
    - same latest reintegrated act identity
    - same frozen policy basis
    - same refreshed residual and same refreshed continuation posture
  - keep structured block / rejection / reproposal handling typed and replayable
  - keep `reproposal_required` posture-only and non-chat-native:
    - it records that the current charter / residual frontier may not lawfully
      continue as-is
    - it requires later structured ingress or governed communication to proceed
    - it is not implicit charter amendment
    - it is not new starter seed-ingress law
  - keep ticket duration single-step and fresh-step only
  - keep communication packet law still deferred to `V61`
- `V60-C`
  - add one advisory continuation hardening / migration surface over the same
    continuation lineage
  - keep outputs advisory-only and non-entitling
  - keep evidence basis distinct from recommendation
  - keep register provenance and lineage-root dedup explicit:
    - `field_origin_tags`
    - `field_dependence_tags`
    - `root_origin_dedup_summary`
  - keep the selected exemplar non-generalizing by default:
    - not class-level continuation law
    - not family-level migration law
    - not communication law
    - not broader autonomy claims
  - keep any later widening or migration decision separate from live behavior by
    default

## Pre-Lane Drift Check Rule

Because all lane bundles are drafted before first implementation, each later lane should
start with one short drift check against the previous lane's actual landing.

That drift check should emit one bounded handoff artifact:

- `agentic_de_lane_drift_record@1`

Each controlling assumption should be classified at least as:

- `holds`
- `amended`
- `superseded`
- `not_selected_anymore`

## Interface Ordering Rule

- `V55` remains the constitutional coherence checker over family surfaces
- `V56` remains the resident proposal / checkpoint / ticket family
- `V57` remains the bounded observed / restored local-effect evidence family
- `V58` remains the live harness admission / handoff / reintegration family
- `V59` remains the persistent continuity family over the selected path
- `V60` owns only bounded task-law compilation and continuation identity over that
  already governed stack
- `V61` should later own governed communication packet and office law that consume
  `V60` outputs
- `V48` remains the owner of delegated worker execution after lawful dispatch

## Do Not Import

- raw transcript semantics as starter task law
- generic chat memory as loop-state identity
- connector traffic as starter continuation ingress
- `TaskResidual` as standing permission
- prior continuity success as act authority
- prior ticket or prior reintegration as standing authority
- communication packet law or office binding in `V60-A`
- ticket-duration widening by continuity or continuation implication alone
- any assumption that later `V60` lanes are authorized merely because they are drafted
