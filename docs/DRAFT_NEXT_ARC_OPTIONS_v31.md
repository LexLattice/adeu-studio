# Draft Next Arc Options v31

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`, updated after the
bounded ANM / `D@1` family closed on `main` and the remaining policy-to-taskpack /
worker-enforcement bridge was identified as a separate infra gap rather than another
implicit `V47` widening.

This draft does not automatically supersede the contest-participation planning branch in
`docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`, the structural-reasoning assessment planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`, the repo self-description planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`, the applied benchmarking planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`, or the authoritative normative
markdown planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`.

Instead, it records a sixth connected candidate family:

how should ADEU Studio bind released policy and released repo/task scope into
externally enforced worker-execution envelopes so delegated Codex work is constrained by
typed taskpack/harness artifacts rather than softly by prompt prose, chat memory, or
`AGENTS.md` alone?

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

Interpretive doctrine for this planning surface:

- horizon-sensitive terms such as `bounded`, `complete`, `closed`, `deferred`, and
  `forbidden` should be read using
  `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`;
- planning-boundary lines below are scope guards and absence-of-authorization
  statements for this planning draft, not lock-equivalent permanent prohibitions by
  themselves;
- planning-vs-lock authority transfer should be read using
  `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`;
- future seam selection and widening posture should be read using
  `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `V41-A` through `V41-F` are closed on `main`.
- `V42-A` through `V42-G4` are closed on `main`.
- `V45-A` through `V45-F` are closed on `main` and now constitute the completed bounded
  repo self-description ladder recorded in `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`.
- `V47-A` through `V47-F` are closed on `main` and now constitute the completed ANM /
  `D@1` policy-source, IR, facts, results, ledger, coexistence, ownership-transition,
  and consumer ladder recorded in `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`.
- `vNext+111` is the current baseline implementation state on `main`.
- released agent-harness kernel surfaces already exist on `main`, including:
  - deterministic taskpack compilation in `packages/adeu_agent_harness`;
  - deterministic taskpack runner enforcement in `packages/adeu_agent_harness`;
  - deterministic signing / verification / provenance surfaces in
    `packages/adeu_agent_harness`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v26.md` records one connected candidate family:
  - `V43`
  - ADEU external governed contest participation substrate
- `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md` records one connected candidate family:
  - `V44`
  - ADEU structural reasoning assessment substrate
- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md` records one connected candidate family:
  - `V45`
  - ADEU repo self-description substrate
- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md` records one connected candidate family:
  - `V46`
  - ADEU applied benchmarking substrate
- `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md` records one connected candidate family:
  - `V47`
  - ADEU authoritative normative markdown and bounded `D@1` compilation substrate
- older harness planning history already exists and remains useful shaping context:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
  - taskpack compiler / runner / verification baseline over `packages/adeu_agent_harness`

## Gap

The repo no longer lacks:

- typed repo self-description over the released `V45` ladder;
- typed ANM policy-source, IR, fact, result, ledger, and consumer doctrine over the
  released `V47` ladder;
- a generic deterministic harness kernel with taskpack compile/run/verify surfaces.

The missing layer sits between those released families.

Today the repo still lacks a released way to:

- bind released `V45` scope objects and released `V47` policy objects into one typed
  worker-execution boundary;
- derive taskpack allowlist / forbidden / command / evidence posture from released
  policy and released scope lineage rather than local convention;
- prove that a delegated worker run was governed by one explicit compiled boundary
  rather than by prompt phrasing or ambient repo instructions alone;
- distinguish:
  - released policy source;
  - released scope source;
  - derived taskpack boundary;
  - worker-run provenance;
  - post-run conformance judgment;
- keep prompts, `AGENTS.md`, and chat prose as projection/context rather than execution
  authority when a typed boundary already exists.

The missing layer is therefore not more normative-source work and not a generic
harness-kernel release.

The missing layer is a policy-to-taskpack / worker-enforcement bridge.

## Relationship To `V43`, `V44`, `V45`, `V46`, And `V47`

`V43`, `V44`, `V45`, `V46`, `V47`, and this new candidate family are connected but
non-identical.

`V45` asks:

- what does the ADEU repo currently contain, and how are those surfaces typed and
  governed as a descriptive artifact system?

`V47` asks:

- how should ADEU encode authoritative obligations inside markdown, compile them into
  bounded normalized semantics, and bind later consumers without laundering authority
  out of facts, results, or ledgers?

Historical harness work asks:

- how should ADEU compile deterministic taskpacks and run them through a fail-closed
  harness kernel?

This new family asks:

- how should released policy and released scope become the typed authority inputs to
  taskpack and worker execution?
- how should worker-bound prompts and commands remain derived projections of typed
  boundaries rather than the source of truth themselves?
- how should worker-run provenance and conformance remain explicit so the repo can tell
  whether a delegated Codex run actually stayed inside the compiled boundary?

`V45-F` already released the descriptive-to-normative binding seam:

- what released descriptive inputs may constrain later normative consumers;
- what authority posture those descriptive inputs hold;
- what those descriptive inputs may not approve or execute by themselves.

`V48` does not reopen that binding seam.

`V48` instead asks:

- how already admitted released descriptive and normative inputs become one typed
  worker-execution envelope;
- how that envelope is compiled into taskpack/runnable boundary carriers;
- how worker-run provenance and later conformance remain bound to that compiled
  execution-envelope lineage.

So this family may constrain:

- delegated Codex work over the ADEU repo;
- how later orchestration experiments externalize worker constraints;
- how worker-run provenance is judged against released policy and scope;
- how prompts, `AGENTS.md`, and local repo text are demoted from authority to
  projection/context when a typed worker boundary exists.

But it may not mint:

- new ANM policy-source semantics;
- new repo self-description semantics;
- execution authority beyond what the bound released policy already allows;
- automatic waiver, deferral, or supersession authority;
- multi-worker orchestration entitlement by default;
- benchmark, contest, or structural-assessment doctrine.

Planning relationship:

- `V43` remains a valid connected candidate family from `v26`;
- `V44` remains a valid connected candidate family from `v27`;
- `V45` remains a valid connected candidate family from `v28`, but its bounded ladder is
  already closed on `main`;
- `V46` remains a valid connected candidate family from `v29`;
- `V47` remains a valid connected candidate family from `v30`, but its bounded ladder is
  already closed on `main`;
- this draft introduces a sixth connected candidate family rather than replacing any of
  them;
- this family should not be read as `V47-G`;
- this family should instead be read as the bridge from released descriptive and
  normative artifacts into actual constrained delegated worker execution.

## Recommended Family

- Family name: `V48`
- Family theme: ADEU policy-to-taskpack and worker-enforcement bridge
- Released earlier shaping inputs:
  - `V45-A` through `V45-F`
  - `V47-A` through `V47-F`
  - released `adeu_agent_harness` taskpack compile / runner / verification surfaces
- Connected candidate families not reopened or superseded here:
  - `V43`
  - `V44`
  - `V45`
  - `V46`
  - `V47`
- Recommended architecture reference:
  - `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- Recommended first reference set for this branch:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
  - `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`
- Recommended next path for this branch:
  - `V48-A`
- Recommended next concrete arc for this branch if selected:
  - `vNext+112`
- Default path selection for this branch:
  - select `V48-A` as the next default candidate
  - treat that default as the policy/scope-to-taskpack binding lane prior to any
    worker-run orchestration widening

This family/path recommendation is branch-local to the `v31` planning surface.

It is not, by itself, a repo-wide next-family resolution while the connected `V43`,
`V44`, `V45`, `V46`, and `V47` branches remain in parallel planning scope.

## Closed Earlier Families And Surfaces

`V45` should now be read as a released descriptive substrate:

- explicit repo entities, schema families, symbol/dependency graphs, arc dependency,
  test intent, optimization posture, and descriptive-to-normative binding.

`V47` should now be read as a released normative substrate:

- ANM source, `D@1`, normalized `D-IR`, predicate contracts, checker facts,
  evaluation results, obligation ledger, coexistence/adoption doctrine,
  selector/predicate ownership-transition doctrine, and bounded consumer doctrine.

Released harness surfaces should now be read as a generic execution substrate:

- deterministic taskpack compiler;
- deterministic taskpack runner;
- deterministic signing / verification / provenance surfaces.

None of those released surfaces, by themselves, yet solve:

- how released policy rows and released repo scope become one typed taskpack boundary;
- how a worker run proves which released policy and scope artifacts governed it;
- how to reject runs that are taskpack-valid in the generic sense but not actually
  derived from the intended released policy/scope lineage.

`V48` is the planning move that fills that bridge without reopening released
descriptive, normative, or harness-kernel baselines.

## Recommended Next Family (`V48`)

`V48` should release a bounded enactment bridge around:

- task-scoped policy binding profiles;
- repo-scope binding profiles;
- deterministic taskpack derivation from released policy + scope;
- worker execution attestation / provenance that names the compiled boundary;
- task/run-scoped boundary instances that name one concrete compiled boundary for one
  worker-run context;
- deterministic conformance reporting over observed worker actions versus the compiled
  boundary;
- explicit projection-only posture for prompts and repo prose when a typed worker
  boundary exists.

The family should treat released policy as:

- upstream authority input;
- not something the worker run is allowed to reinterpret.

The family should treat released repo self-description as:

- upstream scope/input authority;
- not something the worker run is allowed to widen by ambient repo discovery alone.

The family should treat taskpack and runner surfaces as:

- execution-envelope carriers derived from upstream authority;
- not independent policy sources.

The family should treat later multi-worker orchestration as:

- downstream consumers of the bridge;
- not the first release inside this family.

At minimum, later `V48` work should make explicit:

- how a released `V47` policy row or profile maps into:
  - taskpack allowlist posture;
  - forbidden-effect posture;
  - command posture;
  - evidence-slot posture;
- how a released `V45` scope surface maps into worker-reachable file or artifact scope;
- how the compiled taskpack proves its source lineage back to released policy and scope;
- how worker-run provenance proves that the run consumed the intended compiled boundary;
- how conformance judgment rejects:
  - off-boundary edits;
  - prompt-only authority claims;
  - missing lineage;
  - stale boundary reuse.
- what observed-action carriers are admissible before conformance becomes
  implementation-facing, including:
  - filesystem mutation set;
  - command invocation log;
  - emitted artifact set;
  - branch/ref identity.

## Suggested `V48` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V48-A` | policy/scope to taskpack binding profile | candidate `anm_taskpack_binding_profile@1` over released `V47` policy lineage and released `V45` scope lineage | planned |
| `V48-B` | deterministic policy-to-taskpack compiler lane | candidate `compiled_policy_taskpack_binding@1` plus deterministic taskpack derivation from the released binding profile | planned |
| `V48-C` | worker execution envelope + attestation lane | candidate `task_run_boundary_instance@1`, candidate `worker_execution_attestation@1`, and candidate `worker_execution_provenance@1` | planned |
| `V48-D` | post-run conformance / replay lane | candidate `worker_boundary_conformance_report@1` plus replayable diagnostics over frozen observed-action carriers | planned |
| `V48-E` | delegated multi-worker topology seam | candidate `worker_delegation_topology@1` and bounded supervisor/worker handoff doctrine | planned_later_not_selected_here |

These output names are planning-level candidate names, not lock-level schema authority.

`V48-A` through `V48-D` should be read together as the staged realization of the
policy-to-enforcement bridge's first safe family shape.

That is:

- `V48-A` intentionally narrows the first move to explicit binding doctrine;
- `V48-B` then compiles that doctrine into deterministic taskpack surfaces;
- `V48-C` then makes actual worker-run boundary lineage explicit;
- `V48-D` then makes replayable conformance judgment explicit over those runs.

So the `A -> B -> C -> D` staging is an intentional lower-risk subdivision, not a
deviation from the bridge-first doctrine.

## Recommended Next Path (`V48-A`)

Implement the bounded policy/scope-to-taskpack binding lane first.

`V48-A` should introduce:

- one canonical bounded binding-profile artifact candidate:
  - explicit released policy source lineage;
  - explicit released repo-scope lineage;
  - explicit taskpack-surface mapping posture for:
    - allowlist;
    - forbidden effects;
    - commands;
    - evidence slots;
  - explicit projection-only posture for prompt text and repo prose;
  - explicit prompt-boundary conflict posture where the compiled boundary wins and
    conflicting prose is a verifier/compiler error rather than added authority;
  - explicit stale-lineage and unresolved-lineage fail-closed posture;
  - explicit unsupported policy-to-taskpack mapping fail-closed posture;
- one small initial binding set rich enough to cover:
  - exactly one bounded repo-internal task over one released `V45` scope-bearing
    surface;
  - exactly one released `V47` policy-bearing surface;
  - exactly one worker;
  - exactly one resulting boundary instance lineage with no ambiguity about authority
    order;
- no policy-composition algebra, policy conflict-resolution algebra, scope union, or
  scope widening semantics are selected in `V48-A`;
- deterministic local fixtures for one or more initial repo-internal worker tasks;
- no widening yet into multi-worker orchestration, automatic decomposition, or
  execution entitlement expansion.

`V48-A` is binding-first and non-orchestrational:

- it may emit binding profiles and bounded diagnostics;
- it may not yet emit multi-worker topology, automatic planner decomposition, or
  broader execution powers.

## Why This Path

- It is the narrowest safe consumer of the new bridge gap.
- It makes the policy-to-execution authority chain explicit before worker orchestration
  and runtime behavior widen.
- It prevents the family from collapsing immediately into “Codex orchestration” without
  first making the authority inputs typed and inspectable.
- It creates the raw binding layer needed before deterministic taskpack derivation,
  run attestation, and conformance reporting.
- It lets ADEU test whether its released descriptive and normative artifacts can
  actually govern worker behavior externally rather than only describe desired
  behavior in prose.

## First-Slice Boundary (`V48-A`)

`V48-A` should stay bounded to:

- released `V45` scope inputs only;
- released `V47` policy inputs only;
- one canonical binding profile only;
- one released policy source only;
- one released scope source only;
- one worker only;
- one boundary instance only;
- deterministic mapping into taskpack surface categories only;
- small local fixtures only;
- explicit fail-closed lineage and resolution posture only.

It should not attempt:

- policy conflict resolution;
- policy aggregation or policy composition;
- scope union or scope widening;
- multi-worker orchestration;
- automatic task decomposition;
- runtime execution entitlement beyond released policy;
- waiver or deferral issuance;
- free-form prompt synthesis as authority;
- repo-wide taskpack generation for arbitrary tasks;
- contest, benchmark, or structural-assessment family widening;
- reopening generic harness-kernel semantics already shipped on `main`.

## Follow-On Paths Inside `V48`

### `V48-B`

Deterministic policy-to-taskpack compiler lane:

- compile the released binding profile into actual taskpack surfaces;
- prove taskpack lineage back to released policy and released scope;
- emit one compiled boundary identity hash over policy lineage, scope lineage,
  compiler/runtime selection, and declared task identity;
- keep generic taskpack semantics closed while adding bridge-specific compilation.

### `V48-C`

Worker execution envelope + attestation lane:

- make explicit which compiled boundary governed one worker run;
- emit one task/run-scoped boundary instance keyed to:
  - policy lineage hash;
  - scope lineage hash;
  - compiled boundary identity hash;
  - compiler version;
  - repo ref;
  - task instance identity;
- record worker/provider/model/adapter provenance against the bound taskpack lineage;
- keep prompts projection-only and non-authoritative.

### `V48-D`

Post-run conformance / replay lane:

- freeze the first admissible observed-action carriers before release-level conformance
  judgment widens, including:
  - filesystem mutation set;
  - command invocation log;
  - emitted artifact set;
  - branch/ref identity;
- verify whether observed worker behavior stayed inside the compiled boundary;
- emit replayable conformance reports and fail-closed diagnostics;
- prevent “taskpack existed” from being treated as proof that the worker actually
  followed it.

### `V48-E`

Delegated multi-worker topology seam:

- later family work may widen from one worker boundary into supervisor/worker or
  worker/worker handoff doctrine;
- that seam is explicitly later and not selected in the first family move.

## Candidate Package Ownership

Package ownership should remain planning-bound for now.

The first planning pass should therefore assume:

- `packages/adeu_agent_harness` is the likely first owning package for the bridge;
- released `packages/adeu_repo_description` outputs are consumed as scope inputs, not
  reopened as first-owner surfaces;
- released `packages/adeu_semantic_source` and `packages/adeu_commitments_ir` outputs
  are consumed as policy inputs, not reopened as first-owner surfaces.

This should be read as intentional restraint, not missing planning detail.

The family surface is stable enough to plan without freezing cross-package placement
prematurely.

That likely first implementation placement should not, by itself, be read as permanent
schema-identity ownership for every later `V48` surface.

## Governing References

The higher-order concept notes for this family direction are:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`

Connected but non-authorizing context docs are:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`

Released earlier shaping surfaces that `V48` should learn from rather than reopen are:

- released `V45-A` through `V45-F`
- released `V47-A` through `V47-F`
- released `adeu_agent_harness` taskpack compile / run / signing surfaces on `main`

Concrete released substrate anchors for this family direction are:

- `apps/api/fixtures/repo_description/vnext_plus105/repo_descriptive_normative_binding_frame_v105_reference.json`
  as one released `V45-F` descriptive-to-normative binding artifact;
- `artifacts/agent_harness/v54/runner_result.json`
  as one released `taskpack_runner_result@1` lineage/provenance carrier;
- `artifacts/agent_harness/v55/evidence_inputs/v34a_handoff_completion_evidence_v55.json`
  as one released harness evidence artifact tying verifier, runner, and packaging
  surfaces to a shared downstream binding posture.

## Planning Boundary

- no reopening of released `V45` or released `V47` contracts is authorized by this
  planning draft;
- no reopening of generic taskpack compiler or generic harness runner semantics is
  authorized by this planning draft except where the bridge requires explicit typed
  lineage binding;
- no automatic supersession of the `V43`, `V44`, `V45`, `V46`, or `V47` planning
  branches is authorized by this planning draft;
- no prompt prose, chat prose, or `AGENTS.md` text is authorized as a substitute for
  typed worker-bound authority when a released binding profile exists;
- if prompt prose, chat prose, or `AGENTS.md` text conflicts with a compiled boundary,
  the compiled boundary must win and the conflict must be treated as a verifier error
  rather than extra authority;
- no waiver, deferral, mutation, scheduling, recursive execution, or approval
  authority is authorized by this planning draft;
- no multi-worker topology is selected by this planning draft;
- no repo-wide orchestration regime is selected by this planning draft.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v30.md",
  "baseline_arc": "vNext+111",
  "closed_prior_families": [
    "V41",
    "V42",
    "V45",
    "V47"
  ],
  "connected_candidate_families_in_scope": [
    "V43",
    "V44",
    "V45",
    "V46",
    "V47",
    "V48"
  ],
  "branch_candidate_family": "V48",
  "branch_candidate_status": "selected_for_v31_planning_surface_not_repo_wide_family_selection",
  "connected_families_not_reopened_here": [
    "V43",
    "V44",
    "V45",
    "V46",
    "V47"
  ],
  "closed_current_family_paths": [],
  "planned_current_family_paths": [
    "V48-A",
    "V48-B",
    "V48-C",
    "V48-D",
    "V48-E"
  ],
  "default_next_arc_candidate_for_this_branch": "V48-A",
  "default_next_concrete_arc_candidate_for_this_branch": "vNext+112",
  "family_architecture_doc": "docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md",
  "pre_lock_companion_docs_expected": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v30.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v7.md"
  ],
  "planned_family_packages": [
    "packages/adeu_agent_harness"
  ],
  "first_slice_active_packages": [
    "packages/adeu_agent_harness"
  ],
  "package_selection_status": "likely_first_owner_selected_in_planning_not_locked_yet",
  "family_theme": "adeu_policy_to_taskpack_and_worker_enforcement_bridge",
  "branch_local_planning_selection_only": true,
  "released_repo_scope_family_consumed": "V45",
  "released_policy_source_family_consumed": "V47",
  "released_harness_kernel_required": true,
  "released_taskpack_compiler_required": true,
  "released_taskpack_runner_required": true,
  "released_signing_and_provenance_surfaces_required": true,
  "prompt_projection_only_required": true,
  "prompt_boundary_conflict_fails_closed": true,
  "soft_prompt_or_agents_authority_insufficient_for_worker_governance": true,
  "policy_scope_to_taskpack_binding_required": true,
  "single_policy_source_initially_required": true,
  "single_scope_source_initially_required": true,
  "single_worker_initially_required": true,
  "single_boundary_instance_initially_required": true,
  "policy_conflict_resolution_not_selected_in_v48a": true,
  "scope_union_or_widening_not_selected_in_v48a": true,
  "unsupported_policy_to_taskpack_mapping_fails_closed": true,
  "compiled_boundary_identity_hash_required_by_v48b": true,
  "task_run_boundary_instance_identity_required_by_v48c": true,
  "observed_action_carriers_frozen_before_v48d": true,
  "worker_run_lineage_to_compiled_boundary_required": true,
  "post_run_boundary_conformance_required": true,
  "multi_worker_topology_initially_deferred": true,
  "planning_boundary_mode": "scope_guard_not_lock_authority",
  "authority_layering_note": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
  "horizon_glossary_note": "docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md",
  "future_seam_promotion_rules_note": "docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md"
}
```
