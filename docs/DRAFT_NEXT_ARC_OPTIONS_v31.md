# Draft Next Arc Options v31

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`, updated after the
bounded ANM / `D@1` family closed on `main`, the remaining policy-to-taskpack /
worker-enforcement bridge was identified as a separate infra gap rather than another
implicit `V47` widening, and `vNext+112` (`V48-A`) through `vNext+116` (`V48-E`)
closed on `main`, completing the bounded `V48` family with no further internal
`V48` path currently selected.

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
- `V48-A` is closed on `main` and now constitutes the released bounded binding-profile
  starter slice for this family.
- `V48-B` is closed on `main` and now constitutes the released bounded deterministic
  compiler slice for this family.
- `V48-C` is closed on `main` and now constitutes the released bounded worker-run
  envelope + attestation / provenance slice for this family.
- `V48-D` is closed on `main` and now constitutes the released bounded replayable
  single-worker conformance slice for this family.
- `V48-E` is closed on `main` and now constitutes the released bounded delegated
  topology slice for this family.
- `vNext+116` is the current baseline implementation state on `main`.
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
- one canonical typed `V48-A` binding profile that binds released scope and released
  policy into one worker-bound execution boundary;
- one canonical typed `V48-B` compiler bridge that lowers the released binding profile
  into deterministic released-kernel taskpack carriers;
- one canonical typed `V48-C` worker envelope that binds one released compiled
  boundary to one task/run boundary instance, one worker execution attestation, and
  one worker execution provenance chain;
- one canonical typed `V48-D` conformance surface that binds one released `V48-C`
  worker-envelope chain to one frozen four-carrier observed-action set and emits one
  replayable `worker_boundary_conformance_report@1`;
- one canonical typed `V48-E` delegated-topology surface that binds one released
  parent `V48-D` report and one released child `V48-D` report into one bounded
  `worker_delegation_topology@1` with one explicit `supervisor_to_worker` handoff
  edge and no boundary widening;
- a generic deterministic harness kernel with taskpack compile/run/verify surfaces.

The branch-local internal `V48` ladder no longer has a remaining selected seam.

Today the repo does not have a further internal `V48` continuation selected.

`V48` now covers, on `main`:

- released policy/scope-to-taskpack binding;
- released deterministic taskpack compilation over that binding;
- released worker-run boundary instance / attestation / provenance linkage;
- released replayable single-worker conformance over frozen observed-action carriers;
- released bounded delegated topology over two released conformant worker surfaces.

So the remaining work after `vNext+116` is not another implicit `V48-F`.

Any later widening beyond the shipped same-boundary, one-edge delegated topology
should be treated as:

- a new planning decision;
- a downstream consumer or adjacent family choice; or
- a separately scoped future seam selection,

rather than as an ambient continuation automatically authorized by this planning
surface.

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
- Current family state for this branch:
  - `V48-A` closed on `main`
  - `V48-B` closed on `main`
  - `V48-C` closed on `main`
  - `V48-D` closed on `main`
  - `V48-E` closed on `main`
- Recommended next path for this branch:
  - no further internal `V48` path currently selected
- Recommended next concrete arc for this branch if selected:
  - no further internal `V48` concrete arc currently selected
- Default path selection for this branch:
  - no further internal `V48` path currently selected after the bounded
    `V48-A` through `V48-E` ladder closed on `main`

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

None of those released surfaces, by themselves, solved:

- how released policy rows and released repo scope become one typed taskpack boundary;
- how a worker run proves which released policy and scope artifacts governed it;
- how to reject runs that are taskpack-valid in the generic sense but not actually
  derived from the intended released policy/scope lineage.

`V48` is now the released bounded family that filled that bridge on `main` without
reopening released descriptive, normative, or harness-kernel baselines.

## Completed Family (`V48`)

`V48` should now be read as the released bounded enactment bridge around:

- task-scoped policy binding profiles;
- repo-scope binding profiles;
- deterministic taskpack derivation from released policy + scope;
- worker execution attestation / provenance that names the compiled boundary;
- task/run-scoped boundary instances that name one concrete compiled boundary for one
  worker-run context;
- deterministic conformance reporting over observed worker actions versus the compiled
  boundary;
- bounded supervisor/worker delegated topology over two released conformant worker
  surfaces with exact same repo/snapshot/compiled-boundary posture;
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

The family should treat later multi-worker orchestration beyond the shipped
`V48-E` seam as:

- downstream consumers or adjacent later families;
- not something automatically selected inside this planning surface now that the
  bounded `V48` ladder is closed on `main`.

The released `V48` work made explicit:

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
- how delegated topology binds one released parent `V48-D` report and one released
  child `V48-D` report into one bounded handoff artifact without widening the shared
  compiled boundary.
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
| `V48-A` | policy/scope to taskpack binding profile | candidate `anm_taskpack_binding_profile@1` over released `V47` policy lineage and released `V45` scope lineage | closed_on_main |
| `V48-B` | deterministic policy-to-taskpack compiler lane | candidate `compiled_policy_taskpack_binding@1` plus deterministic taskpack derivation from the released binding profile | closed_on_main |
| `V48-C` | worker execution envelope + attestation lane | candidate `task_run_boundary_instance@1`, candidate `worker_execution_attestation@1`, and candidate `worker_execution_provenance@1` | closed_on_main |
| `V48-D` | post-run conformance / replay lane | candidate `worker_boundary_conformance_report@1` plus replayable diagnostics over frozen observed-action carriers | closed_on_main |
| `V48-E` | delegated multi-worker topology seam | candidate `worker_delegation_topology@1` and bounded supervisor/worker handoff doctrine | closed_on_main |

These output names are planning-level candidate names, not lock-level schema authority.

`V48-A` through `V48-E` should now be read together as the completed bounded
policy-to-taskpack and worker-enforcement bridge on `main`.

That is:

- `V48-A` released one canonical policy/scope-to-taskpack binding doctrine;
- `V48-B` released deterministic lowering of that doctrine into released kernel
  taskpack carriers;
- `V48-C` released one worker-run boundary instance plus attestation / provenance
  linkage over one compiled boundary;
- `V48-D` released replayable single-worker conformance over one frozen observed-action
  carrier set;
- `V48-E` released one bounded supervisor-to-worker delegation topology over two
  released `V48-D` reports with exact same repo/snapshot/compiled-boundary posture.

So the `A -> B -> C -> D -> E` staging should now be read as a completed bounded
family ladder rather than as an unfinished bridge.

## Current Family Closeout (`V48`)

`V48-E` is now closed on `main` and should be read as bounded to:

- one released parent `worker_boundary_conformance_report@1`;
- one released child `worker_boundary_conformance_report@1`;
- one explicit `supervisor_to_worker` edge only;
- one explicit parent task identity, one explicit delegated task identity, and one
  explicit child task identity;
- one exact same repo identity, one exact same snapshot identity, and one exact same
  compiled-boundary posture on parent and child;
- one distinct parent worker subject and one distinct child worker subject;
- one typed `handoff_result` with frozen starter supporting-diagnostic families;
- one topology artifact only, with no recursive fan-out or repo-wide orchestration.

It does not authorize:

- worker/worker doctrine;
- recursive topology or many-child topology;
- repo-wide orchestration regime;
- open-ended planner decomposition;
- compiled-boundary widening algebra;
- execution or approval authority expansion.

No further internal `V48` continuation path is currently selected in this planning
surface.

Any later widening beyond the shipped same-boundary, one-edge delegated topology
should be proposed through a new planning move rather than treated as an implicit
`V48-F`.

## Candidate Package Ownership

Package ownership should now be read as selected and released on `main` for this
bounded family.

The implemented `V48` ladder is carried by:

- `packages/adeu_agent_harness` as the released owner for the bridge surfaces;
- released `packages/adeu_repo_description` outputs are consumed as scope inputs, not
  reopened as first-owner surfaces;
- released `packages/adeu_semantic_source` and `packages/adeu_commitments_ir` outputs
  are consumed as policy inputs, not reopened as first-owner surfaces.

This should still be read as bounded family ownership rather than as a universal claim
about every possible later downstream orchestration surface.

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
- no further internal `V48` topology or orchestration path is selected by this
  planning draft now that the bounded `V48-A` through `V48-E` ladder is closed on
  `main`;
- no repo-wide orchestration regime is selected by this planning draft.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v30.md",
  "baseline_arc": "vNext+116",
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
  "closed_current_family_paths": [
    "V48-A",
    "V48-B",
    "V48-C",
    "V48-D",
    "V48-E"
  ],
  "planned_current_family_paths": [],
  "default_next_arc_candidate_for_this_branch": null,
  "default_next_concrete_arc_candidate_for_this_branch": null,
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
  "package_selection_status": "selected_and_released_on_main",
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
  "multi_worker_topology_initially_deferred": false,
  "multi_worker_topology_default_next_path_selected": false,
  "planning_boundary_mode": "scope_guard_not_lock_authority",
  "authority_layering_note": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
  "horizon_glossary_note": "docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md",
  "future_seam_promotion_rules_note": "docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md"
}
```
