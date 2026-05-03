# Draft Next Arc Options v74

Status: planning handoff after `vNext+235` / `V83-C` merged on `main`, after
the `V83` family closeout pass, and after the combined `V68` through `V83`
dogfood probe.

Authority layer: planning.

This draft records the post-`V83` frontier. It does not authorize
implementation, code edits, command execution, tool invocation, target
mutation, worker dispatch, meta-orchestrator runtime transition, Morphic UX
runtime changes, direct OAI runtime behavior, PR creation, commit, merge,
release, product authorization, graph-memory authority, recursive policy
amendment, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v73.md`, which selected the `V83` semantic
implementation-specification review family. `vNext+233`, `vNext+234`, and
`vNext+235` then closed `V83-A`, `V83-B`, and `V83-C` without creating
additional family selector versions.

## Current Frontier

- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- `V70` is closed on `main` as the candidate review-classification family.
- `V71` is closed on `main` as the candidate ratification-review family.
- `V72` is closed on `main` as the contained integration-review family.
- `V73` is closed on `main` as the candidate outcome-review family.
- `V74` is closed on `main` as the operator-projection family.
- `V75` is closed on `main` as the dispatch-review family.
- `V76` is closed on `main` as the reconciliation / arbiter review family.
- `V77` is closed on `main` as the runtime-permission review family.
- `V78` is closed on `main` as the runtime execution authority review family.
- `V79` is closed on `main` as the controlled execution review family.
- `V80` is closed on `main` as the external branch activation review family.
- `V81` is closed on `main` as the cross-corpus governance family.
- `V82` is closed on `main` as the corpus-ingestion authority-review family.
- `V83` is closed on `main` as the semantic implementation-specification
  review family.
- latest closed implementation arc: `vNext+235`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v73.md`
- next planning obligation: select and review `V84` as the next family outside
  closed `V83`.

The combined `V68` through `V83` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended and that
`V83` closed semantic implementation-spec review without downstream
implementation work-packet execution, code-change execution from generated
specs, command execution, tool invocation, worker dispatch,
meta-orchestrator runtime transition, Morphic UX runtime change, direct OAI
runtime behavior, product authorization, release, graph-memory authority,
recursive policy amendment, or `V84` selection.

## Next Planning Question

`V83` made the upstream intent-to-spec transformation explicit:

```text
intent
  -> semantic contract
  -> edge decomposition
  -> artifact obligations
  -> drift / ambiguity posture
  -> implementation-spec projection packet
  -> later work-packet handoff
```

The next missing layer is not implementation itself. The next missing layer is
the review posture that decides whether a released `V83-C` projection packet
is bounded enough, source-bound enough, target-bound enough, validation-bound
enough, and authority-bound enough to become a later implementation lock or
work-packet review package.

Should the next family be `V84`: implementation work-packet activation review,
scope contracts, target-surface boundaries, validation evidence planning, and
non-execution guardrails?

This selector intentionally treats `V84` as work-packet activation **review**,
not work-packet activation and not implementation. It may type what would be
needed before a later family or canonical implementation lock can activate a
bounded work packet. It must not edit files, run commands, invoke tools,
create PRs, commit, merge, release, mutate runtime behavior, or treat a
projection packet as implementation authority.

Controlling invariant:

```text
V84 may produce an implementation-lock review package, but it may not produce
an implementation work packet with execution authority.
```

## Recommended Next Pressure

- family: `V84`
- proposed family name:
  - `V84: implementation work-packet activation review, target-scope binding,
    validation evidence planning, and non-execution guardrails`
- recommended planning posture:
  - select `V84` as the next standalone bridge family after `V83`;
  - select `V84-A` as the next default candidate for `vNext+236`;
  - consume `V68` through `V83` family closeouts and the combined dogfood as
    the repo-native governance substrate;
  - consume released `V83-C` projection packet, handoff, and family-closeout
    fixtures as concrete source rows;
  - define activation-review requests, activation source indexes, and
    non-execution guardrails before scope contracts, target boundaries,
    validation plans, readiness summaries, or post-activation handoffs are
    represented;
  - keep generated/model/agent/reviewer spec material candidate-only unless a
    released `V83-C` projection packet and quality gate already source-bind it.

`V84` should type the question: "what must be true before a semantic
implementation-spec projection can become a bounded later implementation work
packet?" It must not perform the implementation or collapse activation review
into execution.

## Proposed Family Decomposition

`V84` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V84-A` | work-packet activation-review request, activation source index, and non-execution guardrail |
| `V84-B` | work-packet scope contract, implementation target-surface boundary, validation evidence plan, and activation exception register |
| `V84-C` | activation readiness summary, post-work-packet-activation-review handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`V84-A` should be the first active slice. Candidate starter surfaces:

- `repo_work_packet_activation_review_request@1`
- `repo_work_packet_activation_source_index@1`
- `repo_work_packet_activation_non_execution_guardrail@1`

Recommendation: select `V84-A` as the next default candidate after this
selector, with `vNext+236` as the canonical starter bundle if no intervening
arc claims that number.

Later `V84` surfaces should remain planning-layer until their own starter
locks:

- `repo_work_packet_scope_contract@1`
- `repo_implementation_target_surface_boundary@1`
- `repo_work_packet_validation_evidence_plan@1`
- `repo_work_packet_activation_exception_register@1`
- `repo_work_packet_activation_readiness_summary@1`
- `repo_post_work_packet_activation_review_handoff@1`
- `repo_work_packet_activation_family_closeout_alignment@1`

Post-`V84-A` continuation posture: after `vNext+236` closes on `main`, select
`V84-B` as the next default candidate for the next canonical starter bundle.
Machine-detectable restatement: select `V84-B` as the next default candidate.
That selection remains inside the already selected `V84` family and does not
create a new next-arc-options selector version.

Post-`V84-B` continuation posture: after the `V84-B` slice closes on `main`,
select `V84-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V84` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- code implementation or file edits;
- work-packet activation or work-packet execution;
- command execution, tool invocation, or target mutation;
- worker assignment, dispatch execution, or meta-orchestrator runtime;
- Morphic UX runtime changes, UI renderer rewrites, or composer geometry
  runtime fixes;
- direct OAI / Codex harness runtime behavior, provider mutation, model
  selection, quota controls, or tool broker authority;
- PR creation, commit, merge, release, or released-truth authority;
- product launch, product-market validation, or product authorization;
- corpus ingestion, customer-data handling, connector activation, endpoint
  access, or data transfer;
- external branch activation, `V43` contest participation, external
  submission, or benchmark truth;
- graph-memory authority or living-memory runtime;
- generalized digital-artifact projection beyond implementation work-packet
  activation review;
- recursive policy amendment;
- `V85` or any later family.

Those remain mapped future seams until their own planning and lock surfaces
select them.

## Entry And Non-Entry Criteria

`V84` is planning-ready because `V83-C` emits source-bound projection packets,
quality gates, implementation-spec rows, and handoffs that require later
canonical locks before any implementation work packet can execute. The next
practical need is to type the activation-review package that bridges those
projection packets into future implementation locks without relying on
operator intuition.

`V84-A` request recordability must be stricter than desire to implement. An
activation-review request may be recorded when it cites released `V83-C`
projection / handoff / closeout rows or explicit absence rows. An eligible
activation-review request must cite:

- a released `V83-C` projection packet or handoff;
- a released `V83-C` quality gate or explicit blocker posture;
- known source rows for semantic intent, edge decomposition, artifact
  obligations, validation evidence requirements, and guardrails;
- target-surface posture that is bounded enough for later review;
- a canonical later-lock requirement;
- non-execution guardrails.

An eligible request must also carry a stable `activation_package_ref`,
non-granting activation authority posture, and explicit implementation-lock
status showing that no lock was created by `V84`. Generated work-packet
candidates, if present, must be provenance-bound and candidate-only. Target
family boundary posture must remain explicit for Morphic UX, direct OAI,
meta-orchestrator, product, graph, or future-family pressure.

Support docs, generated specs, operator preference, or a broad target label
may contextualize an activation-review request, but they cannot be the only
eligibility sources. Missing projection packets, missing quality gates,
missing target surfaces, broad/glob targets, missing validation evidence, or
carried semantic-drift blockers must be recorded as blockers rather than
smoothed into readiness.

`V84` must not be used if the only evidence is:

- a model suggestion that a generated spec should be implemented;
- a projection packet without released `V83-C` source binding;
- a quality gate that does not resolve to known review checks;
- target surfaces described only as broad package or repo globs;
- tests listed without edge-bound validation evidence requirements;
- missing or untyped canonical lock requirement;
- generated work-packet candidate without source-bound provenance;
- activation package rows whose scope, target, validation, or candidate
  lineage do not match;
- operator confirmation treated as implementation authority;
- a Morphic UX or direct OAI support example treated as runtime
  implementation authorization;
- a work-packet handoff treated as permission to edit files or open a PR.

## Inputs For Starter Drafting

Primary repo inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v73.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v235/evidence_inputs/v83_family_closeout_alignment_v235.json`
- `artifacts/agent_harness/v235/evidence_inputs/v83c_semantic_projection_closeout_evidence_v235.json`
- `apps/api/fixtures/repo_description/vnext_plus235/repo_implementation_spec_projection_packet_v235_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus235/repo_intent_to_work_packet_handoff_v235_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus235/repo_semantic_implementation_spec_family_closeout_alignment_v235_reference.json`

Support / doctrine inputs:

- `docs/support/morphic_ux. v2.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`
- `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
- `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
- `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`
