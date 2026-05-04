# Draft Multi-Arc Roadmap Post V84 v0

Status: planning roadmap after `V84` closed on `main` through `vNext+238`,
after the combined `V68` through `V84` dogfood probe, and after the support
note `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
was drafted.

Authority layer: planning.

This roadmap records the current best anticipated post-`V84` territory. It is
a support planning surface for the next family selector. It is not a selector,
lock, starter bundle, implementation authority, runtime authority, product
authority, release authority, graph-memory authority, recursive-policy
authority, or future-family selection by itself.

Interpretive doctrine for this planning surface:

- horizon-sensitive terms such as `bounded`, `complete`, `closed`,
  `deferred`, and `forbidden` should be read using
  `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`;
- planning-boundary lines below are scope guards and
  absence-of-authorization statements for this roadmap, not lock-equivalent
  permanent prohibitions by themselves;
- planning-vs-lock authority transfer should be read using
  `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`;
- future seam selection and widening posture should be read using
  `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`;
- internal family sequencing should follow
  `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`: one family-level
  `DRAFT_NEXT_ARC_OPTIONS_v*` selector per family, then per-slice
  `vNext+<n>` starter bundles.

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
- `V84` is closed on `main` as the work-packet activation-review family.
- latest closed implementation arc: `vNext+238`
- latest family-level selector: `docs/DRAFT_NEXT_ARC_OPTIONS_v74.md`
- next planning obligation: draft `docs/DRAFT_NEXT_ARC_OPTIONS_v75.md` if the
  next family is selected outside closed `V84`.

The current combined dogfood probe is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_V84_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_V84_COMBINED_DOGFOOD_TEST_v0.json`

The dogfood result says the closed families compose in this direction:

```text
V68 map substrate
  -> V69 source-bound candidate pressure
  -> V70 evidence / adversarial / gap classification
  -> V70 pre-ratification handoff
  -> V71 request / settlement / ratification-review / handoff
  -> V72 containment plan / trial / effect / rollback / authority posture
  -> V73 outcome entry / observation / regression / tool-fitness / ledger
  -> V74 operator projection / typed case view / comparison / visibility / handoff
  -> V75 dispatch review / worker planning / reconciliation posture / handoff
  -> V76 reconciliation / arbiter claim mapping / relation review / dissent / handoff
  -> V77 runtime-permission review / command preflight / effect / telemetry / rollback / authority handoff
  -> V78 runtime execution authority review / tool-use permission envelope / command-scope / readiness handoff
  -> V79 controlled execution review / run-plan review / tool-invocation-plan review / monitoring / handoff
  -> V80 external branch activation review / data-tool-submission-result boundaries / non-activation handoff
  -> V81 cross-corpus governance review / corpus boundary / provenance / authority gaps / non-ingestion handoff
  -> V82 corpus-ingestion authority review / preflight / connector boundary / data-handling authority / non-transfer handoff
  -> V83 semantic implementation-spec review / intent closure / edge decomposition / artifact obligations / projection packet / work-packet handoff
  -> V84 work-packet activation review / scope / target boundary / validation evidence plan / readiness summary / later-lock handoff
```

`V84-C` carries future canonical implementation-lock review pressure forward as
a later-review request. It does not create an implementation lock, activate a
work packet, execute implementation, mutate targets, authorize product /
release / graph surfaces, amend recursive policy, or select `V85`.

## Roadmap Thesis

The post-`V84` territory has two live bands:

1. Immediate upstream institutionalization of the semantic declaration
   meta-loop.
2. Downstream implementation, product, graph, runtime, and policy seams that
   remain visible but should not be selected by accident.

The immediate pressure is not "implement the work packet." The immediate
pressure is:

```text
natural task / code context
  -> typed semantic declaration
  -> canonical pointer lookup
  -> class-indexed obligation expansion
  -> evidence contract and edge probes
  -> independent audit
  -> deterministic closeout routing
```

This is the architectural inversion recorded in
`docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`:

```text
Do not put the whole institution inside the model.
Put the model inside the institution.
```

The model should become a bounded artifact-producing office that obeys
semantic pointers, artifact shapes, declared uncertainty slots, and transition
tables. The harness owns sequence meaning.

## Roadmap Operating Model: Territory Graph, Not Queue

This roadmap should be read as a territory graph, not a pre-authorized queue.

`V85` is the recommended next selector target because the newly surfaced
semantic declaration meta-loop is now the nearest missing upstream substrate.
It should not erase the `V84-C` canonical implementation-lock pressure. It
should make the precondition to robust implementation-lock review stronger:
the repo needs a typed way to declare the semantic act before obligations,
evidence, audit, and closeout routing are expanded.

Minimum continuation posture values:

- `selected_next_candidate`
- `mapped_not_selected`
- `deferred_to_later_family`
- `conditional_branch`
- `blocked_pending_source`
- `blocked_pending_authority`
- `superseded_or_renamed`

Only a future `DRAFT_NEXT_ARC_OPTIONS_v*` selector may select a family.

## Continuation Map

| Candidate / band | Theme | Likely ladder | Current posture | Reason |
|---|---|---|---|---|
| `V85` | semantic declaration / canonical meta-list review | `V85-A` declaration request, source index, non-authority guardrail; `V85-B` canonical meta-list lookup index, operator/class/obligation registry, opaque and explicit pointer fixtures; `V85-C` declaration review summary, lookup handoff, family closeout alignment | `selected_next_candidate` for future selector | nearest missing upstream substrate after `V83` and `V84`; makes model role pointer-bound and artifact-bound before implementation-lock review widens |
| `V86` | obligation expansion / evidence contract / edge probe plan | obligation expansion bundle, edge probe plan, evidence contract, closeout witness requirement map | `mapped_not_selected` | depends on released `V85` declaration and canonical lookup rows |
| `V87` | reviewer / auditor taskpack and audit artifact review | reviewer taskpack, audit report, boundary conformance review, audit non-authority guardrail | `mapped_not_selected` | depends on `V86` evidence and obligation expansion substrate; keeps reviewer separate from worker and meta-orchestrator |
| `V88` | deterministic closeout transition table / remand routing | transition table, closeout adjudication summary, remand route register, waiver / permanence / unknown-resolution guardrails | `mapped_not_selected` | closes the semantic declaration meta-loop without making the model the process-controller |
| canonical implementation-lock review | later lock review over released `V84-C` readiness packages | canonical implementation lock request, lock input bundle, lock stop-gate, implementation-slice readiness | `deferred_to_later_family` | `V84-C` emitted real pressure, but the semantic declaration meta-loop can make later implementation locks more principled |
| Morphic UX implementation review | Morphic UX projection implementation under bounded UX doctrine | Morphic UX work-packet source rows, UX law binding, UI target boundaries, visual/evidence review | `deferred_to_later_family` | Morphic UX remains an instantiation of the higher intent-to-artifact problem; no runtime UI mutation is selected here |
| direct OAI harness implementation review | direct provider / Codex harness implementation review | provider profile source rows, capability boundary, tool/runtime authority guardrails, harness implementation packet | `deferred_to_later_family` | direct-harness support docs are context and pressure, not provider runtime authority |
| meta-orchestrator workflow activation review | procedural circuit over declaration, expansion, audit, and closeout offices | loop-state transition review, worker office boundary, route-table validation, runtime non-transition guardrail | `deferred_to_later_family` | should likely consume `V85` through `V88`, not precede them as runtime behavior |
| product typed-adjudication report / workbench review | read-only reports over typed adjudication and intent-to-artifact packets | report export, case visibility, authority-risk report, product non-authorization guardrail | `mapped_not_selected` | product legibility is useful but does not authorize productization |
| graph memory / living decision graph | queryable case, source, authority, evidence, exception, and handoff graph | graph source index, queryable decision memory, non-authority traversal guardrail | `mapped_not_selected` | row volume makes this attractive, but graph traversal remains non-authority |
| external branch / `V43` participation | external contest or external-world participation review | branch posture, data/tool/submission/result/withdrawal authority | `conditional_branch` | `V80` typed activation review; actual participation remains unselected and authority-bound |
| corpus ingestion / connector / endpoint action | actual ingestion, connector activation, endpoint access, data transfer | authority review, preflight, action envelope, non-transfer guardrail | `blocked_pending_authority` | `V82` typed review only; no data transfer or endpoint action is authorized |
| cross-corpus adjudication execution | adjudication over imported / customer / benchmark / paper corpora | ingestion authority, provenance, benchmark guardrail, adjudication execution review | `blocked_pending_source` | `V81` and `V82` made governance/ingestion review visible, not execution-ready |
| release / PR / commit / merge authority | shipped implementation authority | commit/release authority record, PR/merge/release guardrails, maintainer authority source | `blocked_pending_authority` | no current post-`V84` support row authorizes release |
| recursive policy amendment | policy amendment from recursive outcome or loop evidence | amendment request, authority profile, settlement, adoption review | `blocked_pending_authority` | recurring success is not self-approval |

## Immediate `V85` Candidate Shape

Recommended family name for the next selector:

```text
V85: semantic declaration and canonical meta-list review
```

Recommended family thesis:

`V85` may make natural task / code context reviewable as typed semantic
declaration and canonical pointer lookup substrate, but it must not expand
obligations into implementation authority, run workers, create
implementation locks, execute commands, mutate targets, productize, create
graph-memory authority, amend recursive policy, or select `V86`.

### `V85-A` Candidate Surfaces

Recommended starter surfaces:

- `repo_turn_semantic_declaration_request@1`
- `repo_semantic_declaration_source_index@1`
- `repo_semantic_declaration_non_authority_guardrail@1`

`V85-A` should record source-bound declaration pressure only. It should not
create the canonical meta-list, expand obligations, emit evidence contracts,
create worker taskpacks, produce audit reports, or run closeout routing.

### `V85-B` Candidate Surfaces

Recommended support surfaces:

- `repo_canonical_meta_lookup_index@1`
- `repo_semantic_operator_class_registry@1`
- `repo_obligation_family_registry@1`
- `repo_semantic_pointer_lookup_fixture@1`

`V85-B` should prove exact pointer handling before natural binding is trusted:
opaque ID lookup, explicit semantic pointer lookup, order preservation,
duplicate preservation, unknown-pointer abstention, conflict routing, and no
class or obligation invention.

### `V85-C` Candidate Surfaces

Recommended closeout surfaces:

- `repo_semantic_declaration_review_summary@1`
- `repo_post_semantic_declaration_review_handoff@1`
- `repo_semantic_declaration_family_closeout_alignment@1`

`V85-C` should summarize declaration readiness and hand off to future
obligation expansion or future family review. It must not select `V86`.

## `V86` Through `V88` Planning Handles

If `V85` closes cleanly, the likely semantic meta-loop continuation is:

```text
V85 semantic declaration / canonical pointer lookup
  -> V86 obligation expansion / evidence contract / edge probe plan
  -> V87 independent audit taskpack / audit report review
  -> V88 deterministic closeout transition table / remand routing
```

Those labels are planning handles only. They may be split, renamed, merged, or
deferred by future selectors after released upstream rows exist.

`V86` should not run implementation. It should expand obligations and evidence
requirements from known declarations and canonical lookup rows.

`V87` should not become auditor sovereignty. It should type reviewer/auditor
taskpacks and audit artifacts as evidence for later deterministic closeout.

`V88` should not become runtime orchestration. It should type closeout
transition tables and remand routing over accepted artifacts.

## Pending Seams Preserved From Earlier Roadmaps

The following seams remain real, but unselected:

- canonical implementation-lock review;
- Morphic UX projection / implementation review;
- direct OAI harness implementation review;
- meta-orchestrator workflow activation review;
- product typed-adjudication reporting / workbench review;
- graph memory / living decision graph;
- release / PR / commit / merge authority;
- external branch participation and `V43` contest activation;
- corpus ingestion, connector activation, endpoint access, and data transfer;
- cross-corpus adjudication execution;
- benchmark truth and global model selection;
- recursive policy amendment.

The older post-`V74` roadmap labels have been partly superseded by completed
families:

- `V75` through `V84` are no longer candidate bands; they are closed families.
- the older graph-memory placeholder remained unselected and was not consumed
  by `V82`, which became corpus-ingestion authority review after `V81-C`
  emitted nearer source-bound pressure;
- productized typed adjudication, graph memory, external participation,
  experiment design, and recursive policy remain mapped but unselected.

## Entry And Non-Entry Criteria For `V85`

`V85` is selector-ready if the future selector can cite:

- released `V83` and `V84` closeout substrate;
- the combined `V68` through `V84` dogfood support record;
- the canonical semantic declaration meta-loop support note;
- concrete evidence that implementation-lock review still depends on
  upstream semantic act classification;
- a non-authority boundary showing that declaration is not implementation,
  obligation expansion, audit, closeout routing, runtime transition, product
  authorization, release, graph memory, or policy amendment.

`V85` must not be used if the only evidence is:

- operator desire to implement the next work packet;
- a model-generated declaration with no source witnesses;
- a broad natural-language task with no declared uncertainty route;
- a non-canonical class or obligation treated as accepted;
- an opaque pointer expanded by model preference rather than registry lookup;
- a support doc treated as runtime authority;
- Morphic UX, direct OAI, or meta-orchestrator support pressure treated as
  implementation authorization.

## Inputs For `V85` Starter Drafting

Primary repo inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v74.md`
- `docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83_FAMILY_CLOSEOUT_v0.md`
- `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_V84_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_V84_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v238/evidence_inputs/v84_family_closeout_alignment_v238.json`
- `artifacts/agent_harness/v238/evidence_inputs/v84c_work_packet_activation_closeout_evidence_v238.json`
- `apps/api/fixtures/repo_description/vnext_plus238/repo_work_packet_activation_readiness_summary_v238_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus238/repo_post_work_packet_activation_review_handoff_v238_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus238/repo_work_packet_activation_family_closeout_alignment_v238_reference.json`

Support / doctrine inputs:

- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`
- `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
- `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
- `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`
- `docs/support/morphic_ux. v2.md`

## Recommended Next Drafting Move

Draft `docs/DRAFT_NEXT_ARC_OPTIONS_v75.md` as the post-`V84` selector with:

1. immediate selection of `V85` as semantic declaration / canonical meta-list
   review;
2. `V85-A` as the first active slice;
3. `V86` through `V88` mapped as unselected planning handles;
4. canonical implementation-lock review, Morphic UX implementation review,
   direct OAI harness implementation review, meta-orchestrator workflow
   activation review, product review, graph memory, release authority, and
   recursive-policy amendment preserved as deferred seams.

The selector should use this controlling sentence:

```text
V85 may make semantic declaration and canonical pointer lookup reviewable, but
it must not expand those declarations into implementation authority, worker
execution, runtime transition, product authorization, release, graph-memory
authority, recursive policy amendment, or later-family selection.
```
