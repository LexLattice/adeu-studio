# Draft Next Arc Options v73

Status: planning handoff after `vNext+232` / `V82-C` merged on `main`, after
the `V82` family closeout pass, and after the combined `V68` through `V82`
dogfood probe.

Authority layer: planning.

This draft records the post-`V82` frontier. It does not authorize
implementation, code edits, command execution, tool invocation, worker
dispatch, external branch activation, corpus ingestion, connector activation,
endpoint access, cross-corpus adjudication execution, product authorization,
PR creation, commit, merge, release, benchmark truth, graph-memory authority,
recursive policy amendment, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v72.md`, which selected the `V82`
corpus-ingestion authority-review family. `vNext+230`, `vNext+231`, and
`vNext+232` then closed `V82-A`, `V82-B`, and `V82-C` without creating
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
- latest closed implementation arc: `vNext+232`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v72.md`
- next planning obligation: select and review `V83` as the next family outside
  closed `V82`.

The combined `V68` through `V82` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended and that
`V82` closed corpus-ingestion authority review without corpus ingestion,
data transfer, customer-data handling, connector activation, endpoint access,
cross-corpus adjudication execution, benchmark truth, imported-result truth,
product authorization, release, graph-memory authority, recursive policy
amendment, or `V83` selection.

## Next Planning Question

The long `V68` through `V82` run has made increasingly many downstream action
surfaces reviewable without authorizing them. The next bottleneck is not
runtime execution, connector activation, productization, or corpus ingestion.
It is the institutional process that should happen before implementation:

```text
intent
  -> semantic closure
  -> edge / ambiguity / authority decomposition
  -> implementation-spec projection
  -> later work packet or implementation slice
```

The repo already practices this informally through ADEU arc drafting,
external review, slice starters, implementation PRs, review-fix loops, lean
closeouts, family closeouts, and dogfood probes. The process is effective, but
still partly proto-institutional: the semantic edges are often held in prose
memory and operator/model reasoning rather than as a first-class typed
substrate.

Should the next family be `V83`: semantic implementation specification review,
intent contracts, edge decomposition, artifact obligation maps, and
implementation-spec projection packets?

This selector intentionally treats `V83` as semantic implementation-spec
**review**, not implementation. It may type what must be true before a later
implementation slice can claim that code, UI, schema, workflow, or artifact
work is semantically aligned with intent. It must not edit files as a result
of the spec, execute commands, open PRs, dispatch workers, or certify its own
spec as implementation truth.

## Recommended Next Pressure

- family: `V83`
- proposed family name:
  - `V83: semantic implementation specification review, intent edge
    decomposition, artifact obligation mapping, and non-implementation
    guardrails`
- recommended planning posture:
  - select `V83` as the next standalone bridge family after `V82`;
  - select `V83-A` as the next default candidate for `vNext+233`;
  - consume `V68` through `V82` family closeouts and the combined dogfood as
    the repo-native governance substrate;
  - consume the local direct-harness ODEU docs as support context, not lock
    authority:
    - `/home/rose/work/LexLattice/codex-review-shell-direct/docs/META_ORCHESTRATOR_LOOP_ODEU_SPEC.md`
    - `/home/rose/work/LexLattice/codex-review-shell-direct/docs/OAI_CODEX_UPSTREAM_ODEU_PROFILE.md`
  - treat Morphic UX v2 as an important downstream test case, but not the
    umbrella family:
    - `docs/support/morphic_ux. v2.md`
  - define source-bound intent contracts, source indexes, and
    non-implementation guardrails before edge decomposition, obligation maps,
    projection packets, or work-packet handoffs are represented.
  - make model/agent-generated implementation-spec candidates first-class as
    candidate-only source rows with prompt / profile / generation provenance,
    not as semantic truth or implementation authority.

`V83` should type the question: "what does intent require before any concrete
artifact implementation can be soundly specified?" It must not perform the
implementation or collapse a spec into accepted artifact truth.

## Proposed Family Decomposition

`V83` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V83-A` | semantic intent contract, intent source index, and non-implementation guardrail |
| `V83-B` | intent edge decomposition, artifact obligation map, and semantic drift / ambiguity register |
| `V83-C` | implementation-spec projection packet, intent-to-work-packet handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`V83-A` should be the first active slice. Candidate starter surfaces:

- `repo_semantic_intent_contract@1`
- `repo_intent_source_index@1`
- `repo_intent_non_implementation_guardrail@1`

Recommendation: select `V83-A` as the next default candidate after this
selector, with `vNext+233` as the canonical starter bundle if no intervening
arc claims that number.

Later `V83` surfaces should remain planning-layer until their own starter
locks:

- `repo_intent_edge_decomposition@1`
- `repo_artifact_obligation_map@1`
- `repo_semantic_drift_ambiguity_register@1`
- `repo_implementation_spec_projection_packet@1`
- `repo_intent_to_work_packet_handoff@1`
- `repo_semantic_implementation_spec_family_closeout_alignment@1`

Post-`V83-A` continuation posture: after `vNext+233` closes on `main`, select
`V83-B` as the next default candidate for the next canonical starter bundle.
Machine-detectable restatement: select `V83-B` as the next default candidate.
That selection remains inside the already selected `V83` family and does not
create a new next-arc-options selector version.

Post-`V83-B` continuation posture: after the `V83-B` slice closes on `main`,
select `V83-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V83` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- code implementation or file edits;
- command execution or tool invocation;
- worker assignment, dispatch execution, or meta-orchestrator runtime;
- live OAI / Codex direct harness behavior;
- provider capability mutation, model selection, quota controls, or tool
  broker authority;
- Morphic UX runtime changes, composer geometry runtime fixes, or UI renderer
  rewrites;
- generalized digital-artifact projection beyond implementation-spec review;
- legal, theorem, paper, research-question, or product-spec projection
  schemas;
- corpus ingestion, customer-data handling, connector activation, endpoint
  access, or data transfer;
- external branch activation, `V43` contest participation, external
  submission, or benchmark truth;
- product launch, product-market validation, or product authorization;
- PR creation, commit, merge, release, or released-truth authority;
- graph-memory authority or living-memory runtime;
- recursive policy amendment;
- `V84` or any later family.

Those remain mapped future seams until their own planning and lock surfaces
select them.

## Entry And Non-Entry Criteria

`V83` is planning-ready because the post-`V82` substrate shows that the repo can
carry review pressure through many authority layers while preserving the
boundary that review is not execution. The next practical need is to
institutionalize the upstream reasoning step that decides what should be coded
relative to intent.

`V83-A` request recordability must be stricter than operator desire. A semantic
intent contract may be recorded only when it cites concrete source rows or
explicit absence rows for:

- the user or operator intent;
- relevant repo-family closeout or dogfood substrate;
- domain support docs or external support substrate;
- known non-goals;
- known authority or implementation boundaries.

An eligible `V83-A` starter row must cite released post-`V82` substrate and at
least one concrete intent source. Support docs may contextualize the family,
but support context cannot be the only source for an eligible intent contract.
Missing expected sources must become explicit absence rows. Generated model or
agent spec candidates, if present, may support recordability only as
candidate-only review sources unless bounded prompt/context/profile provenance
and source-bound non-goals, authority boundaries, and success horizons are
present.

`V83` must not be used if the only evidence is:

- a model suggestion that a feature sounds useful;
- an operator preference without source refs or non-goal boundaries;
- a support note treated as lock authority;
- an external project doc treated as repo truth without imported-source
  posture;
- a Morphic UX example treated as a general implementation contract;
- a direct-harness provider profile treated as runtime capability authority;
- a generated implementation spec treated as code correctness;
- a generated implementation spec treated as semantic contract authority,
  implementation truth, or executable work-packet authority;
- passing syntax or tests treated as semantic intent preservation.

## Inputs For Starter Drafting

Primary repo inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v72.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_SEMANTIC_IMPLEMENTATION_SPECIFICATION_V83_PLANNING_v0.md`
- `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v232/evidence_inputs/v82_family_closeout_alignment_v232.json`
- `artifacts/agent_harness/v232/evidence_inputs/v82c_corpus_ingestion_review_closeout_evidence_v232.json`
- `apps/api/fixtures/repo_description/vnext_plus232/repo_corpus_ingestion_review_summary_v232_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus232/repo_post_corpus_ingestion_review_handoff_v232_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus232/repo_corpus_ingestion_review_family_closeout_alignment_v232_reference.json`

Support / doctrine inputs:

- `docs/support/morphic_ux. v2.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`
- `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
- `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
- `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`

External local support inputs:

- `/home/rose/work/LexLattice/codex-review-shell-direct/docs/META_ORCHESTRATOR_LOOP_ODEU_SPEC.md`
- `/home/rose/work/LexLattice/codex-review-shell-direct/docs/OAI_CODEX_UPSTREAM_ODEU_PROFILE.md`

These external local docs are support substrate for the initial `V83` family
review. If they become active source rows in a future lock, the lock should
represent them as imported external support sources or copy the relevant
excerpts into repo-owned support artifacts rather than relying on prose memory.
If any referenced Morphic UX or direct-harness source is unavailable at lock
time, the starter should record explicit import-gap or absence rows and keep
related examples blocked or context-only.

## Lock Readiness Note

This selector is not an active lock. If this family is accepted, the next
starter bundle should be:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS233.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS233.md`
- `docs/ASSESSMENT_vNEXT_PLUS233_EDGES.md`

That lock should select only `V83-A`:

- `repo_semantic_intent_contract@1`
- `repo_intent_source_index@1`
- `repo_intent_non_implementation_guardrail@1`

It should not select `V83-B`, `V83-C`, implementation, work-packet execution,
meta-orchestrator runtime, Morphic UX runtime changes, direct OAI runtime
behavior, command execution, PR creation, release, product authorization, graph
memory, or generalized digital-artifact projection.

## Post-`V83` Territory

Do not select the next family inside this selector. If `V83-C` later emits
source-bound projection packets and intent-to-work-packet handoffs, the likely
next pressure is implementation work-packet activation review, not immediate
implementation. That possible `V84` should be chosen only by a future selector
after the `V83` family closes.
