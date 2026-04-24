# Draft ARC Series Multi-Layer Mapping v2

Status: support-layer integrated review draft.

Authority layer: support.

This is the single root mapping document to review before drafting the next specific
arc families. It integrates the two original `xhigh` drafts, the two alternate `high`
drafts, the ODEU conceptual diff, and the follow-on meta-conversation about reasoning
recursion and internally generated workflow types.

This document does not supersede any lock, architecture/decomposition document,
planning selector, closeout decision, released schema, fixture, package, source module,
or maintainer decision. It is a support-layer synthesis and planning candidate map.

Support lineage now lives under `docs/support/arc_series_mapping/`:

- `DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v0.md`
- `DRAFT_ARC_SERIES_MULTILAYER_MAPPING_v0_ALT.md`
- `DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v1.md`
- `DRAFT_ARC_SERIES_MULTILAYER_MAPPING_v1_ALT.md`
- `DRAFT_ARC_SERIES_ODEU_CONCEPTUAL_DIFF_v0.md`
- `DRAFT_ARC_SERIES_ODEU_CONCEPTUAL_DIFF_v0.report.json`
- `odeu_conceptual_diff_report.schema.json`
- `DRAFT_ARC_SERIES_REASONING_RECURSION_LOOP_v0.md`
- `DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md`
- `REVIEW_GPTPRO_ARC_SERIES_MAPPING_V68_PLANNING_v0.md`
- `REVIEW_GPTPRO_ARC_SERIES_CARTOGRAPHY_ABC_SPECS_v0.md`

Follow-on review integration note:

- follow-on GPTPro feedback was pasted after the first `V68` starter bundle draft
  and is now preserved as
  `docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_MAPPING_V68_PLANNING_v0.md`;
- a second GPTPro review over the `V68-A/B/C` specs is preserved as
  `docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_CARTOGRAPHY_ABC_SPECS_v0.md`;
- the reviews are integrated as support-layer shaping evidence, not as authority;
- their main framing correction is adopted here:
  - `V68` is the only immediate drafting target;
  - `V69` through `V75` are a sequenced lifecycle hypothesis that `V68` must
    cartograph, not pre-authorized follow-on locks.
- their concrete `V68-A/B/C` patch set is adopted in the starter draft family:
  - `repo_*` schema names are used for repo ARC series cartography;
  - namespace kinds are kept tight, with source kind and authority layer carried
    by source-row fields;
  - closure posture and branch posture are separate row concerns;
  - derivation manifest, gap scan, and tool-run evidence surfaces are selected for
    the later `V68-B/C` specs rather than left optional.

Horizon-sensitive terms such as `bounded`, `closed`, `complete`, `deferred`,
`forbidden`, and `missing` follow `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`.
Planning-boundary claims here are scope guards, not lock-level prohibitions.

## Current Repo Frontier

Current frontier checked by GPTPro against repo zip snapshot
`6eb7a9c9538de672d9102714a0fc6e3b9b050afd`:

- latest locked continuation: `vNEXT_PLUS187`
- latest closed family slice: `V67-C`
- `V67` family posture: closed on `main`
- latest next-arc selector at reviewed snapshot: `DRAFT_NEXT_ARC_OPTIONS_v52.md`
- no `DRAFT_NEXT_ARC_OPTIONS_v53.md` was present in that snapshot
- next planning obligation: select / draft `V68` outside closed `V67`

This document now treats `DRAFT_NEXT_ARC_OPTIONS_v53.md` and
the draft `LOCKED_CONTINUATION_vNEXT_PLUS188.md` starter trio as the canonical
response to that frontier once the pre-start gate accepts them.

## Integrated Thesis

The ARC series is a single layered philosophy-engineering harness. It has been building
the conditions under which future reasoning, action, review, documentation, and
self-improvement can happen without silently converting prose, transcript, local file
mutation, worker output, benchmark output, or tool success into authority.

The prior four drafts converged on one point:

- the next concrete family should be `V68`, a whole-series cartography family.

They differed on what the rest of the missing set is optimizing for:

- the `xhigh` drafts optimize for recursive self-improvement lifecycle completeness;
- the `high` drafts optimize for near-term repo workflow authority shortcuts.

The integrated reading is that both are right at different layers. The future map must
preserve the recursive lifecycle while explicitly absorbing the operational seams that
the high drafts exposed. The GPTPro review narrows the immediate drafting posture:
only `V68` is selected for canonical drafting now; `V69` through `V75` remain mapped
as later hypotheses until their own planning and locks exist.

## Observed Recursion

This task sequence produced a real recursive signal:

```text
reasoning artifact
  -> changes human/operator conceptual state
  -> generates a new meta-task
  -> discovers a missing type
  -> creates a bounded support-layer type
  -> uses that type on the prior reasoning artifacts
  -> produces evidence for governing future instances of that move
```

The useful name for this is:

```text
self-evidencing workflow-type emergence
```

Strict reading:

- self-evidencing is not self-validating;
- the loop produced evidence that a workflow-type seam exists;
- it did not prove that `odeu_conceptual_diff_report@1` is final, released, or
  generally adequate;
- the human operator was internal to the loop because the prior artifacts changed the
  operator's next question;
- that changed question is outcome evidence for future candidate intake and review.

ODEU classification:

- Ontology: a new support-layer artifact type emerged, conceptual diff over reasoning
  artifacts.
- Epistemics: its value was shown by use, not asserted abstractly.
- Deontics: it stayed support-layer, anchored in nearby diff/comparison families, and
  did not mint lock, runtime, merge, or release authority.
- Utility: it gives concrete evidence for `V68`, `V69`, `V70`, `V73`, and `V74`.

## Product Projection

The product-facing wedge is typed adjudication as a service:

```text
raw repo / PR / design fork / research artifact / model outputs
  -> typed conceptual audit
  -> ODEU decomposition
  -> evidence and tool-applicability report
  -> authority-risk map
  -> edge / weak-point ledger
  -> implementation-safe next slice
  -> machine-followable report artifact
```

This should be understood as a `V74`-facing product projection, not as an immediate
shortcut around `V68` through `V73`.

The external category is:

```text
scientific A/B testing for model reasoning outputs on a user's own substrate
```

Unlike generic benchmarks, the comparison is grounded in a fixed prompt, fixed repo or
corpus, explicit comparison schema, typed ODEU axes, recorded evidence, model/posture
provenance, and downstream recommendation.

Candidate product bundle:

- `odeu_conceptual_analysis@1`;
- `model_output_comparison_case@1`;
- `tool_applicability_report@1`;
- `authority_boundary_map@1`;
- `edge_seam_register@1`;
- `weak_point_ledger@1`;
- `next_slice_recommendation@1`;
- `synthesis_candidate@1`.

Use-case variants:

- repo-refactor audit;
- PR / design-fork conceptual diff;
- architecture-risk audit;
- agent-output adjudication;
- research-paper assimilation audit;
- edge / failure-mode detection;
- benchmark-result authority audit;
- model-output A/B/C comparison over a user's own repo or corpus.

Roadmap mapping:

- `V68`: knows the target repo/corpus, arc lineage, schema surfaces, branch posture,
  evidence locations, and product-audit lineage.
- `V69`: admits the prompt, repo/corpus, model outputs, resident role assignments, and
  internally generated candidate artifact types.
- `V70`: produces ODEU comparison, evidence/tool applicability, authority-risk,
  weak-point, and edge-seam judgments.
- `V71`: keeps human ratification, model-role settlement, and synthesis acceptance
  explicit.
- `V72`: turns recommendations into bounded implementation-safe next slices without
  confusing them with commit/release authority.
- `V73`: records outcome, model/corpus performance, prompt refinements, and recurring
  weakness patterns.
- `V74`: becomes the operator-facing product workbench.
- `V75`: optionally widens to governed multi-model / multi-agent reruns and refinement
  loops.

The support note
`docs/support/arc_series_mapping/DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md`
records the fuller product brainstorm. Its useful role in this roadmap is to keep the
commercial face visible while preserving the rule that product projection cannot mint
authority.

## Current Layered Spine

| Layer | Primary families | Closed capability | Remaining pressure |
|---|---|---|---|
| Pre-family and hygiene baseline | early `vNext` lineage, `V31` | governance, closeout hygiene, evidence explorer, proposer/repo-root discipline, early runtime/read-surface foundations | not the current bottleneck, but must be represented in cartography |
| Semantic and documentation authority | `V32`, `V40`, `V47`, `V49`, `V66` | semantic compiler, architecture IR, ANM / `D@1`, semantic forms, native documentation practice | semantic authority exists for documents, not yet for live operator-turn admission |
| Harness, trust, orchestration | `V33`, `V34`, `V35`, `V48`, `V65` | taskpacks, signing/verification, orchestration, worker boundaries, delegated export/reconciliation | adversarial review and arbiter settlement are not yet first-class adoption phases |
| Reasoning, evidence, benchmarks | `V39`, `V41`, `V42`, `V44`, `V46`, `V51`, `V52` | practical analysis, ARC-specific challenge stack, structural reasoning assessment, benchmarking, simulation, paper semantics | evidence can evaluate claims but does not by itself adopt harness changes |
| Repo self-description and history | `V45`, `V50`, `V53`, `V54` | schema/entity/symbol/test/optimization description, symbol audit, edge ledger, history semantics | no current whole-series cartography over all families and branches |
| Constitutional and resident-agent runtime | `V55` through `V65` | coherence, live interaction, local effect, restoration, continuity, continuation, communication, connectors, remote operator, writable surface, delegated reconciliation | local action/write/delegation are still below commit, release, and recursive adoption authority |
| Human and product surfaces | `V36`, `V51`, `V52`, `V63`, `V67` | Morphic UX substrate, ODEU simulation, paper workbench, remote operator surface, ergonomic adjudication | operator projection for recursive candidates is not yet a single governed surface |

Negative laws that remain controlling:

- transcript is not authority;
- communication is not permission;
- continuity is not standing authority;
- local write ability is not commit, merge, PR, or release authority;
- worker output is not native truth without reconciliation;
- benchmark output is not self-improvement proof without experiment and adoption law;
- planning support is not lock-level authorization;
- tool success is not scope expansion beyond the tool's declared surface;
- self-evidencing workflow emergence is not self-validation.

## Future Family Map

The integrated core missing set remains `V68` through `V75`, with operational seams
from the high drafts absorbed as required slices or review questions. Only `V68` is
the immediate drafting target. `V69` through `V75` are a sequenced lifecycle
hypothesis that `V68` must cartograph. `V43` is tracked as a connected conditional
branch, not silently dropped.

| Proposed family | Integrated role | Required absorbed seams | Primary output targets | Boundary |
|---|---|---|---|---|
| `V68` | whole-series cartography, namespace disambiguation, closure registry, branch posture, support lineage, evidence indexing, tool-applicability, coordinate posture | selector/family/slice/implementation/closeout/evidence namespace joins; V45-C compatibility lesson; current V67-C evidence spine; conceptual-diff lineage; GPTPro frontier review | `repo_arc_series_cartography@1`, `repo_arc_namespace_map@1`, `repo_family_closure_register@1`, `repo_branch_posture_register@1`, `repo_support_lineage_register@1`, `repo_evidence_surface_index@1`, `repo_arc_mapping_tool_applicability_report@1`, `repo_recursive_coordinate_emission_plan@1` | descriptive support/planning graph only, no scheduling or runtime authority |
| `V69` | recursive candidate intake plus semantic ingress / operator binding / O/E/D/U mapping | external candidates, internally generated conceptual candidates, raw turn-to-typed-operator boundary, source provenance | `recursive_candidate_advancement_record@1`, `operator_ingress_binding@1`, `recursive_odeu_mapping@1`, `candidate_source_provenance_packet@1` | admit and map only, no adoption, execution, commit, or hidden operator invention |
| `V70` | evidence, quality, tool-result, and adversarial-review classification | tool applicability judgments, structural reasoning/benchmark evidence, constitutional advisory posture, independent critic records, arbiter-input framing | `recursive_integration_classification@1`, `recursive_quality_threshold_report@1`, `tool_result_applicability_judgment@1`, `adversarial_review_packet@1`, `integration_risk_register@1` | evaluates and classifies, but cannot ratify or release |
| `V71` | ratification, amendment scope, and human-internal authority kernel | human role as internal loop component, support-vs-lock boundary, warning-only-vs-gating distinction, settlement over review conflicts | `recursive_ratification_request@1`, `recursive_ratification_record@1`, `amendment_scope_boundary@1`, `human_role_authority_profile@1`, `arbiter_settlement_record@1` | decision/ratification only, no implementation by itself |
| `V72` | contained trial, integration, rollback, and commit/release authority boundary | local write vs accepted diff vs commit intent vs PR update vs merge vs released truth; rollback; V64/V65 consumption | `recursive_integration_trial_plan@1`, `recursive_integration_execution_record@1`, `rollback_readiness_record@1`, `commit_release_authority_record@1`, `integration_containment_report@1` | bounded integration and release-posture control only, no autonomous constitutional amendment |
| `V73` | longitudinal outcome review, self-improvement ledger, tool fitness drift, and operator-cognition outcome signals | baseline/intervention/evaluation/regression/adoption posture; self-evidencing workflow-type emergence; stale tool review | `recursive_outcome_review@1`, `self_improvement_ledger@1`, `promotion_demotion_decision@1`, `tool_fitness_drift_register@1`, `operator_cognition_outcome_signal@1` | review and recommendation only, no self-approval |
| `V74` | self-improvement operator studio and typed adjudication product projection | human-legible candidate case view, conceptual-diff result projection, model-output A/B comparison, ratification workbench, exception visibility | `self_improvement_operator_case_view@1`, `typed_adjudication_case_view@1`, `ratification_workbench_projection@1`, `decision_visibility_contract@1` | projection of typed authority only, no authority minted by UI |
| `V75` | governed dispatch, execute, multi-worker widening, and optional multi-model rerun orchestration | multi-worker topology after gates exist, dispatch/execute leases, reconciliation, broader adversarial review execution, prompt/evaluation/refinement loops if selected | `governed_dispatch_packet@1`, `execute_authority_lease@1`, `multi_worker_orchestration_topology@1`, `model_comparison_rerun_packet@1`, `dispatch_reconciliation_report@1` | later execution widening only after candidate, evaluation, ratification, integration, review, and projection gates exist |

### Connected Conditional Branch

`V43` governed external contest participation remains real and unreleased.

Integrated posture:

- `V43` is not part of the core recursive self-improvement lifecycle unless the next
  planning horizon selects external-world intake as immediate pressure;
- `V68` must track it as a connected branch with clear branch posture;
- if selected, `V43` should compile host/world law before strategy or execution;
- `V42` remains ARC-specific and cannot be silently generalized to all contest worlds.

## Recommended Order

Default order:

1. `V68`: establish current whole-series cartography and evidence joins.
2. `V69`: admit both external and internally generated candidates, including typed
   operator ingress from human turns.
3. `V70`: classify evidence, tool results, risk, and adversarial review outputs.
4. `V71`: ratify or reject with explicit human-internal authority.
5. `V72`: run contained integration, rollback, and commit/release posture.
6. `V73`: review outcomes, regressions, tool drift, and operator-cognition signals.
7. `V74`: project candidate decisions and exceptions to the human operator.
8. `V75`: widen dispatch, execute, and multi-worker capability only after the gates are
   in place.

`V43` can be selected after `V68` if external-world intake becomes the selected pressure,
but it should not be used to bypass `V69` through `V73`.

## Proof Sketch

Sufficiency:

- `V68` tells the repo where a claim, artifact, family, branch, and evidence surface
  sits.
- `V69` admits a candidate, including candidates generated by prior ADEU reasoning and
  human operator cognition.
- `V70` evaluates evidence and tool applicability without confusing local success with
  authority.
- `V71` makes ratification and amendment scope explicit.
- `V72` contains trial/integration and separates local writes from released truth.
- `V73` records whether the change helped, harmed, drifted, or produced new workflow
  types needing admission.
- `V74` makes the decision legible to the operator.
- `V75` only then widens execution and multi-worker capacity.

Necessity:

- Without `V68`, current evidence remains distributed across selectors, locks,
  closeouts, fixtures, tests, and support docs.
- Without `V69`, internally generated conceptual artifacts like the ODEU conceptual
  diff have no native candidate-admission path.
- Without `V70`, advisory checks, test passes, schema creation, benchmark deltas, and
  critic outputs can be over-read.
- Without `V71`, human involvement remains conversational rather than typed authority.
- Without `V72`, local mutation and worker reconciliation can be mistaken for commit,
  merge, or release truth.
- Without `V73`, self-evidencing workflow-type emergence remains a chat insight rather
  than an outcome signal.
- Without `V74`, the operator sees scattered artifacts rather than one governed
  decision case.
- Without `V75`, the loop remains manually orchestrated and cannot safely widen action.

Minimality at this support horizon:

- the high-draft seams are not discarded; they are absorbed where they protect a
  distinct boundary;
- semantic ingress belongs in `V69`;
- commit / merge / release posture belongs in `V72` unless review proves it needs a
  separate family;
- adversarial review and arbiter settlement belong across `V70` / `V71`, with possible
  execution widening under `V75`;
- `V43` is tracked as connected conditional, because its necessity depends on selected
  external-world pressure.

## Review Questions Before Arc Drafting

1. Should `commit_release_authority_record@1` be a `V72` slice, or does commit/merge/
   release authority need a separate family?
2. Should adversarial review be a `V70` evidence slice, a `V71` settlement slice, or a
   separate family before `V75`?
3. Can `V69` safely own both recursive candidate intake and semantic operator ingress,
   or should operator ingress become its own family?
4. When does `V43` become prerequisite rather than connected deferred branch?
5. Should `odeu_conceptual_diff_report@1` stay a support schema, or enter `V69` as a
   candidate for released schema work?
6. Is `typed_adjudication_case_view@1` only a `V74` product projection, or should the
   audit artifact bundle be drafted earlier as part of `V70` evidence classification?

## Integrated Review Answers

GPTPro's review answers are accepted as support-layer shaping guidance:

1. Keep commit / release authority in `V72` for now, but make it a named high-risk
   sub-slice rather than a buried field. Split it only if `V72` cannot keep
   contained integration / rollback distinct from merge / release truth.
2. Split adversarial review across `V70` and `V71`: `V70` owns adversarial review as
   evidence / classification input; `V71` owns settlement / ratification over
   conflicting reviews. Execution widening remains `V75`.
3. Let `V69` own operator ingress only as typed admission / binding of a human turn
   into an O/E/D/U candidate record. Split it if it becomes a live turn compiler,
   standing operator profile, or runtime permission surface.
4. Keep `V43` connected-conditional until external-world contest / host participation
   becomes selected planning pressure.
5. Keep `odeu_conceptual_diff_report@1` support-layer during `V68`; `V69` may later
   admit it as a candidate for released schema work.
6. Split typed adjudication: machine-readable audit / report artifacts belong earlier,
   mainly `V70`; the operator-facing case view belongs in `V74`.

## Machine-Checkable Seed

```json
{
  "schema": "adeu_arc_series_multi_layer_mapping@2",
  "status": "support_synthesis_integrated_review_draft",
  "authority_layer": "support",
  "source_document": "docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md",
  "support_lineage_dir": "docs/support/arc_series_mapping",
  "integrated_sources": [
    "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v0.md",
    "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_MULTILAYER_MAPPING_v0_ALT.md",
    "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v1.md",
    "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_MULTILAYER_MAPPING_v1_ALT.md",
    "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_ODEU_CONCEPTUAL_DIFF_v0.md",
    "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_ODEU_CONCEPTUAL_DIFF_v0.report.json",
    "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_REASONING_RECURSION_LOOP_v0.md",
    "docs/support/arc_series_mapping/DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md",
    "docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_MAPPING_V68_PLANNING_v0.md",
    "docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_CARTOGRAPHY_ABC_SPECS_v0.md"
  ],
  "current_repo_frontier": {
    "review_snapshot_commit": "6eb7a9c9538de672d9102714a0fc6e3b9b050afd",
    "latest_locked_continuation_at_review": "vNEXT_PLUS187",
    "latest_closed_family_slice_at_review": "V67-C",
    "v67_family_posture_at_review": "closed_on_main",
    "latest_next_arc_selector_at_review": "DRAFT_NEXT_ARC_OPTIONS_v52.md",
    "v53_present_at_review": false,
    "next_planning_obligation": "select_and_draft_v68_outside_closed_v67"
  },
  "observed_recursive_signal": {
    "name": "self_evidencing_workflow_type_emergence",
    "claim": "the workflow produced evidence that future instances of the same workflow class need typed admission, evaluation, and outcome review",
    "guardrail": "self_evidencing_is_not_self_validating"
  },
  "core_missing_family_order": [
    "V68_arc_cartography_namespace_evidence_and_tool_applicability",
    "V69_recursive_candidate_intake_semantic_ingress_and_odeu_mapping",
    "V70_evidence_quality_tool_result_and_adversarial_review_classification",
    "V71_ratification_amendment_scope_and_human_internal_authority",
    "V72_contained_integration_rollback_and_commit_release_authority",
    "V73_outcome_review_self_improvement_ledger_and_tool_fitness_drift",
    "V74_self_improvement_operator_projection",
    "V75_governed_dispatch_execute_and_multi_worker_widening"
  ],
  "immediate_drafting_target": "V68_only",
  "later_lifecycle_posture": "V69_through_V75_are_sequenced_hypothesis_not_pre_authorized_locks",
  "v68_starter_surface_candidates": [
    "repo_arc_series_cartography@1",
    "repo_arc_namespace_map@1",
    "repo_family_closure_register@1",
    "repo_branch_posture_register@1",
    "repo_support_lineage_register@1",
    "repo_evidence_surface_index@1",
    "repo_arc_mapping_tool_applicability_report@1",
    "repo_recursive_coordinate_emission_plan@1"
  ],
  "connected_conditional_branches": [
    {
      "family": "V43",
      "theme": "general_governed_external_contest_participation",
      "posture": "connected_conditional_branch",
      "selection_condition": "external_world_intake_becomes_immediate_planning_pressure"
    }
  ],
  "product_projection": {
    "name_candidates": [
      "ADEU Eval Forge",
      "ODEU Model Comparator",
      "ADEU Audit Artifact",
      "Typed Adjudication Workbench"
    ],
    "posture": "v74_facing_projection_not_authority_source",
    "core_claim": "typed_model_output_and_artifact_adjudication_on_user_substrate_instead_of_vibe_analysis",
    "depends_on": [
      "V68",
      "V69",
      "V70",
      "V71",
      "V72",
      "V73"
    ],
    "candidate_artifacts": [
      "odeu_conceptual_analysis@1",
      "model_output_comparison_case@1",
      "tool_applicability_report@1",
      "authority_boundary_map@1",
      "edge_seam_register@1",
      "weak_point_ledger@1",
      "next_slice_recommendation@1",
      "synthesis_candidate@1"
    ]
  },
  "review_questions": [
    "commit_release_family_or_v72_slice",
    "adversarial_review_family_or_v70_v71_slice",
    "operator_ingress_inside_v69_or_separate_family",
    "v43_prerequisite_threshold",
    "odeu_conceptual_diff_candidate_admission",
    "typed_adjudication_case_view_v74_projection_or_v70_artifact_bundle"
  ],
  "proof_status": "support_layer_proof_sketch_not_formal_proof"
}
```
