# Draft Next Arc Options v53

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v52.md`, now that `V67`
is closed on `main`, and after support-layer review of:

- `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md`
- `docs/support/arc_series_mapping/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v0.md`
- `docs/support/arc_series_mapping/DRAFT_ARC_SERIES_MULTILAYER_MAPPING_v0_ALT.md`
- `docs/support/arc_series_mapping/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v1.md`
- `docs/support/arc_series_mapping/DRAFT_ARC_SERIES_MULTILAYER_MAPPING_v1_ALT.md`
- `docs/support/arc_series_mapping/DRAFT_ARC_SERIES_ODEU_CONCEPTUAL_DIFF_v0.md`
- `docs/support/arc_series_mapping/DRAFT_ARC_SERIES_ODEU_CONCEPTUAL_DIFF_v0.report.json`
- `docs/support/arc_series_mapping/DRAFT_ARC_SERIES_REASONING_RECURSION_LOOP_v0.md`
- `docs/support/arc_series_mapping/DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_MAPPING_V68_PLANNING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_CARTOGRAPHY_ABC_SPECS_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68C_IMPLEMENTATION_MAPPING_v0.md`

Authority layer: planning.

This draft records the next candidate family after `V67`:

how should ADEU create a whole-series ARC cartography layer that can describe the
already shipped family/slice/vNext/schema/artifact lineage, branch posture, closure
state, source-status posture, evidence surface indexing, support lineage, and
tool-applicability limits, without converting that map into scheduling authority,
ratification authority, implementation authority, product authority, or recursive
self-improvement adoption by itself?

This is a planning document only. It is not a lock doc and does not authorize
runtime behavior, schema release, implementation, candidate admission, self-
improvement adoption, commit, merge, release, or product surface work by itself.
The `V68-A/B/C` implementation specs cited by this draft are support inputs to
future active-slice locks, not admitted implementation authority by themselves.

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

## Feedback Integration Posture

The follow-on GPTPro feedback is now captured as:

- `docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_MAPPING_V68_PLANNING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_CARTOGRAPHY_ABC_SPECS_v0.md`

The review is integrated as support-layer shaping evidence. Its controlling framing
for this planning draft is:

- `V68` is the only immediate drafting target;
- `V69` through `V75` are a sequenced lifecycle hypothesis that `V68` must
  cartograph, not pre-authorized follow-on locks.

The review also confirms that source status should be first-class. The cartography
source set should therefore support at least these source-status postures:

- `integrated_shaping_source`
- `available_but_not_integrated`
- `review_pending_input`
- `rejected_or_superseded_source`

That boundary is itself evidence for `V68`: a whole-series map that cannot say which
review inputs were present, missing, pending, admitted, or rejected is not robust
enough for later recursive candidate intake.

## Current Repo Frontier

Current frontier checked by GPTPro against repo zip snapshot
`6eb7a9c9538de672d9102714a0fc6e3b9b050afd`:

- latest locked continuation: `vNEXT_PLUS187`
- latest closed family slice: `V67-C`
- `V67` family posture: closed on `main`
- latest next-arc selector at reviewed snapshot: `DRAFT_NEXT_ARC_OPTIONS_v52.md`
- no `DRAFT_NEXT_ARC_OPTIONS_v53.md` was present in that reviewed snapshot
- next planning obligation: select / draft `V68` outside closed `V67`

This document is the `v53` planning response to that frontier.

## Baseline

- `V67` is closed on `main`.
- The repo already has shipped families across semantic compilation, architecture IR,
  orchestration, benchmarking, repo description, history semantics, constitutional
  coherence, resident-agent membranes, writable surfaces, delegated reconciliation,
  ANM-native documentation practice, and ergonomic adjudication.
- The repo already has partial descriptive machinery:
  - `repo_schema_family_registry@1`
  - `repo_entity_catalog@1`
  - `repo_arc_dependency_register@1` / `repo_arc_dependency_register@2`
  - `repo_symbol_catalog@1`
  - `repo_test_intent_matrix@1`
  - `repo_optimization_register@1`
  - `repo_descriptive_normative_binding_frame@1`
- The repo already has closeout and planning surfaces:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v*.md`
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS*.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS*.md`
  - `docs/ASSESSMENT_vNEXT_PLUS*_EDGES.md`
  - closeout artifacts under `artifacts/stop_gate/` and
    `artifacts/agent_harness/`.
- The support map in `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md` identifies
  `V68` as the first needed family in the next recursive lifecycle.

## Gap

The repo does not yet have one current whole-series cartography object.

The absence is not just a documentation inconvenience. It creates specific failure
modes:

- `V` family names, `vNext+` implementation / closeout arc numbers, fixture directory names, schema
  family names, and branch-local execution targets can be conflated.
- Closed family state can be inferred from prose instead of represented as a typed
  closure register.
- Deferred branches such as `V43` can disappear from current planning view because
  they are not in the selected immediate family ladder.
- Tool output can be overread when the tool was actually namespace-limited, as seen
  in the prior `arc-closeout-check ARC=67` applicability lesson.
- Internally generated workflow types, such as the conceptual-diff report created
  during the support pass, have no map position before `V69` can admit them.
- External or follow-on review inputs can be conversationally referenced without a
  typed source-status posture.

So the repo lacks the cartographic layer that would let it say:

- this is the current family/slice/arc namespace map;
- this family is closed, open, deferred, connected conditional, superseded, or
  not selected yet;
- this source was integrated, available-but-not-integrated, pending, rejected, or
  superseded;
- this evidence surface supports only this claim horizon;
- this tool was applicable to this namespace and not that namespace; and
- this future seam is tracked without being authorized.

`V68` must explicitly distinguish at least these namespace discriminants:

- `selector_version`
- `family_id`
- `family_slice_id`
- `implementation_arc_id`
- `closeout_arc_id`
- `evidence_arc_id`
- `branch_local_execution_target`
- `planning_doc_ref`
- `lock_doc_ref`
- `decision_doc_ref`
- `assessment_doc_ref`
- `architecture_doc_ref`
- `support_doc_ref`
- `schema_id`
- `fixture_dir_ref`
- `evidence_input_ref`
- `stop_gate_ref`

Source kind and authority layer are fields on source rows, not namespace kinds.

## Relationship To Existing Repo Description Families

`V45` already describes repo entities, schema families, dependencies, symbols, tests,
optimization surfaces, and descriptive/normative binding. `V68` should consume that
lineage rather than replace it.

`V68` asks a different question:

- how do all ARC-family, implementation-arc, closeout-arc, support-doc, evidence,
  branch, and future-seam records fit into one current map?

So `V68` may constrain:

- family/slice/arc namespace disambiguation;
- family closure and branch posture;
- source-set and review-input posture;
- evidence-surface applicability;
- tool-result applicability;
- recursive-coordinate emission planning.

But it may not mint:

- implementation scheduling;
- recursive candidate admission;
- quality classification;
- ratification;
- integration / rollback authority;
- outcome review authority;
- operator UI authority;
- dispatch / execution authority;
- product-surface authority.

Those belong to later families if selected.

## Recommended Family

- family name: `V68`
- family theme: ARC series cartography, namespace disambiguation, closure registry,
  branch posture, support lineage, evidence surface indexing, and tool-applicability
  mapping
- lineage role:
  - `packages/adeu_repo_description` remains the likely schema / model / validator
    home for repo-scale cartography artifacts;
  - current planning and closeout docs remain the authority sources for their own
    layers;
  - support-layer ARC mapping docs remain shaping evidence only.
- family role:
  - one starter schema-and-validator slice for the cartography object family;
  - later deterministic derivation and gap-scanning over current repo artifacts;
  - later tool-applicability and recursive-coordinate emission planning.

## Recommended Next Slice

- family: `V68`
- next concrete slice: `V68-A`
- recommended selector outcome:
  - select `V68-A` as the next default candidate
  - keep `V68-A` bounded to schema/model/validator/reference-fixture work for ARC
    series cartography
  - do not use `V68-A` to adopt conceptual-diff schemas, admit recursive candidates,
    adjudicate model outputs, ratify future seams, or build the product workbench.

## Suggested `V68` Path Ladder

- `V68-A`: schema-and-validator cartography backbone
  - ship the starter ARC cartography record shapes:
    - arc namespace map
    - family closure register
    - branch posture register
    - support lineage register
    - evidence surface index
    - tool applicability report
    - coordinate posture / coordinate emission plan
  - ship source-status, namespace, closure, branch, evidence, and tool-applicability
    enums
  - ship deterministic validators and reference/reject fixtures
  - keep the first map descriptive and non-authorizing
- `V68-B`: deterministic repo-derived cartography and gap scan
  - derive current family/slice/implementation-arc/closeout-arc rows from docs and
    closeout artifacts
  - detect namespace ambiguity, missing closure rows, missing branch posture, and
    stale source references
  - preserve human review for ambiguous cases
- `V68-C`: tool-applicability and recursive-coordinate emission plan
  - record which existing repo tools are applicable to which map claims
  - emit a bounded coordinate plan that later families can consume
  - keep recursive candidate intake deferred to `V69`.

The `V68-A`, `V68-B`, and `V68-C` implementation mapping notes are drafted early for
joint GPTPro review. They are support-only until each slice receives its own
canonical starter bundle at activation time.

## Why `V68` And Not Immediate Candidate Intake Or Product Work

The product wedge and recursive candidate lifecycle are real, but they depend on a
current map. Without the map, later families would need to rediscover:

- what family/slice namespace is in play;
- which source documents were admitted;
- which branches are deferred or conditional;
- what evidence already exists;
- which tools were tried and where their outputs apply.

So `V68` is not glamorous product work and not the full self-improvement loop. It is
the missing cartographic substrate that prevents later recursive moves from floating.

Validation note for this planning-only family draft:

- use `make arc-start-check ARC=188` for the first docs-only starter bundle;
- use `make check` only when Python source, tests, Makefile, CI, or lint scripts
  change;
- this planning draft is not closeout evidence.
