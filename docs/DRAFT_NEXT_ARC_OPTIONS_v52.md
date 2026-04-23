# Draft Next Arc Options v52

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v51.md`, now that `V66`
is closed on `main`, and after support-layer review of:

- `docs/support/DRAFT_ERGONOMIC_INSTANTIATION_ADJUDICATOR_v0.md`
- `docs/support/DRAFT_ERGONOMIC_INSTANTIATION_ADJUDICATOR_2ND_PASS_v0.md`
- `docs/support/REVIEW_GPTPRO_ERGONOMIC_INSTANTIATION_ADJUDICATOR_2ND_PASS_v0.md`

Authority layer: planning.

This draft does not supersede the canonical planning records for the already closed
runtime, documentation, and UX governance branches. It records the next candidate
family after `V66`:

how should ADEU add a bounded ergonomic instantiation adjudication layer on top of
the already released Morphic UX governance stack, so a stable constitutional surface
object can be lawfully instantiated under a specific human + device + task envelope,
without reopening the closed UX governance substrate, silently minting new surface
semantics, inferring layout law from screenshots, or collapsing heuristics into fake
measurement precision?

This is a planning document only. It is not a lock doc and does not authorize
runtime behavior, schema release, adjudication output, or implementation by itself.

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

- `V66` is closed on `main`;
- the repo already ships the main Morphic UX governance substrate on `main`:
  - `ux_domain_packet@1`
  - `ux_morph_ir@1`
  - `v36a_first_family_approved_profile_table@1`
  - `v36a_same_context_reachability_glossary@1`
  - `ux_surface_projection@1`
  - `ux_interaction_contract@1`
  - `ux_morph_diagnostics@1`
  - `ux_conformance_report@1`
  - `ux_surface_compiler_variant_manifest@1`
- the main released implementation lives in:
  - `packages/adeu_core_ir/src/adeu_core_ir/ux_governance.py`
  - `packages/adeu_core_ir/schema/`
  - `spec/`
  - `apps/api/fixtures/ux_governance/vnext_plus61` through
    `apps/api/fixtures/ux_governance/vnext_plus65`
- the repo already has the current Morphic UX support doctrine on `main`,
  including the existing UX-governance planning / lock lineage and the
  support-layer ergonomic adjudication notes listed above.

## Gap

The repo no longer lacks the constitutional Morphic UX object layer.

The current stack can already say:

- what the bounded surface family is;
- which regions, lanes, action clusters, and interaction invariants are lawful;
- how one approved morph family may project into concrete surface variants; and
- how the realized surface can be diagnosed and checked for conformance.

What the repo still lacks is the missing middle layer between:

- constitutional sameness law; and
- case-specific concrete instantiation.

In particular, the repo still lacks:

- one explicit ergonomic rule authority stack, so constitutional invariants,
  repo-local ergonomic deontics, adopted external floors, platform presets, user
  preferences, and heuristic utility are not silently collapsed;
- one finite ergonomic component registry and per-surface visibility contract, so
  candidate projections are evaluated against fixed ergonomic classes rather than
  ad hoc widget vocabulary;
- one bounded candidate projection artifact family, distinct from the existing
  approved morph-profile table, so ergonomic adjudication evaluates only finite,
  repo-native candidate shapes;
- one case-envelope and measurement-admissibility model, so CSS geometry,
  physical-size estimates, visual-angle estimates, declared user preferences, and
  runtime conformance evidence are not treated as interchangeable;
- one adjudication request/result family, so blocked configurations, preferred
  projections, ambiguity markers, and measurement obligations are explicit rather
  than implicit in design prose or screenshots.

So the repo still lacks the next UX-governance fill that would let it say:

- these are the only ergonomic rules in play here, with explicit provenance and
  override posture;
- these are the only ergonomic classes and candidate projections that may be
  evaluated here;
- these measurements are admissible for CSS geometry only, those for physical or
  visual-angle reasoning, and these others are not admissible at all; and
- this exact ergonomic adjudication result is replayable, fail-closed, and
  separate from aesthetic free variation.

## Relationship To Existing UX Governance

The current UX governance stack asks:

- what is the stable Morphic UX object?
- which morphs and projections are lawful?
- how should realized surfaces be diagnosed and checked?

This new family asks:

- how should a stable lawful surface become concretely instantiated under a
  bounded ergonomic case envelope?
- how should that adjudication stay artifact-bound, provenance-bearing,
  finite-registry-driven, and epistemically strict?
- how should ergonomic policy consume existing UX governance artifacts without
  minting new regions, lanes, action clusters, authority postures, or morph axes?

So this new family may constrain:

- ergonomic rule precedence and override posture;
- ergonomic component classes and visibility obligations;
- admissible candidate projection profiles;
- measurement provenance and admissibility;
- case-bound adjudication request/result posture.

But it may not mint:

- new `ux_domain_packet@1` semantics;
- new `ux_morph_ir@1` morph axes by default;
- new `ux_surface_projection@1` regions, lanes, or action clusters by default;
- new `ux_interaction_contract@1` trust-boundary or evidence-before-commit law;
- generic layout-solver sovereignty;
- screenshot-first “vibe check” authority;
- clinical or biometric user modeling; or
- runtime personalization engines by default.

## Recommended Family

- family name: `V67`
- family theme: ergonomic instantiation adjudication
- lineage role:
  - `packages/adeu_core_ir` remains the schema / model home;
  - existing UX governance artifacts remain the consumed constitutional basis;
  - new ergonomic artifacts remain a sibling extension to the current
    `ux_governance` lane, not a replacement for it.
- family role:
  - one schema-and-validator starter for ergonomic rule authority, component
    registry, candidate profiles, case envelope, and adjudication request/result;
  - later one bounded adjudication engine over a finite candidate set;
  - later one advisory runtime-measurement / conformance hardening seam.

## Recommended Next Slice

- family remains: `V67`
- `V67-A` starter language and validator backbone is now shipped on `main`
- next concrete slice: `V67-B`
- recommended selector outcome:
  - keep the current UX governance substrate closed on `main`
  - keep the shipped `V67-A` artifact family stable on `main`
  - select `V67-B` as the next default candidate
  - keep `V67-B` bounded to finite-candidate adjudication only.

`V67-B` should:

- consume the shipped `V67-A` artifact language intact:
  - `ux_ergonomic_rule_authority_stack@1`
  - `ux_component_ergonomic_registry@1`
  - `ux_component_visibility_contract@1`
  - `ux_ergonomic_candidate_projection_profile_table@1`
  - `ux_ergonomic_case_envelope@1`
  - `ux_ergonomic_adjudication_request@1`
  - `ux_ergonomic_adjudication_result@1`
- consume the released UX governance basis intact:
  - `ux_domain_packet@1`
  - `ux_morph_ir@1`
  - `v36a_first_family_approved_profile_table@1`
  - `v36a_same_context_reachability_glossary@1`
  - `ux_surface_projection@1`
  - `ux_interaction_contract@1`
  - `ux_surface_compiler_variant_manifest@1`
- compute only over finite repo-native candidate rows already declared in the
  shipped candidate table
- keep artifact validity in `report_status` and ergonomic case outcome in
  `overall_judgment`
- emit only bounded blocked / feasible / ambiguity / measurement-obligation
  result posture over the shipped result schema
- stay out of:
  - generic layout solving
  - runtime adaptive morph switching
  - screenshot-first authority
  - scalar ergonomic scores
  - new runtime bridge artifacts
  - mutation of released UX diagnostics / conformance law.

## Suggested `V67` Path Ladder

- `V67-A`: schema-and-validator backbone only
  - ship the seven ergonomic artifacts above
  - ship canonicalization helpers, schema export, reference fixtures, reject
    fixtures, and deterministic validators
  - split local payload validation from cross-artifact bundle validation
  - keep `schema` as the repo-native artifact field rather than draft-only
    `schema_id`
  - artifact-inspector-family anchored only
- `V67-B`: bounded adjudication engine
  - compute hard-blocks, feasible candidates, preference tiers, ambiguity markers,
    and measurement obligations over the finite candidate set
  - keep artifact validity in `report_status` and ergonomic case outcome in
    `overall_judgment`
  - no general layout solver
- `V67-C`: advisory runtime / conformance hardening
  - bridge adjudication outputs to typed realized-measurement evidence and one
    non-entitling advisory bridge report
  - still no sovereign runtime personalization engine by default.

## Why `V67` And Not Another ANM Or Standalone-App Branch

This branch is not:

- another ANM lane;
- another standalone dual-partner shell lane; or
- a reopening of the closed UX governance substrate.

It is the next missing sibling extension of Morphic UX governance:

- constitutional sameness law already exists;
- projection and conformance law already exist;
- ergonomic instantiation adjudication does not.

Validation note for this planning-only family draft:

- use `git diff --check` for the doc edits
- do not treat this planning draft as a starter-bundle lock pack by itself
- even with the sharpened selector outcome, `V67-B` remains planning-only until a
  starter lock or implementation lock is drafted.
