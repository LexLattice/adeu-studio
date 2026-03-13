# Assessment vNext+61 Edges (Pre-Lock)

This document records pre-lock edge assessment for `vNext+61` (`V36-A` typed UX-governance
baseline).

Status: pre-lock assessment (March 14, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS61_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "authoritative_scope": "v61_pre_lock_edge_assessment",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning only. Post-closeout disposition must replace this scaffold after v61 closes."
}
```

## Scope

- In scope: thin `V36-A` typed UX-governance substrate over the closed `V35` authority
  baseline; canonical `ux_domain_packet@1` and `ux_morph_ir@1` schemas; one accepted
  `artifact_inspector_advisory_workbench` reference instance; frozen approved profile
  table and same-context reachability glossary; deterministic serialization/hash binding;
  and closeout evidence/guard coverage.
- Out of scope: `V36-B` projection/interaction, `V36-C` rendered reference surface,
  `V36-D` diagnostics engine, `V36-E` compiler export, route rewrites, generic
  design-system release, stop-gate schema-family fork, metric-key expansion, and the
  separate `O1`/`O2`/`O3` closeout-hardening bundle.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS60.md`
- `docs/seed arc v10.md`
- `apps/web/src/app/`
- `apps/api/scripts/lint_arc_bundle.py`
- `apps/api/tests/test_lint_arc_bundle.py`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`

## Pre-Lock Edge Set (v61 Start)

1. No typed UX-governance schema substrate exists on `main`: `open`.
   - no released `ux_domain_packet@1` or `ux_morph_ir@1` canonical artifact family exists
     yet.
2. No accepted bounded reference instance exists on `main`: `open`.
   - the first-family `artifact_inspector_advisory_workbench` example currently exists as
     seed prose only, not as an accepted canonical instance.
3. Reference-instance binding coherence risk: `open`.
   - even once two reference-instance files exist, the lock still needs a fail-closed
     guarantee that they describe the same bounded family/profile identity rather than two
     unrelated valid files.
4. O/E/D/U split drift risk: `open`.
   - without explicit schemas and tests, ontology/epistemics/deontics/utility separation
     could collapse back into prompt prose or ad hoc fields.
5. Approved-profile-table absence risk: `open`.
   - without an enumerated first-family profile table, individually legal axis values
     could be recombined into ungoverned morph variants.
6. Same-context reachability ambiguity risk: `open`.
   - the first-family evidence-before-commit rule now has a glossary in planning, but no
     canonical artifact or guard surface exists yet on `main`.
   - the glossary must stay substrate-level in v61 and not quietly smuggle `V36-B`
     projection/widget semantics into the substrate.
7. Authority-minting by surface artifact wording risk: `open`.
   - the family rule is frozen in planning, but no schema/reference-instance guard yet
     proves that the new artifacts cannot silently mint authority or weaken `V35` gates.
8. Greenfield placement/accretion risk: `open`.
   - no dedicated artifact layer exists yet; without explicit placement discipline,
     `V36-A` could scatter new governance logic across page components.
9. Deterministic serialization/hash binding gap: `open`.
   - no released hash-bound schema/reference-instance outputs exist yet for the first
     family.
10. Evidence integration gap: `open`.
   - no canonical `v36a_ux_domain_morph_ir_evidence@1` closeout block exists on `main`.
11. Guard coverage gap for glossary/profile/reference-instance drift: `open`.
    - no tests currently prove fail-closed behavior on missing O/E/D/U splits, missing
      accepted instances, profile-table drift, or glossary drift.
12. Existing route rewrite leakage risk: `open`.
    - current `apps/web` terrain could be used as justification for silent retrofits
      unless the first release stays bounded to a new surface/artifact lane only.
13. Stop-gate continuity risk: `open`.
    - v61 must preserve `stop_gate_metrics@1` and exact metric-key equality with v60.

## Required Edge Closures Before Closeout

1. Canonical `ux_domain_packet@1` and `ux_morph_ir@1` schemas exist on `main`.
2. One accepted `artifact_inspector_advisory_workbench` reference instance exists for both
   schemas and is canonically serializable/hashable.
3. The accepted `ux_domain_packet@1` and `ux_morph_ir@1` reference instances are proven as
   one coherent bound pair through shared reference identity/profile fields.
4. Required O/E/D/U split, invariant/morph split, approved profile table, and
   same-context reachability glossary are all frozen in canonical artifacts.
5. Approved profile table contains exactly two explicit approved profiles and rejects
   out-of-table combinations fail closed.
6. Same-context reachability glossary remains frozen in substrate-level terms only.
7. `V35` authority baseline remains unchanged; the new artifacts may express authority but
   may not mint authority.
8. Canonical `v36a_ux_domain_morph_ir_evidence@1` exists and proves deterministic
   serialization plus preserved stop-gate continuity.
9. Guard coverage fails closed on missing accepted reference instances,
   reference-instance binding drift, profile drift, invalid profile combinations,
   glossary drift, free-form brief-to-code bypass, and authority-minting drift.
10. No rendered route, projection/interaction contract, diagnostics engine, compiler
   export, or broad route rewrite ships in v61.

## Residual Risks (Expected Even If v61 Succeeds)

1. `V36-B` through `V36-E` remain unreleased; v61 defines the substrate only.
2. No rendered-surface conformance lane exists yet; implementation-observable bindings are
   deferred until later paths consume this substrate.
3. Existing `apps/web` routes remain conventional composition surfaces until later `V36`
   paths land.
4. The closeout-hardening bundle remains separate and incomplete by design.

## Recommendation (Pre-Lock)

1. Proceed with `vNext+61` as a narrow `V36-A` substrate-only arc.
2. Require `A1` to land canonical schemas, one accepted reference instance, the approved
   profile table, and the reachability glossary before any later `V36` surface work.
3. Require `A2` to bind the substrate to canonical evidence and fail-closed guards.
4. Keep all rendered-surface, diagnostics, compiler, and route-rewrite work explicitly
   deferred to later locked arcs.
