# Assessment vNext+62 Edges (Pre Lock)

This document records the pre-lock edge assessment for `vNext+62` (`V36-B` surface
projection and interaction contract baseline).

Status: pre-lock assessment (March 14, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS62_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "authoritative_scope": "v62_pre_lock_edge_assessment",
  "required_in_decision": true,
  "notes": "This pre-lock assessment enumerates the blocking edge set for the proposed v62 starter bundle only; post-closeout disposition must replace it if the arc ships."
}
```

## Scope

- In scope: thin `V36-B` typed surface projection and interaction contract baseline over
  the closed `V36-A` substrate; canonical `ux_surface_projection@1` and
  `ux_interaction_contract@1`; one accepted deterministic reference projection/interaction
  pair anchored back to the released accepted `V36-A` reference pair; explicit authority
  provenance; stable implementation-observable bindings; and closeout evidence/guard
  coverage.
- Out of scope: `V36-C` rendered reference surface, `V36-D` diagnostics/conformance,
  `V36-E` compiler export, route rewrites, generic design-system release, stop-gate
  schema-family fork, metric-key expansion, runtime semantics changes, and the separate
  `O1`/`O2`/`O3` closeout-hardening bundle.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md`
- `docs/ASSESSMENT_vNEXT_PLUS61_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md`
- `docs/seed arc v10.md`
- `packages/adeu_core_ir/src/adeu_core_ir/ux_governance.py`
- `packages/adeu_core_ir/src/adeu_core_ir/ux_governance_evidence.py`
- `packages/adeu_core_ir/schema/ux_domain_packet.v1.json`
- `packages/adeu_core_ir/schema/ux_morph_ir.v1.json`
- `apps/api/fixtures/ux_governance/vnext_plus61/`

## Pre-Lock Edge Set (Blocking Until Resolved)

1. No canonical `ux_surface_projection@1` schema exists on `main`.
   - `V36-A` closed the domain/morph substrate only; projection remains unreleased.
2. No canonical `ux_interaction_contract@1` schema exists on `main`.
   - the repo still lacks a typed interaction graph that distinguishes surface events,
     UI transitions, requested runtime effects, and runtime-visible consequences.
3. No accepted deterministic reference projection/interaction pair exists on `main`.
   - v62 needs one bound pair for `artifact_inspector_advisory_workbench`, not schema
     prose alone.
4. No binding from the future `V36-B` reference pair back to the released accepted
   `V36-A` reference pair is frozen on `main`.
   - v62 can still drift into an internally coherent but substrate-detached pair unless
     the binding back to the released `V36-A` reference pair and canonical profile id is
     made explicit.
5. Authority provenance resolution is not yet frozen in released artifacts.
   - `authoritative_gate_source` still needs a canonical resolution surface limited to
     accepted governance artifacts and accepted `V35` runtime authority artifacts, and it
     must be required on every authoritative, gated, committing, or approval-bearing
     interaction entry.
6. Stable provenance hooks and implementation-observable bindings are not yet released.
   - later diagnostics and rendered-surface conformance need these hooks before any UI
     implementation path widens.
   - v62 also needs minimum frozen target surfaces so later conformance is not forced to
     reverse-engineer partial bindings.
7. Evidence-before-commit preservation can drift at the projection layer.
   - `V36-A` froze the glossary, but v62 still has to prove projection preserves the same
     bounded-workbench reachability rule rather than reinterpreting it.
8. Advisory/authoritative boundary collapse risk remains open.
   - projection and interaction outputs could still visually or structurally collapse
     advisory actions into authoritative actions without an explicit guard lane.
9. Requested-runtime-effect wording could silently mint authority.
   - interaction artifacts must describe already-accepted runtime truth rather than
     inventing new authority through UX-local semantics.
10. Runtime-visible-consequence wording drift remains open.
    - interaction artifacts could overstate accepted runtime truth or collapse requested
      effect and accepted effect into one meaning without an explicit epistemic boundary.
11. Page-local projection improvisation risk remains open.
    - without explicit guards, v62 could leak ad hoc route/component logic into the
      released projection/interaction lane instead of consuming the closed `V36-A`
      substrate.
12. Greenfield placement/accretion risk remains open.
    - v62 should land in explicit artifact foundations, not as app-only or route-local
      logic.
13. No canonical `v36b_surface_projection_interaction_evidence@1` exists on `main`.
    - closeout-grade evidence for the `V36-B` lane still has to be defined and emitted.
14. Guard coverage gap for provenance/binding failures remains open.
    - the repo does not yet fail closed on invalid `authoritative_gate_source`, missing
      bindings, missing provenance hooks, forbidden authority-source classes, unstable
      deterministic bindings, glossary shadowing, or evidence-before-commit drift in the
      projection/interaction layer.
15. Existing route rewrite leakage risk remains open.
    - the next slice must stay pre-rendered-surface and must not silently widen into
      `apps/web` implementation work.
16. Stop-gate continuity risk remains open.
    - v62 still has to prove exact metric-key continuity against v61 while adding the new
      evidence lane.

## Blocking Read

- The main architectural blocker is not missing UI code; it is the absence of canonical
  projection and interaction artifacts that can carry authority provenance and later
  conformance bindings without route-level improvisation or drift away from the released
  `V36-A` accepted reference substrate.
- The main sequencing blocker is that `V36-C` through `V36-E` become structurally unsafe
  if v62 does not first freeze one deterministic projection/interaction pair over the
  released `V36-A` substrate.

## Recommendation (Pre Lock)

1. Lock `vNext+62` as a narrow `V36-B` artifact baseline only.
2. Require one accepted deterministic reference projection/interaction pair, not just
   schema existence, and require it to bind back to the released accepted `V36-A`
   reference pair plus canonical profile id.
3. Make `authoritative_gate_source`, stable provenance hooks, and
   implementation-observable bindings first-class acceptance targets in `B1` and `B2`,
   with frozen minimum target surfaces and explicit rejection of forbidden authority
   sources.
4. Keep rendered-surface work, diagnostics/conformance, compiler export, and broad route
   retrofits explicitly deferred unless released under new lock text.
