# Assessment vNext+64 Edges (Pre Lock)

This document records the pre-lock edge assessment for `vNext+64` (`V36-D` morph
diagnostics and conformance baseline).

Status: pre-lock assessment (March 15, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS64_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "authoritative_scope": "v64_pre_lock_edge_assessment",
  "required_in_decision": true,
  "notes": "This pre-lock assessment enumerates the blocking edge set for the proposed v64 starter bundle only; post-closeout disposition must replace it if the arc ships."
}
```

## Scope

- In scope: thin `V36-D` diagnostics/conformance baseline over the closed `V36-A`,
  `V36-B`, and `V36-C` substrate; one bounded
  `artifact_inspector_advisory_workbench` diagnostics family; deterministic seeded
  violation detection; severity taxonomy; provenance pointers; rendered-surface assertion
  bridging; a minimal typed conformance report; and closeout evidence/guard coverage.
- Out of scope: `V36-E` compiler export, lawful variant generation, repo-wide route
  rewrites, generic design-system release, stop-gate schema-family fork, metric-key
  expansion, runtime semantics changes, runtime auto-repair, and the separate
  `O1`/`O2`/`O3` closeout-hardening bundle.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md`
- `docs/ASSESSMENT_vNEXT_PLUS61_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md`
- `docs/ASSESSMENT_vNEXT_PLUS62_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS63.md`
- `docs/ASSESSMENT_vNEXT_PLUS63_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md`
- `docs/seed arc v10.md`
- `packages/adeu_core_ir/src/adeu_core_ir/ux_governance.py`
- `packages/adeu_core_ir/src/adeu_core_ir/ux_governance_evidence.py`
- `apps/api/fixtures/ux_governance/vnext_plus61/`
- `apps/api/fixtures/ux_governance/vnext_plus62/`
- `apps/api/fixtures/ux_governance/vnext_plus63/`
- `apps/web/src/app/artifact-inspector/`

## Pre-Lock Edge Set (Blocking Until Resolved)

1. No canonical `ux_morph_diagnostics@1` schema exists on `main`.
   - `V36-A` through `V36-C` closed substrate and one rendered reference surface only;
     no diagnostics artifact family is released yet.
2. No canonical `ux_conformance_report@1` schema exists on `main`.
   - the repo still lacks a typed final-judgment artifact that remains distinct from raw
     diagnostics, avoids prose-only conformance review, and freezes deterministic
     aggregation from findings to overall judgment.
3. No accepted deterministic reference diagnostics artifact exists on `main`.
   - v64 still needs one bounded reference diagnostics packet over the
     `artifact_inspector_advisory_workbench` family.
4. No accepted deterministic conformance report exists on `main`.
   - v64 still needs one bounded typed conformance summary derived from the same
     reference surface family and canonical profile id.
5. No deterministic severity taxonomy is frozen in released UX artifacts.
   - the first diagnostics lane must freeze `error` / `warning` / `advisory` rather than
     leaving severity as prose, and still needs to freeze a minimum per-finding
     structure.
6. No diagnostics provenance-pointer contract exists into the canonical artifact stack.
   - the repo still lacks canonical pointers from findings back to the released
     domain/morph/projection/interaction/rendered artifacts, plus the minimum
     audit-facing fields that show which rendered assertions and supporting evidence were
     actually used.
7. No rendered-surface assertion bridge is frozen over the v63 route contract, semantic
   snapshot, and binding manifest.
   - diagnostics/conformance still cannot rely on the released rendered reference surface
     deterministically, and the next slice still has to forbid smuggling fresh
     route-local heuristics through that bridge.
8. Same-context evidence-visibility violations are not yet surfaced deterministically.
   - the frozen `V36-A` glossary exists, and the rendered route consumes it, but no
     canonical diagnostics artifact can yet report a violation against it.
9. Provisional-versus-authoritative styling drift is not yet surfaced deterministically.
   - v63 renders the states, but no released diagnostics lane reports when that boundary
     is violated.
10. Advisory/authoritative boundary collapse is not yet surfaced deterministically.
    - a future regression could still collapse action semantics visually without a
      released canonical finding surface.
11. Recovery-path gaps and competing-primary-action conflicts are not yet surfaced
    deterministically.
    - the rendered route exists, but the repo still lacks canonical UX-law findings for
      these bounded first-family failures, plus deterministic findings for destructive
      confirmation gaps, utility/posture conflicts, and requested-profile versus
      realized-command-grammar conflicts against the frozen approved profile contract.
12. Diagnostics could regress into a taste engine without an explicit constitutional lock.
    - the next slice must stay artifact-backed and provenance-linked rather than emitting
      aesthetic preference prose.
13. Event-stream or worker-prose truth substitution risk remains open in diagnostics.
    - findings and conformance summaries must not treat event streams, worker prose, or
      local UI heuristics as accepted truth or authoritative grounds for pass/fail
      judgment.
14. No canonical `v36d_morph_diagnostics_conformance_evidence@1` exists on `main`.
    - closeout-grade evidence for the `V36-D` lane still has to be defined and emitted.
15. Guard coverage gap for diagnostics/conformance drift remains open.
    - the repo does not yet fail closed on missing seeded violations, missing provenance
      pointers, missing rendered assertion bridges, non-deterministic severity mapping,
      taste-engine drift, or conformance/report drift in the `V36-D` layer.
16. Stop-gate continuity risk remains open.
    - v64 still has to prove exact metric-key continuity against v63 while adding the new
      diagnostics/conformance evidence lane.

## Blocking Read

- The main architectural blocker is not a missing screenshot or extra route chrome; it is
  the absence of one deterministic canonical diagnostics/conformance lane that proves the
  released rendered reference surface can be audited without manual taste review.
- The main sequencing blocker is that `V36-E` becomes structurally unsafe if v64 does not
  first freeze diagnostics, provenance, and conformance over the released `V36-C`
  rendered surface.

## Recommendation (Pre Lock)

1. Lock `vNext+64` as a narrow `V36-D` diagnostics/conformance baseline only.
2. Require one bounded diagnostics/conformance lane over the closed rendered
   `artifact_inspector_advisory_workbench` surface, not a broad UX review framework or
   repo-wide audit retrofit.
3. Make seeded violation detection, frozen severity taxonomy, canonical provenance
   pointers, rendered assertion bridging, typed conformance derivation, and
   no-taste-engine / no-truth-substitution guarantees first-class acceptance targets in
   `D1` and `D2`.
4. Keep compiler export, lawful variant generation, runtime auto-repair, and broad route
   retrofits explicitly deferred unless released under new lock text.
