# Assessment vNext+70 Edges (Pre Lock)

This document records edge planning for `vNext+70` (`V37-E` advisory control-update
export baseline) before implementation begins.

Status: pre-lock assessment (March 18, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS70_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "authoritative_scope": "v70_prelock_edge_planning",
  "required_in_decision": true,
  "notes": "This is a pre-lock planning artifact only. Post-closeout edge disposition must replace this state after v70 implementation completes."
}
```

## Scope

- In scope: thin `V37-E` recursive-compilation advisory control-update export substrate
  over the closed `V35`, `V36`, `V37-A`, `V37-B`, `V37-C`, and `V37-D` baseline;
  canonical `meta_control_update_candidate@1`; canonical
  `meta_control_update_manifest@1`; one deterministic advisory candidate and one
  deterministic manifest over the accepted bounded reference loop; hard-control-first
  ranking; typed application friction; and closeout evidence/guard coverage.
- Out of scope: broader multi-run loop-family widening, generalized autonomous
  self-improvement, automatic repo mutation, automatic prompt rewrite, automatic
  validator rollout, stop-gate schema-family fork, metric-key expansion, and the
  separate `O1`/`O2`/`O3` closeout-hardening bundle.

## Inputs

- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v11.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS70.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/LOCKED_URM_CODEX_INTEGRATION_v0.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS69.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS69.md`
- `docs/ASSESSMENT_vNEXT_PLUS69_EDGES.md`

## Pre-Lock Edge Set (v70 Start)

1. No canonical `meta_control_update_candidate@1` schema exists on `main`.
   - `E1` must define stable typed advisory candidates over accepted intent,
     accepted loop substrate, accepted diagnostics, and accepted conformance.
2. No canonical `meta_control_update_manifest@1` schema exists on `main`.
   - `E1` must define a typed manifest rather than a loose export summary.
3. No accepted deterministic candidate/manifest pair yet binds back to the released
   `V37-A`, `V37-B`, `V37-C`, and `V37-D` tuple.
   - `E1` and `E2` must fail closed unless `reference_loop_family`,
     `reference_instance_id`, and `intent_packet_id` remain exactly equal across the
     consumed and emitted artifacts.
4. Advisory candidates could remain too vague unless minimum per-candidate structure is
   frozen.
   - `E1` must freeze stable ids, bounded target control classes, target surface refs,
     bound finding ids, supporting evidence refs, drift-reduction claim, risk notes,
     explicit friction mode, and advisory-only status.
5. Export ranking could drift toward prompt-local fixes unless hard-control-first
   priority order is frozen.
   - `E1` and `E2` must make validator/runtime/evidence/schema fixes outrank
     prompt-dispatch fixes where the same drift supports multiple candidate targets.
6. Candidate emission could be mistaken for acceptance or governance authority.
   - `E1` and `E2` must make explicit that candidate emission is advisory only and does
     not by itself become policy, acceptance, or repo mutation.
7. Default emitted form could bypass adjudication through raw patch or shell payloads.
   - `E1` and `E2` must preserve typed friction between recommendation and
     application and reject blind copy-paste bypass by default.
8. Candidate derivation could drift away from accepted substrate into soft local
   heuristics.
   - `E1` and `E2` must bind candidate derivation exactly to accepted intent,
     accepted loop outputs, accepted diagnostics, accepted conformance, and accepted
     evidence refs.
9. No canonical `v37e_control_update_export_evidence@1` exists on `main`.
   - `E2` must materialize the closeout evidence lane for deterministic advisory export,
     advisory-only posture, ranking preservation, and stop-gate continuity.
10. Stop-gate continuity risk remains open at arc start.
    - v70 must preserve `stop_gate_metrics@1` and exact metric-key equality with v69.
11. Thin-slice boundary drift remains open.
    - v70 must not quietly ship broader multi-run widening or any automatic mutation
      surface under an advisory control-update label.

## Recommendation (Pre Lock)

1. Treat `V37-E` as the correct next thin slice after `V37-D` closure.
2. Keep v70 strictly at one advisory control-update export substrate lane over the
   released bounded reference loop.
3. Consume the released `V37-A`, `V37-B`, `V37-C`, and `V37-D` artifacts as
   authoritative and preserve the compilation-boundary distinction between candidate
   emission and accepted compilation.
4. Defer broader multi-run loop-family widening, automatic mutation surfaces, and the
   separate operational hardening bundle to later work.
