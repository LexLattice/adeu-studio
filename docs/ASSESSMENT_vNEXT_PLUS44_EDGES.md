# Assessment vNext+44 Edges (V33-A Post-Hoc)

This document records post-implementation edge analysis for `vNext+44` (`V33-A` Pipeline Profile + TaskPack contracts + deterministic compiler + fail-closed guards).

Status: post-hoc assessment (March 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS44_EDGES.md",
  "phase": "post_hoc_assessment",
  "authoritative": true,
  "authoritative_scope": "v44_closeout_edge_analysis",
  "required_in_closeout": true,
  "notes": "Post-hoc assessment refreshed against merged v44 implementation and closeout artifacts."
}
```

## Scope

- In scope: `V33-A` contract/compiler implementation (`S1`) and determinism/fail-closed guard suite (`S2`).
- Out of scope: Codex SDK runner (`V33-B`), auditor/evidence-writer lane (`V33-C`), integrated/standalone UX packaging (`V33-D`), metric-key expansion, and runtime/provider/proposer boundary changes.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS44.md`
- PR `#236` (`contracts: add V33-A pipeline profile and taskpack compiler MVP`)
- PR `#237` (`tests: add v44 taskpack determinism and fail-closed guard suite`)
- `packages/adeu_agent_harness/src/adeu_agent_harness/compile.py`
- `packages/adeu_agent_harness/tests/test_taskpack_compile.py`
- `artifacts/quality_dashboard_v44_closeout.json`
- `artifacts/stop_gate/metrics_v44_closeout.json`
- `artifacts/stop_gate/report_v44_closeout.md`
- `artifacts/agent_harness/v44/taskpack_profile_registry.json`
- `artifacts/agent_harness/v44/profiles/v44_closeout_profile.json`
- `artifacts/agent_harness/v44/taskpacks/v41/v44_closeout/taskpack_manifest.json`

## Post-Hoc Edge Set (V33-A)

1. Raw-doc semantic authority bleed risk.
2. Registry bypass / ad-hoc profile path injection risk.
3. Registry mutability drift under stable `profile_id` risk.
4. Profile schema/entry drift risk.
5. Authority-input arc-selection ambiguity risk.
6. TaskPack component set/schema-id drift risk.
7. Manifest component-hash mismatch risk.
8. Bundle-hash-subject drift risk.
9. Markdown projection section-order drift risk.
10. Attribution marker missing/position/spoof/collision risk.
11. Required-error-channel downgrade risk.
12. Stop-gate continuity regression risk.

## Guardrail Evaluation (Observed)

- Compiler-authority lock: pass.
  - taskpack compiler consumes explicit profile contract + compiled ASC artifacts only.
- Registry-only profile resolution lock: pass.
  - absolute/ad-hoc path ingestion rejected fail-closed.
- Registry hash-binding lock: pass.
  - resolved canonical profile hash mismatch fails closed (`AHK0006`).
- Registry schema/uniqueness lock: pass.
  - malformed entry, duplicate `profile_id`, and schema mismatch fail closed (`AHK0014`/`AHK0016`/`AHK0003`).
- Authority-input resolution lock: pass.
  - invalid arc selection and missing/schema-drift authority inputs fail closed (`AHK0008`/`AHK0009`/`AHK0003`).
- ABI integrity lock: pass.
  - required component presence, schema-id format/binding, and component-hash integrity enforced by `verify_taskpack_bundle(...)` (`AHK0017`/`AHK0018`/`AHK0019`).
- Bundle-hash-subject lock: pass.
  - canonical manifest hash subject mismatch fails closed (`AHK0020`).
- Markdown projection/attribution locks: pass.
  - section-order drift, missing markers, invalid marker position, and marker spoof/collision all fail closed (`AHK0010`/`AHK0011`/`AHK0012`/`AHK0013`).
- Severity lock: pass.
  - required violations emit error payload on stderr with non-zero exit; no warning-channel substitution.
- Continuity lock: pass.
  - stop-gate schema family remains `stop_gate_metrics@1`; v43-v44 metric keysets are exact-set equal with cardinality `80`.

## Coverage Snapshot

- v44 `S2` test file now covers 20 deterministic/fail-closed cases (`20 passed`).
- Bundle verification path is invoked both directly by tests and by compiler post-write self-verification.

## Known Limits (Accepted in v44)

- Runtime anti-injection policy enforcement over model outputs is deferred to `V33-B`.
- Auditor/evidence-writer lane automation is deferred to `V33-C`.
- Integrated vs standalone UX mode parity enforcement is deferred to `V33-D`.
- v44 intentionally introduces no stop-gate metric-key changes.

## Residual Risks

1. Future runner-surface work (`V33-B`) can reintroduce authority-boundary drift if candidate-change-plan validation is not frozen up front.
2. Runtime-observability deltas remain informational unless a future arc adds explicit pass/fail thresholds.
3. Closeout reproducibility still depends on strict deterministic env usage for all regeneration commands.

## Follow-on Recommendation

1. Start `vNext+45` planning for `V33-B` with explicit lock text for:
   - candidate-change-plan canonicalization,
   - taskpack-only authority enforcement,
   - pre-write policy validation and fail-closed rejection.
2. Keep v44 taskpack closeout artifacts and hashes as the frozen baseline for runner-lane integration testing.
