# Draft Stop-Gate Decision (Post vNext+48)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md`

Status: draft decision note (post-hoc closeout capture, March 5, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS48.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v48_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+48` closeout evidence only.
- It must not redefine semantics, locks, or scope from `docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md`.
- This note captures `V34-A` (`X1`/`X2`) closeout evidence only; it does not authorize `V34-B`..`V34-G` behavior release.
- Signature pre-flight remains artifact-authoritative, deterministic, and fail-closed under frozen lock text.
- Runtime-observability comparison row remains required evidence and informational-only in this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `f9114b5c2e883fa50289083683b2fd19ae8c76b9`
- arc-completion CI run:
  - Run ID: `22731407840`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22731407840`
  - conclusion: `success`
- merged implementation PRs:
  - `#245` (`contracts: add V34-A signing pre-flight verifier MVP`)
  - `#246` (`tests: add v48 signing determinism and fail-closed guard suite`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v48_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v48_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v48_closeout.md`
  - runtime observability evidence input: `artifacts/agent_harness/v48/evidence_inputs/runtime_observability_comparison_v48.json`
  - metric-key continuity evidence input: `artifacts/agent_harness/v48/evidence_inputs/metric_key_continuity_assertion_v48.json`
  - signing wiring evidence input: `artifacts/agent_harness/v48/evidence_inputs/v34a_signing_wiring_evidence_v48.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS48_EDGES.md`

- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v48_closeout.json --baseline artifacts/quality_dashboard_v47_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v48_closeout.json --quality-baseline artifacts/quality_dashboard_v47_closeout.json --out-json artifacts/stop_gate/metrics_v48_closeout.json --out-md artifacts/stop_gate/report_v48_closeout.md`

## Exit-Criteria Check (vNext+48)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `X1` merged with green CI | required | `pass` | PR `#245` merged; CI run `22731053789` is `success` |
| `X2` merged with green CI | required | `pass` | PR `#246` merged; CI run `22731407840` is `success` |
| Stop-gate schema-family continuity retained | required | `pass` | `schema = "stop_gate_metrics@1"` in v47 and v48 closeout metrics |
| Stop-gate metric-key continuity retained | required | `pass` | v47 and v48 keysets are exact-set equal (`added_keys = []`, `removed_keys = []`) |
| Deterministic cardinality continuity retained | required | `pass` | metric-key cardinality computed from `metrics` keys is `80 -> 80` |
| V34-A signing pre-flight and fail-closed guard suite are merged and test-covered | required | `pass` | PR `#245`, PR `#246`, and `packages/adeu_agent_harness/tests/test_taskpack_signature.py` (`18` passing tests on closeout rerun) |
| Required closeout JSON blocks are present | required | `pass` | `runtime_observability_comparison@1`, `metric_key_continuity_assertion@1`, `v34a_signing_wiring_evidence@1` under `artifacts/agent_harness/v48/evidence_inputs/` |
| Historical continuity posture remains green | required | `pass` | v48 closeout `issues = []`, `valid = true`, `all_passed = true` |
| No boundary-release expansion introduced | required | `pass` | v48 scope remains `V34-A` only (`X1`/`X2`) |

Summary:

- `schema = "stop_gate_metrics@1"`
- `valid = true`
- `all_passed = true`
- `issues = []`
- `derived_cardinality = 80` (computed from `metrics` keyset cardinality)

## Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v47_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v48_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v47 Baseline vs v48 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+47",
  "current_arc": "vNext+48",
  "baseline_source": "artifacts/stop_gate/report_v47_closeout.md",
  "current_source": "artifacts/stop_gate/report_v48_closeout.md",
  "baseline_elapsed_ms": 105,
  "current_elapsed_ms": 111,
  "delta_ms": 6,
  "notes": "v48 closeout remains informational-only for timing. Runtime byte observability uses a fixed replay-cycle aggregate (`bytes_hashed_replay_cycles = 3`)."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+47` baseline | `artifacts/stop_gate/metrics_v47_closeout.json` | `22` | `78` | `105` | `68230` | `204690` | `true` | `true` |
| `vNext+48` closeout | `artifacts/stop_gate/metrics_v48_closeout.json` | `22` | `78` | `111` | `68230` | `204690` | `true` | `true` |

## V34-A Signing Wiring Evidence

```json
{
  "schema": "v34a_signing_wiring_evidence@1",
  "preflight_entrypoint": "python -m adeu_agent_harness.verify_taskpack_signature",
  "signature_subject": "taskpack_bundle_hash",
  "single_signature_only": true,
  "algorithm_key_binding_enforced": true,
  "verification_passed": true,
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v47": true,
  "notes": "v48 X1/X2 merged with deterministic pre-flight signing verification and fail-closed downstream binding guards on main."
}
```

## Recommendation (Post v48)

- gate decision:
  - `GO_VNEXT_PLUS49_PLANNING_DRAFT`
- rationale:
  - v48 closes `V34-A` (`X1`/`X2`) with deterministic signing pre-flight and fail-closed guard coverage on `main`.
  - no continuity, schema-family, or metric-key regressions were observed in closeout evidence.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md`, `docs/ASSESSMENT_vNEXT_PLUS49_EDGES.md`, and `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS49.md` for `V34-B` selection (or justified alternate).
2. Keep v48 closeout artifacts stable; rerun closeout commands only under frozen deterministic env contract.
3. Keep `V34-C`..`V34-G` deferred until explicitly locked in later arcs.
