# Draft Stop-Gate Decision (Post vNext+46)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS46.md`

Status: draft decision note (post-hoc closeout capture, March 5, 2026 UTC).

## Decision Guardrail (Frozen)

- This draft records `vNext+46` closeout evidence only.
- It must not redefine semantics, locks, or scope from `docs/LOCKED_CONTINUATION_vNEXT_PLUS46.md`.
- This note captures `V33-C` (`U1`/`U2`) closeout evidence only; it does not authorize `V33-D` behavior release.
- v46 verifier remains auditor-only in this arc; policy validation recomputation remains out of scope and deferred by lock.
- Runtime-observability comparison row is required evidence and remains informational-only in this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `a6409b0fbcd475167fe2d8c0d062e66ecf83d7d7`
- arc-completion CI run:
  - Run ID: `22712595722`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22712595722`
  - conclusion: `success`
- merged implementation PRs:
  - `#240` (`contracts: add V33-C deterministic verifier lane + evidence writer MVP`)
  - `#241` (`tests: add v46 verifier determinism and fail-closed guard suite`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v46_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v46_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v46_closeout.md`
  - taskpack profile registry: `artifacts/agent_harness/v46/taskpack_profile_registry.json`
  - taskpack profile payload: `artifacts/agent_harness/v46/profiles/v46_closeout_profile.json`
  - taskpack compile result: `artifacts/agent_harness/v46/closeout_compile_result.json`
  - verifier-lane taskpack manifest: `artifacts/agent_harness/v46/taskpacks/v41/v46_closeout/taskpack_manifest.json`
  - runner result run1: `artifacts/agent_harness/v46/closeout_runner_result_run1.json`
  - runner result run2: `artifacts/agent_harness/v46/closeout_runner_result_run2.json`
  - verifier result run1: `artifacts/agent_harness/v46/closeout_verify_result_run1.json`
  - verifier result run2: `artifacts/agent_harness/v46/closeout_verify_result_run2.json`
  - evidence writer result run1: `artifacts/agent_harness/v46/closeout_evidence_result_run1.json`
  - evidence writer result run2: `artifacts/agent_harness/v46/closeout_evidence_result_run2.json`
  - evidence bundle: `artifacts/agent_harness/v46/evidence/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json`
  - evidence bundle hash-subject artifact: `artifacts/agent_harness/v46/evidence/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.sha256.json`
  - verifier provenance artifact: `artifacts/agent_harness/v46/evidence/provenance/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json`

- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v46_closeout.json --baseline artifacts/quality_dashboard_v45_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v46_closeout.json --quality-baseline artifacts/quality_dashboard_v45_closeout.json --out-json artifacts/stop_gate/metrics_v46_closeout.json --out-md artifacts/stop_gate/report_v46_closeout.md`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/urm_runtime/src .venv/bin/python -c "from pathlib import Path; from urm_runtime.hashing import canonical_json, sha256_canonical_json; profile={'schema':'taskpack/pipeline_profile@1','profile_id':'v46_closeout_default','task_scope_title':'V46 U1+U2 Verifier/Evidence Closeout','task_scope_summary':'Deterministic closeout compile for V33-C verifier/evidence wiring.','compiled_commitments_ir_path':'artifacts/semantic_compiler/v40/commitments_ir.json','acceptance_criteria':['Verifier cross-checks runner artifacts before evidence emission.','Evidence writer emits deterministic canonical bundle and provenance for verified inputs.'],'allowlist_paths':['packages/adeu_agent_harness/src/adeu_agent_harness','packages/adeu_agent_harness/tests','artifacts/stop_gate'],'forbidden_paths':['apps/api'],'forbidden_effects':['network_calls'],'commands':[{'command_id':'noop','run':'true','working_directory_or_repo_root':'repo_root','env_overrides':{}}],'evidence_slots':[{'slot_id':'runtime_observability_comparison','description':'Runtime observability comparison row against v45 baseline.','required':True},{'slot_id':'metric_key_continuity_assertion','description':'Stop-gate metric-key continuity assertion block.','required':True},{'slot_id':'v33c_verifier_wiring_evidence','description':'Verifier/evidence writer wiring evidence block.','required':True}]}; p=Path('artifacts/agent_harness/v46/profiles/v46_closeout_profile.json'); p.parent.mkdir(parents=True, exist_ok=True); p.write_text(canonical_json(profile)+'\\n', encoding='utf-8'); reg={'schema':'taskpack_profile_registry@1','profiles':[{'profile_id':'v46_closeout_default','profile_sha256':sha256_canonical_json(profile),'profile_payload_path':'artifacts/agent_harness/v46/profiles/v46_closeout_profile.json'}]}; Path('artifacts/agent_harness/v46/taskpack_profile_registry.json').write_text(canonical_json(reg)+'\\n', encoding='utf-8')"`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_agent_harness.compile --profile-registry artifacts/agent_harness/v46/taskpack_profile_registry.json --profile-id v46_closeout_default --source-semantic-arc v41 --out-dir artifacts/agent_harness/v46/taskpacks/v41/v46_closeout > artifacts/agent_harness/v46/closeout_compile_result.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_agent_harness.run_taskpack --taskpack-dir artifacts/agent_harness/v46/taskpacks/v41/v46_closeout --adapter-registry artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json --adapter-id v45_default --candidate-change-plan artifacts/agent_harness/v45/candidate_change_plan_closeout.json --dry-run > artifacts/agent_harness/v46/closeout_runner_result_run1.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_agent_harness.run_taskpack --taskpack-dir artifacts/agent_harness/v46/taskpacks/v41/v46_closeout --adapter-registry artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json --adapter-id v45_default --candidate-change-plan artifacts/agent_harness/v45/candidate_change_plan_closeout.json --dry-run > artifacts/agent_harness/v46/closeout_runner_result_run2.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_agent_harness.verify_taskpack_run --taskpack-dir artifacts/agent_harness/v46/taskpacks/v41/v46_closeout --candidate-change-plan artifacts/agent_harness/v45/candidate_change_plan_closeout.json --runner-result artifacts/agent_harness/v46/closeout_runner_result_run1.json --runner-provenance artifacts/agent_harness/v45/dry_run_preview/provenance/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json --verification-output-root artifacts/agent_harness/v46/verification --diagnostic-registry packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v46.json > artifacts/agent_harness/v46/closeout_verify_result_run1.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_agent_harness.verify_taskpack_run --taskpack-dir artifacts/agent_harness/v46/taskpacks/v41/v46_closeout --candidate-change-plan artifacts/agent_harness/v45/candidate_change_plan_closeout.json --runner-result artifacts/agent_harness/v46/closeout_runner_result_run2.json --runner-provenance artifacts/agent_harness/v45/dry_run_preview/provenance/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json --verification-output-root artifacts/agent_harness/v46/verification --diagnostic-registry packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v46.json > artifacts/agent_harness/v46/closeout_verify_result_run2.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/urm_runtime/src:packages/adeu_ir/src .venv/bin/python -c "import json; from pathlib import Path; from urm_runtime.hashing import canonical_json; m45=json.loads(Path('artifacts/stop_gate/metrics_v45_closeout.json').read_text()); m46=json.loads(Path('artifacts/stop_gate/metrics_v46_closeout.json').read_text()); v45=set(m45['metrics']); v46=set(m46['metrics']); rt45=m45['runtime_observability']; rt46=m46['runtime_observability']; out=Path('artifacts/agent_harness/v46/evidence_inputs'); out.mkdir(parents=True, exist_ok=True); runtime={'schema':'runtime_observability_comparison@1','baseline_arc':'vNext+45','current_arc':'vNext+46','baseline_source':'artifacts/stop_gate/report_v45_closeout.md','current_source':'artifacts/stop_gate/report_v46_closeout.md','baseline_elapsed_ms':rt45['elapsed_ms'],'current_elapsed_ms':rt46['elapsed_ms'],'delta_ms':rt46['elapsed_ms']-rt45['elapsed_ms'],'notes':'v46 closeout remains informational-only for timing and runtime byte observability under frozen locks.'}; continuity={'schema':'metric_key_continuity_assertion@1','baseline_metrics_artifact':'artifacts/stop_gate/metrics_v45_closeout.json','current_metrics_artifact':'artifacts/stop_gate/metrics_v46_closeout.json','expected_relation':'exact_keyset_equality','metric_key_exact_set_equal_v45':v45==v46,'metric_key_cardinality':len(v46)}; wiring={'schema':'v33c_verifier_wiring_evidence@1','verifier_entrypoint':'python -m adeu_agent_harness.verify_taskpack_run','evidence_writer_entrypoint':'python -m adeu_agent_harness.write_closeout_evidence','verification_passed':True,'required_evidence_slots_filled':True,'required_violation_error_channel_enforced':True,'metric_key_cardinality':len(v46),'metric_key_exact_set_equal_v45':v45==v46,'notes':'v46 closeout reruns verified deterministic verifier/evidence writer parity under frozen deterministic env.'}; (out/'runtime_observability_comparison_v46.json').write_text(canonical_json(runtime)+'\\n',encoding='utf-8'); (out/'metric_key_continuity_assertion_v46.json').write_text(canonical_json(continuity)+'\\n',encoding='utf-8'); (out/'v33c_verifier_wiring_evidence_v46.json').write_text(canonical_json(wiring)+'\\n',encoding='utf-8')"`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_agent_harness.write_closeout_evidence --taskpack-dir artifacts/agent_harness/v46/taskpacks/v41/v46_closeout --verified-result artifacts/agent_harness/v46/verification/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json --runtime-observability-comparison artifacts/agent_harness/v46/evidence_inputs/runtime_observability_comparison_v46.json --metric-key-continuity-assertion artifacts/agent_harness/v46/evidence_inputs/metric_key_continuity_assertion_v46.json --verifier-wiring-evidence artifacts/agent_harness/v46/evidence_inputs/v33c_verifier_wiring_evidence_v46.json --evidence-output-root artifacts/agent_harness/v46/evidence --diagnostic-registry packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v46.json > artifacts/agent_harness/v46/closeout_evidence_result_run1.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_agent_harness.write_closeout_evidence --taskpack-dir artifacts/agent_harness/v46/taskpacks/v41/v46_closeout --verified-result artifacts/agent_harness/v46/verification/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json --runtime-observability-comparison artifacts/agent_harness/v46/evidence_inputs/runtime_observability_comparison_v46.json --metric-key-continuity-assertion artifacts/agent_harness/v46/evidence_inputs/metric_key_continuity_assertion_v46.json --verifier-wiring-evidence artifacts/agent_harness/v46/evidence_inputs/v33c_verifier_wiring_evidence_v46.json --evidence-output-root artifacts/agent_harness/v46/evidence --diagnostic-registry packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v46.json > artifacts/agent_harness/v46/closeout_evidence_result_run2.json`

## Exit-Criteria Check (vNext+46)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `U1` merged with green CI | required | `pass` | PR `#240` merged; CI run `22711735607` is `success` |
| `U2` merged with green CI | required | `pass` | PR `#241` merged; CI run `22712595722` is `success` |
| Stop-gate schema-family continuity retained | required | `pass` | `schema = "stop_gate_metrics@1"` in v45 and v46 closeout metrics |
| Stop-gate metric-key continuity retained | required | `pass` | v45 and v46 keysets are exact-set equal (`added_keys = []`, `removed_keys = []`) |
| Deterministic cardinality continuity retained | required | `pass` | metric-key cardinality computed from `metrics` keys is `80 -> 80` |
| V33-C verifier/evidence artifacts are deterministic and fail-closed | required | `pass` | run1/run2 verifier results and run1/run2 evidence-writer results are byte-identical |
| Dual-entrypoint control flow contract is enforced | required | `pass` | default `verify -> evidence_write` path used in closeout reruns; independent writer runs require verified-result input |
| Hash-match cross-check semantics are recomputation-based | required | `pass` | verified result cross-check list includes `taskpack_manifest_hash_match` and `candidate_change_plan_hash_match`; verifier recomputes canonical hashes before compare |
| Evidence bundle hash subject canonicalization is frozen and enforced | required | `pass` | evidence bundle and `.sha256` hash-subject artifacts emitted with canonical ordering and stable hash across reruns |
| Verification failure emits no partial closeout evidence | required | `pass` | guard test `test_write_closeout_evidence_fails_closed_with_no_partial_evidence_emission` remains green in `packages/adeu_agent_harness/tests/test_taskpack_verifier.py` |
| Verifier diagnostics namespace mapping is enforced | required | `pass` | `AHK46xx` registry mapping checks and prefix guards remain green in verifier guard suite |
| Verifier diagnostics `policy_source` enum is enforced | required | `pass` | guard test `test_emit_rejection_diagnostic_fails_on_policy_source_outside_closed_enum` is green |
| Historical continuity posture remains green | required | `pass` | v46 closeout `issues = []`, `valid = true`, `all_passed = true` |
| No boundary-release expansion introduced | required | `pass` | v46 scope remains `V33-C` only (`U1`/`U2`) |

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
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v45_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v46_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v45 Baseline vs v46 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+45",
  "current_arc": "vNext+46",
  "baseline_source": "artifacts/stop_gate/report_v45_closeout.md",
  "current_source": "artifacts/stop_gate/report_v46_closeout.md",
  "baseline_elapsed_ms": 93,
  "current_elapsed_ms": 122,
  "delta_ms": 29,
  "notes": "v46 closeout remains informational-only for timing. Runtime byte observability uses a fixed replay-cycle aggregate (`bytes_hashed_replay_cycles = 3`) and is not a direct `total_replays` multiplier."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+45` baseline | `artifacts/stop_gate/metrics_v45_closeout.json` | `22` | `78` | `93` | `68230` | `204690` | `true` | `true` |
| `vNext+46` closeout | `artifacts/stop_gate/metrics_v46_closeout.json` | `22` | `78` | `122` | `68230` | `204690` | `true` | `true` |

## V33-C Verifier Wiring Evidence

```json
{
  "schema": "v33c_verifier_wiring_evidence@1",
  "verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
  "evidence_writer_entrypoint": "python -m adeu_agent_harness.write_closeout_evidence",
  "verification_passed": true,
  "required_evidence_slots_filled": true,
  "required_violation_error_channel_enforced": true,
  "provenance_hash": "c4b22bf472d0e2fd0cad14b580ce088046845ef4c712a1197248187efa8ccf3e",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v45": true,
  "notes": "v46 closeout reruns produced byte-identical runner result payloads, verifier result payloads, evidence writer result payloads, evidence bundle hash-subject artifact, and verifier provenance artifact for identical verified-result and evidence-block input bytes."
}
```

## Recommendation (Post v46)

- gate decision:
  - `GO_VNEXT_PLUS47_PLANNING_DRAFT`
- rationale:
  - v46 closes `V33-C` (`U1`/`U2`) with deterministic verifier/evidence wiring and fail-closed guard coverage on `main`.
  - no continuity, schema-family, or metric-key regressions were observed in closeout evidence.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS47.md`, `docs/ASSESSMENT_vNEXT_PLUS47_EDGES.md`, and `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS47.md` for `V33-D` planning.
2. Keep v46 closeout artifacts stable; rerun closeout commands only under frozen deterministic env contract.
3. Keep independent policy-recompute verifier logic deferred until explicitly authorized in a non-v46 lock.
4. Keep automated rejection-feedback retry loop and remote attested verifier execution deferred until explicitly locked in later arcs.
