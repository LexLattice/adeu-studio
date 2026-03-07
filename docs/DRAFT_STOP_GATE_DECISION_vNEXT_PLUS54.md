# Draft Stop-Gate Decision (Post vNext+54)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS54.md`

Status: draft decision note (post-hoc closeout capture, March 7, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS54.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v54_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+54` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS54.md`.
- This note captures `V34-F` standalone bundle integrity self-verification closeout evidence
  only; it does not authorize installer/updater behavior, detached distribution,
  fetch/unpack flows, or `V34-G` deployment-mode release by itself.
- Shared standalone integrity verification, deterministic integrity-result emission,
  manifest-authoritative emitted-file verification, and cumulative closeout evidence
  integration remain artifact-authoritative, deterministic, and fail-closed under frozen
  lock text.
- Runtime-observability comparison row remains required evidence and informational-only in
  this arc.
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md` is carried alongside this closeout as a
  non-authoritative post-v54 operational proposal only; it does not affect the v54 gate
  decision.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `e087ff95ae255e60fabe50eaa2b1c0508eb92b66`
- arc-completion CI runs:
  - PR `#257`
    - merge commit: `7ed78b536997ce30b3f315dc58138e69fd60940c`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/22796423448`
    - conclusion: `success`
  - PR `#258`
    - merge commit: `e087ff95ae255e60fabe50eaa2b1c0508eb92b66`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/22796835362`
    - conclusion: `success`
- merged implementation PRs:
  - `#257` (`contracts: add v34f standalone integrity checker baseline`)
  - `#258` (`tests: add v34f standalone integrity evidence guards`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v54_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v54_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v54_closeout.md`
  - runtime observability evidence input:
    `artifacts/agent_harness/v54/evidence_inputs/runtime_observability_comparison_v54.json`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v54/evidence_inputs/metric_key_continuity_assertion_v54.json`
  - policy recompute evidence input:
    `artifacts/agent_harness/v54/evidence_inputs/v34c_policy_recompute_evidence_v54.json`
  - retry-context evidence input:
    `artifacts/agent_harness/v54/evidence_inputs/v34d_retry_context_evidence_v54.json`
  - attestation evidence input:
    `artifacts/agent_harness/v54/evidence_inputs/v34e_attestation_evidence_v54.json`
  - standalone integrity evidence input:
    `artifacts/agent_harness/v54/evidence_inputs/v34f_standalone_integrity_evidence_v54.json`
  - standalone integrity verification artifact:
    `artifacts/agent_harness/v54/standalone_integrity/verification/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_06771cd37f98c093d817c36873f8e26bb428623b6ea23c3df3d20f63fa428782.json`
- supporting deterministic verifier/evidence artifacts (reproducible):
  - closeout profile:
    `artifacts/agent_harness/v54/profiles/v54_closeout_profile.json`
  - taskpack profile registry:
    `artifacts/agent_harness/v54/taskpack_profile_registry.json`
  - compiled closeout taskpack:
    `artifacts/agent_harness/v54/taskpacks/v41/v54_closeout/`
  - closeout candidate change plan:
    `artifacts/agent_harness/v54/candidate_change_plan.json`
  - retry-context seed candidate change plan:
    `artifacts/agent_harness/v54/candidate_change_plan_retry_context.json`
  - closeout runner result:
    `artifacts/agent_harness/v54/runner_result.json`
  - retry-context seed runner result:
    `artifacts/agent_harness/v54/runner_result_policy_failure.json`
  - copied runner preview/provenance/rejection artifacts:
    `artifacts/agent_harness/v54/runner/`
  - signing handoff artifacts:
    `artifacts/agent_harness/v54/test_signing/`
  - verification result:
    `artifacts/agent_harness/v54/verification/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_4fe7511982fb7ea924304156db4a02675b1468bda5ae22838a9cf33d5497ba21.json`
  - policy recompute artifact:
    `artifacts/agent_harness/v54/recompute/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_4fe7511982fb7ea924304156db4a02675b1468bda5ae22838a9cf33d5497ba21.json`
  - local verification artifact:
    `artifacts/agent_harness/v54/local_verification/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_4fe7511982fb7ea924304156db4a02675b1468bda5ae22838a9cf33d5497ba21.json`
  - local policy recompute artifact:
    `artifacts/agent_harness/v54/local_recompute/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_4fe7511982fb7ea924304156db4a02675b1468bda5ae22838a9cf33d5497ba21.json`
  - retry-context feeder artifact:
    `artifacts/agent_harness/v54/retry_context/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_1d4f0a307a8d3763432e438fe725457dbe7a02822b432aafd066aec46cbc641a.json`
  - sanitization profile artifact:
    `artifacts/agent_harness/v54/retry_context/retry_context_sanitization_profile.json`
  - remote enclave attestation artifact:
    `artifacts/agent_harness/v54/attestation/remote_enclave_attestation/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_4fe7511982fb7ea924304156db4a02675b1468bda5ae22838a9cf33d5497ba21.json`
  - attestation verification result artifact:
    `artifacts/agent_harness/v54/attestation/verification/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_4fe7511982fb7ea924304156db4a02675b1468bda5ae22838a9cf33d5497ba21.json`
  - standalone packaging result:
    `artifacts/agent_harness/v54/packaging/taskpack_packaging_result_standalone.json`
  - standalone packaging manifest:
    `artifacts/agent_harness/v54/packaging/standalone/taskpack_ux_packaging_manifest.json`
  - standalone packaging provenance:
    `artifacts/agent_harness/v54/packaging/standalone/provenance/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_4784867dc2624b4452fedf27eba98f64a587ffed215520972fd3d2fcff28a9ed.json`
  - standalone bundle root:
    `artifacts/agent_harness/v54/packaging/standalone/`
  - closeout evidence bundle:
    `artifacts/agent_harness/v54/evidence/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_4fe7511982fb7ea924304156db4a02675b1468bda5ae22838a9cf33d5497ba21.json`
  - closeout evidence bundle hash sidecar:
    `artifacts/agent_harness/v54/evidence/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_4fe7511982fb7ea924304156db4a02675b1468bda5ae22838a9cf33d5497ba21.sha256.json`
  - verifier provenance:
    `artifacts/agent_harness/v54/evidence/provenance/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_4fe7511982fb7ea924304156db4a02675b1468bda5ae22838a9cf33d5497ba21.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS54_EDGES.md`
- follow-on non-authoritative operational proposal:
  - `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v54_closeout.json --baseline artifacts/quality_dashboard_v53_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v54_closeout.json --quality-baseline artifacts/quality_dashboard_v53_closeout.json --out-json artifacts/stop_gate/metrics_v54_closeout.json --out-md artifacts/stop_gate/report_v54_closeout.md`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python - <<'PY' ... generate v54 profile/registry/taskpack, deterministic signing handoff, success + rejection runner artifacts, verification result, local-equivalence attestation artifacts, retry_context_feeder_result@1, retry_context_sanitization_profile@1, seeded pre-integrity closeout evidence bundle, standalone_integrity_verification_result@1, evidence_inputs/*.json, and final closeout evidence bundle/provenance from the v53 stop-gate artifacts, current compile/run/verify/attestation/retry_context/standalone_integrity/write_closeout_evidence entrypoints, and the frozen v45 adapter registry ... PY`
  - `make closeout-lint`

## Exit-Criteria Check (vNext+54)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `C1` merged with green CI | required | `pass` | PR `#257` merged; CI runs `22796423448` / `22796422968` are `success` |
| `C2` merged with green CI | required | `pass` | PR `#258` merged; CI runs `22796835362` / `22796832560` are `success` |
| Stop-gate schema-family continuity retained | required | `pass` | `schema = "stop_gate_metrics@1"` in v53 and v54 closeout metrics |
| Stop-gate metric-key continuity retained | required | `pass` | v53 and v54 keysets are exact-set equal (`metric_key_exact_set_equal_v53 = true`) |
| Deterministic cardinality continuity retained (`80`) | required | `pass` | metric-key cardinality computed from `metrics` keys is `80 -> 80` |
| `standalone_integrity_verification_result@1` emitted and schema-valid | required | `pass` | `artifacts/agent_harness/v54/standalone_integrity/verification/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_06771cd37f98c093d817c36873f8e26bb428623b6ea23c3df3d20f63fa428782.json` |
| `standalone_integrity_verification_result@1` emitted on failure paths too | required | `pass` | `integrity_result_emitted_on_failure = true` in `v34f_standalone_integrity_evidence_v54.json` and merged packaging guards |
| Input-validation failures still emit typed integrity results | required | `pass` | `integrity_result_emitted_on_input_validation_failure = true` in `v34f_standalone_integrity_evidence_v54.json` and merged packaging guards |
| Standalone-only deployment mode enforced | required | `pass` | `deployment_mode = "standalone"` and `deployment_mode_standalone_only = true` in `v34f_standalone_integrity_evidence_v54.json` |
| Packaging-manifest bundle-hash subject verified | required | `pass` | `packaging_manifest_bundle_hash_subject_verified = true` and declared/recomputed bundle hash equality in `v34f_standalone_integrity_evidence_v54.json` |
| Recomputed manifest bundle hash recorded | required | `pass` | `recomputed_manifest_bundle_hash = 06771cd37f98c093d817c36873f8e26bb428623b6ea23c3df3d20f63fa428782` |
| Full packaging-provenance artifact hash binding verified | required | `pass` | `packaging_provenance_binding_verified = true`, `packaging_provenance_artifact_hash_verified = true`, and provenance path/hash fields in `v34f_standalone_integrity_evidence_v54.json` |
| Explicit bundle-root input and bundle-relative path domain verified | required | `pass` | `bundle_root_input_explicit = true` and `manifest_paths_bundle_relative = true` in `v34f_standalone_integrity_evidence_v54.json` |
| Manifest duplicate paths, symlinks, and non-regular files fail closed | required | `pass` | `manifest_normalized_path_duplicates_forbidden = true`, `symlinks_forbidden = true`, and `regular_files_only = true` in `v34f_standalone_integrity_evidence_v54.json` plus merged packaging guards |
| Missing or extra bundle files fail closed | required | `pass` | `missing_or_extra_bundle_files_fail_closed = true` and `emitted_file_inventory_exact_match_verified = true` in `v34f_standalone_integrity_evidence_v54.json` |
| Canonical `v34f` evidence block emitted and hash-bound | required | `pass` | `standalone_integrity_verification_result_hash = 02833dd840ed1da4fca81a09e07c9dfc0780191ce94c5b1d138e81c100d2b23e` in `v34f_standalone_integrity_evidence_v54.json` and final closeout evidence bundle |

Summary:

- `schema = "stop_gate_metrics@1"`
- `valid = true`
- `all_passed = true`
- `issues = []`
- `derived_cardinality = 80` (computed from `metrics` keyset cardinality)

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v53_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v54_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison (v53 Baseline vs v54 Closeout)

```json
{"baseline_arc":"vNext+53","baseline_elapsed_ms":97,"baseline_source":"artifacts/stop_gate/report_v53_closeout.md","current_arc":"vNext+54","current_elapsed_ms":104,"current_source":"artifacts/stop_gate/report_v54_closeout.md","delta_ms":7,"notes":"v54 closeout remains informational-only for runtime timing/byte observability under frozen stop-gate semantics.","schema":"runtime_observability_comparison@1"}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+53` baseline | `artifacts/stop_gate/metrics_v53_closeout.json` | `22` | `78` | `97` | `68230` | `204690` | `true` | `true` |
| `vNext+54` closeout | `artifacts/stop_gate/metrics_v54_closeout.json` | `22` | `78` | `104` | `68230` | `204690` | `true` | `true` |

## V34-F Standalone Integrity Evidence

```json
{"actual_emitted_file_hashes_recomputed":true,"auto_fetch_or_unpack_forbidden":true,"bundle_root_escape_forbidden":true,"bundle_root_input_explicit":true,"contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS54.md#v34f_standalone_integrity_contract@1","current_packaging_materialization_failure_fails_closed":true,"current_packaging_materialization_recomputed":true,"deployment_mode":"standalone","deployment_mode_standalone_only":true,"emitted_file_inventory_exact_match_verified":true,"integrity_checker_entrypoint":"python -m adeu_agent_harness.standalone_integrity","integrity_result_emitted_on_failure":true,"integrity_result_emitted_on_input_validation_failure":true,"manifest_normalized_path_duplicates_forbidden":true,"manifest_paths_bundle_relative":true,"metric_key_cardinality":80,"metric_key_exact_set_equal_v53":true,"missing_or_extra_bundle_files_fail_closed":true,"normalized_emitted_path_duplicates_forbidden":true,"notes":"v54 closeout standalone integrity evidence regenerated on main.","packaging_manifest_bundle_hash_subject_verified":true,"packaging_manifest_schema_validated":true,"packaging_provenance_artifact_hash_verified":true,"packaging_provenance_binding_verified":true,"raw_repo_reads_forbidden":true,"recomputed_manifest_bundle_hash":"06771cd37f98c093d817c36873f8e26bb428623b6ea23c3df3d20f63fa428782","regular_files_only":true,"schema":"v34f_standalone_integrity_evidence@1","shared_integrity_checker_identifier":"v34f_standalone_integrity_checker@1:adeu_agent_harness.standalone_integrity.verify_standalone_integrity","shared_integrity_checker_identifier_policy":"frozen_module_function_path_or_registry_key_no_free_text","shared_integrity_checker_used":"adeu_agent_harness.standalone_integrity.verify_standalone_integrity","standalone_integrity_verification_result_hash":"02833dd840ed1da4fca81a09e07c9dfc0780191ce94c5b1d138e81c100d2b23e","standalone_integrity_verification_result_path":"artifacts/agent_harness/v54/standalone_integrity/verification/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_06771cd37f98c093d817c36873f8e26bb428623b6ea23c3df3d20f63fa428782.json","standalone_packaging_bundle_hash":"06771cd37f98c093d817c36873f8e26bb428623b6ea23c3df3d20f63fa428782","standalone_packaging_manifest_path":"artifacts/agent_harness/v54/packaging/standalone/taskpack_ux_packaging_manifest.json","standalone_packaging_provenance_hash":"9f917de5fd811749594bfe75c496c66953a5da23e1850a7c5ddd7f38d6c059e9","standalone_packaging_provenance_path":"artifacts/agent_harness/v54/packaging/standalone/provenance/5a131cd8f543b8e699b6f2506289edac212defef173893aa5a1cb33dcdd4bb62_4784867dc2624b4452fedf27eba98f64a587ffed215520972fd3d2fcff28a9ed.json","standalone_packaging_result_path":"artifacts/agent_harness/v54/packaging/taskpack_packaging_result_standalone.json","symlinks_forbidden":true,"verification_passed":true,"verification_passed_policy":"true_means_integrity_checker_validation_inventory_bundle_hash_guards_and_closeout_validation_passed_not_installer_success_or_deployment_mode_release","verification_result_semantic_input_forbidden":true}
```

## Recommendation (Post v54)

- gate decision:
  - `GO_VNEXT_PLUS55_PLANNING_DRAFT`
- rationale:
  - v54 closes the thin `V34-F` standalone bundle integrity self-verification baseline with
    deterministic standalone integrity artifacts, explicit bundle-root/path-domain guards,
    manifest-authoritative emitted-file verification, and canonical `v34f` evidence
    integrated on `main`.
  - no continuity, schema-family, or metric-key regressions were observed in closeout.
  - the follow-on closeout-hardening proposal is worth separate feedback and later
    scheduling, but it does not alter the v54 gate decision.
