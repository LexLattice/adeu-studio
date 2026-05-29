# Draft Stop-Gate Decision vNext+278

Status: post-closeout decision for `BRL-0-A`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS278.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+278` / `BRL-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS278.md`.
- It does not authorize semantic adjudication, domain ontology generation, HOB
  closure recomputation, OTB transition authorization, probe generation, probe
  execution, candidate replay execution, observation capture, candidate
  comparison, impact-cone selection, no-regression certificates, product
  behavior claims, official-eval authority, ProgramBench integration,
  future-family selection, release authority, or recursive policy amendment.

## Evidence Source

- merged implementation PR:
  - `#507` (`[codex] Implement BRL-0-A replay manifest validation`)
- arc-completion merge commit:
  - `8931e2fc7c662b12dbb1e2b7e9c6547e280ab306`
- merged-at timestamp:
  - `2026-05-29T14:28:36Z`
- implementation commits integrated by the merge:
  - `f0f6c079db882c69bd6e2aca522fb122d33230c0`
    (`Implement BRL-0-A replay manifest validation`)
  - `5eee7bc40f3b212813cbbb3bbbc9213893c05b50`
    (`Harden BRL-0-A manifest validation`)
- implementation verification recorded before merge:
  - focused behavioral replay lock pytest (`28 passed`)
  - behavioral replay lock Ruff check
  - behavioral replay lock schema export
  - `make check-full`
  - GitHub CI `python`, `lean-formal`, and `web`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=278`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v278_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v278_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v278_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v278/evidence_inputs/metric_key_continuity_assertion_v278.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v278/evidence_inputs/runtime_observability_comparison_v278.json`
  - `BRL-0-A` closeout evidence input:
    `artifacts/agent_harness/v278/evidence_inputs/brl_0a_closeout_evidence_v278.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v278/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS278_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `BRL-0-A` merged on `main` | required | `pass` | PR `#507`, merge commit `8931e2fc7c662b12dbb1e2b7e9c6547e280ab306` |
| Implementation stayed in the behavioral replay lock lane | required | `pass` | merged implementation package is `adeu_behavioral_replay_lock` |
| Selected A surfaces shipped | required | `pass` | six record shapes from the lock shipped |
| Replay manifest validation is structural only | required | `pass` | validation report validates manifest identity, references, hashes, lifecycle, and guardrails only |
| Probe contracts are content-bound | required | `pass` | manifest records bind referenced probe ids to `probe_contract_hash` values |
| Expected observations are content-bound | required | `pass` | manifest records bind expected observation refs to canonical observation hashes |
| Canonicalization profile identity is verified | required | `pass` | supplied profile hash must match the manifest's locked profile hash |
| Suite root is child-hash bound | required | `pass` | suite root includes probe contract and expected observation hashes |
| Non-authority guardrail denies execution/certification authority | required | `pass` | guardrail denies probe execution, replay execution, observation capture, comparison, impact-cone, and no-regression authority |
| A does not implement B/C surfaces | required | `pass` | no replay execution, observation record, regression diff, suite-root report, impact-cone, certificate, staleness, or integration APIs shipped |
| Canonical output hashing is stable | required | `pass` | focused fixtures cover shuffled input determinism and domain-separated hashes |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v278_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v278/evidence_inputs/metric_key_continuity_assertion_v278.json` records exact keyset equality versus `v277` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v278/evidence_inputs/runtime_observability_comparison_v278.json` records `78 ms` baseline, `90 ms` current, `12 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v278_closeout_stop_gate_summary@1",
  "arc": "vNext+278",
  "target_path": "BRL-0-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v277": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 90,
  "runtime_observability_delta_ms": 12
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v277_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v278_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+277","baseline_elapsed_ms":78,"baseline_source":"artifacts/stop_gate/report_v277_closeout.md","current_arc":"vNext+278","current_elapsed_ms":90,"current_source":"artifacts/stop_gate/report_v278_closeout.md","delta_ms":12,"schema":"runtime_observability_comparison@1"}
```

## Slice Evidence Input

```json
{"arc":"vNext+278","candidate_comparison_authority_granted":false,"canonical_hash_stability_verified":true,"canonicalization_hide_protected_surfaces_rejected":true,"canonicalization_profile_hash_bound":true,"closed_slice":"BRL-0-A","duplicate_probe_id_rejected":true,"expected_observation_hashes_bound_to_manifest":true,"expected_observation_provenance_required":true,"family":"BRL-0","fixture_tree_hash_required_for_protected_file_surfaces":true,"future_family_selection_granted":false,"guardrail_authority_grants_rejected":true,"implementation_authority_granted":false,"implementation_commits":["f0f6c079db882c69bd6e2aca522fb122d33230c0","5eee7bc40f3b212813cbbb3bbbc9213893c05b50"],"implementation_package":"packages/adeu_behavioral_replay_lock","impact_cone_selection_authority_granted":false,"manifest_hash_staleness_rejected":true,"merge_commit":"8931e2fc7c662b12dbb1e2b7e9c6547e280ab306","merged_at":"2026-05-29T14:28:36Z","no_regression_certificate_authority_granted":false,"observation_capture_authority_granted":false,"official_eval_authority_granted":false,"product_authority_granted":false,"probe_contract_hashes_bound_to_manifest":true,"probe_execution_authority_granted":false,"probe_generation_authority_granted":false,"pull_request":"https://github.com/LexLattice/adeu-studio/pull/507","reference_schema_root":"packages/adeu_behavioral_replay_lock/schema","replay_execution_authority_granted":false,"runtime_event_stream_path":"artifacts/agent_harness/v278/runtime/evidence/local/urm_events.ndjson","runtime_observability_comparison_path":"artifacts/agent_harness/v278/evidence_inputs/runtime_observability_comparison_v278.json","schema":"brl_0a_closeout_evidence@1","schema_export_verified":true,"secret_like_env_policy_required":true,"selected_record_shapes":["repo_behavioral_replay_manifest@1","repo_behavioral_probe_contract@1","repo_behavioral_canonicalization_profile@1","repo_behavioral_observation_hash@1","repo_behavioral_replay_manifest_validation_report@1","repo_behavioral_replay_lock_non_authority_guardrail@1"],"suite_root_hash_child_hash_binding_enforced":true,"test_reference_path":"packages/adeu_behavioral_replay_lock/tests/test_brl_0a.py","unknown_owner_label_local_extension_required":true,"verification_commands":[".venv/bin/python -m pytest packages/adeu_behavioral_replay_lock/tests -q",".venv/bin/python -m ruff check packages/adeu_behavioral_replay_lock",".venv/bin/python -m adeu_behavioral_replay_lock.export_schema","make check-full","GitHub CI: python, lean-formal, web","make arc-closeout-check ARC=278"],"worker_dispatch_authority_granted":false}
```

## Recommendation

- gate decision:
  - `BRL_0A_REPLAY_MANIFEST_VALIDATION_COMPLETE_ON_MAIN`
- rationale:
  - `v278` closes the bounded `BRL-0-A` replay manifest, probe contract,
    canonicalization profile, expected observation hash, validation report, and
    non-authority guardrail seam on `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_behavioral_replay_lock`)
    - six deterministic A-level record surfaces
    - probe contracts and expected observations are content-hash bound
    - canonicalization profiles are manifest-hash checked
    - suite-root and manifest hashes reject stale child rows
    - validation remains structural and non-executing
    - no replay execution, observation capture, candidate comparison,
      impact-cone selection, no-regression certificate, product authority,
      official-eval authority, or future-family selection shipped
  - deterministic closeout artifacts preserve the frozen stop-gate schema and
    exact metric keyset.
- family status:
  - `BRL-0` remains open for `BRL-0-B`.
