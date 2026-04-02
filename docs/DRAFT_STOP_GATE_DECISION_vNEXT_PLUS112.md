# Draft Stop-Gate Decision (Post vNext+112)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS112.md`

Status: draft decision note (post-hoc closeout capture, April 2, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS112.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v112_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+112` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS112.md`.
- This note captures bounded `V48-A` binding-profile evidence only; it does not
  authorize taskpack manifest or bundle emission, signature verification release,
  worker attestation release, post-run conformance release, multi-worker topology,
  repo-wide taskpack generation, execution posture expansion, approval posture,
  waiver issuance, or deferral issuance by itself.
- Canonical `V48-A` release in v112 is carried by the shipped `adeu_agent_harness`
  source, schema-export, deterministic fixture, and targeted test surfaces plus the
  canonical `v48a_policy_to_taskpack_binding_evidence@1` evidence input under
  `artifacts/agent_harness/v112/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#334` (`V48-A: add taskpack binding profile`)
- arc-completion merge commit: `2d018edd00e09e4c85bbb42b924a02d09de21844`
- merged-at timestamp: `2026-04-02T18:19:33Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v112_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v112_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v112_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v112/evidence_inputs/metric_key_continuity_assertion_v112.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v112/evidence_inputs/runtime_observability_comparison_v112.json`
  - `V48-A` release evidence input:
    `artifacts/agent_harness/v112/evidence_inputs/v48a_policy_to_taskpack_binding_evidence_v112.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v112/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS112_EDGES.md`

## Exit-Criteria Check (vNext+112)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V48-A` merged with green CI | required | `pass` | PR `#334`, merge commit `2d018edd00e09e4c85bbb42b924a02d09de21844`, checks `python/web/lean-formal = pass` |
| Released taskpack binding profile ships with authoritative/mirror schema parity | required | `pass` | `packages/adeu_agent_harness/schema/anm_taskpack_binding_profile.v1.json`, `spec/anm_taskpack_binding_profile.schema.json`, and parity coverage in `packages/adeu_agent_harness/tests/test_taskpack_binding_export_schema.py` |
| Accepted binding fixture carries exactly one policy source, one scope source, one scope-binding entry, one worker subject, and one binding subject | required | `pass` | committed reference fixture `packages/adeu_agent_harness/tests/fixtures/v48a/reference_anm_taskpack_binding_profile.json`, cardinality validation in `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`, and tests `test_v48a_reference_profile_replays_deterministically`, `test_v48a_model_accepts_committed_reference_payload`, and `test_v48a_rejects_multiple_policy_sources` |
| Admitted `V47-E` carrier rows resolve to exactly one bound released `D-IR` clause and do not self-authorize apart from that clause lineage | required | `pass` | `policy_authority_clause_ref` carried in the committed profile fixture, released-row validation in `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`, and deterministic replay in `test_v48a_reference_profile_replays_deterministically` |
| Admitted `V45-F` binding entries resolve to the same scope surface and binding subject while remaining admission-only | required | `pass` | `V45-F` admission checks in `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`, committed profile fixture, reject fixture `packages/adeu_agent_harness/tests/fixtures/v48a/reject_scope_binding_entry_mismatch_spec.json`, and test `test_v48a_rejects_mismatched_scope_binding_entry` |
| Taskpack-surface mappings remain exact and kernel-shaped for allowlist, forbidden, commands, and evidence slots | required | `pass` | frozen contract markers in `packages/adeu_agent_harness/tests/test_taskpack_binding_export_schema.py`, released schema pair, committed reference fixtures, and export-shape assertions in `test_exported_schema_has_stable_contract_markers` |
| Contradictory projections fail closed rather than selecting precedence | required | `pass` | projection-conflict validation in `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`, reject fixture `packages/adeu_agent_harness/tests/fixtures/v48a/reject_projection_conflict_spec.json`, and test `test_v48a_rejects_projection_conflicts` |
| Prompt/chat/`AGENTS.md` posture remains projection-only and prompt-boundary conflict fails closed | required | `pass` | prompt-authority validation in `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`, reject fixture `packages/adeu_agent_harness/tests/fixtures/v48a/reject_prompt_authority_drift_spec.json`, and test `test_v48a_rejects_prompt_authority_drift` |
| Unsupported command/evidence payload drift fails closed instead of leaking raw type errors | required | `pass` | command projection validation in `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py` and test `test_v48a_rejects_malformed_command_env_overrides_fail_closed` |
| Schema export remains free of absolute path material and replay-clean on rerun | required | `pass` | path guard in `packages/adeu_agent_harness/src/adeu_agent_harness/export_schema.py` and tests `test_schema_export_rerun_is_clean_and_deterministic`, `test_exported_schema_contains_no_absolute_path_material`, and `test_absolute_path_guard_rejects_single_backslash_windows_paths` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v112_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v112/evidence_inputs/metric_key_continuity_assertion_v112.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v112/evidence_inputs/runtime_observability_comparison_v112.json` |

## Stop-Gate Summary

```json
{
  "schema": "v112_closeout_stop_gate_summary@1",
  "arc": "vNext+112",
  "target_path": "V48-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v111": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 94,
  "runtime_observability_delta_ms": -17
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v111_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v112_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+111","current_arc":"vNext+112","baseline_source":"artifacts/stop_gate/report_v111_closeout.md","current_source":"artifacts/stop_gate/report_v112_closeout.md","baseline_elapsed_ms":111,"current_elapsed_ms":94,"delta_ms":-17,"notes":"v112 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V48-A harness bridge starter: one canonical anm_taskpack_binding_profile@1, exactly one released V47-E policy carrier resolving to one bound D-IR clause, exactly one released V45 scope surface with one admitting V45-F binding entry, exact allowlist/forbidden/command/evidence-slot projection categories, kernel-shaped command and evidence carriers, fail-closed projection-conflict handling, fail-closed prompt-boundary drift handling, and retained non-executive single-worker posture."}
```

## V48A Policy-To-Taskpack Binding Evidence

```json
{"schema":"v48a_policy_to_taskpack_binding_evidence@1","evidence_input_path":"artifacts/agent_harness/v112/evidence_inputs/v48a_policy_to_taskpack_binding_evidence_v112.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS112.md#v112-continuation-contract-machine-checkable","merged_pr":"#334","merge_commit":"2d018edd00e09e4c85bbb42b924a02d09de21844","implementation_packages":["adeu_agent_harness"],"binding_profile_implementation_source_path":"packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py","binding_profile_export_source_path":"packages/adeu_agent_harness/src/adeu_agent_harness/export_schema.py","binding_profile_authoritative_schema_path":"packages/adeu_agent_harness/schema/anm_taskpack_binding_profile.v1.json","binding_profile_mirror_schema_path":"spec/anm_taskpack_binding_profile.schema.json","test_reference_paths":["packages/adeu_agent_harness/tests/test_taskpack_binding.py","packages/adeu_agent_harness/tests/test_taskpack_binding_export_schema.py","packages/adeu_agent_harness/tests/test_taskpack_compile.py"],"accepted_binding_spec_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48a/reference_taskpack_binding_spec.json","accepted_profile_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48a/reference_anm_taskpack_binding_profile.json","rejected_multiple_policy_sources_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48a/reject_multiple_policy_sources_spec.json","rejected_scope_binding_entry_mismatch_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48a/reject_scope_binding_entry_mismatch_spec.json","rejected_projection_conflict_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48a/reject_projection_conflict_spec.json","rejected_prompt_authority_drift_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48a/reject_prompt_authority_drift_spec.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v112/evidence_inputs/metric_key_continuity_assertion_v112.json","runtime_observability_comparison_path":"artifacts/agent_harness/v112/evidence_inputs/runtime_observability_comparison_v112.json","runtime_event_stream_path":"artifacts/agent_harness/v112/runtime/evidence/local/urm_events.ndjson","notes":"v112 evidence pins the released V48-A bridge starter on main: one canonical anm_taskpack_binding_profile@1, exact single-policy/single-scope/single-worker cardinality, one admitted V47-E policy carrier resolving to one bound D-IR clause, one admitted V45 scope surface plus one V45-F binding entry with admission-only posture, exact allowlist/forbidden/command/evidence-slot projection categories, kernel-shaped command and evidence carriers, fail-closed projection conflict handling, fail-closed prompt authority drift handling, fail-closed malformed command env validation, and retained non-executive no-manifest/no-attestation/no-conformance posture."}
```

## Recommendation (Post v112)

- gate decision:
  - `V48A_POLICY_TO_TASKPACK_BINDING_COMPLETE_ON_MAIN`
  - `V48_POLICY_TO_TASKPACK_AND_WORKER_ENFORCEMENT_BRANCH_ACTIVE_ON_MAIN`
- rationale:
  - v112 closes the bounded `V48-A` policy/scope-to-taskpack binding seam on `main`
    by taking released `V45` scope lineage, released `V47-E` policy-consumer lineage,
    and released harness kernel categories and binding them together in one typed
    profile without widening into compilation, attestation, or conformance lanes.
  - the shipped slice is bridge-first and non-orchestrational: it does not reopen
    descriptive semantics, ANM semantics, generic taskpack compiler semantics,
    worker-run attestation, post-run conformance, or multi-worker topology.
  - the admitted `V47-E` row is now an explicit carrier only, with the bound released
    `D-IR` clause kept visible as upstream policy authority.
  - the admitted `V45-F` entry now remains an explicit admission-only prerequisite for
    scope consumption rather than a hidden execution-authorizing surface.
  - the shipped mapping categories remain exact and kernel-shaped, with contradictory
    allowlist / forbidden / command / evidence-slot projections rejected fail closed
    rather than by local precedence.
  - prompt text, chat prose, and `AGENTS.md` are now explicit projection/context only
    when a typed binding profile exists, and prompt-boundary conflicts are fail closed.
  - authoritative schema, mirrored export, committed fixtures, and targeted tests stay
    in parity for the released binding profile surface.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`-17 ms` vs v111 baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md` now records `V48-A` as closed on `main` and
    advances the branch-local default next path to `V48-B` / `vNext+113`.
