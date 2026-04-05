# Draft Stop-Gate Decision (Post vNext+134)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS134.md`

Status: draft decision note (post-hoc closeout capture, April 5, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS134.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v134_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+134` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS134.md`.
- This note captures bounded `V44-D` probe-library widening evidence only; it does
  not authorize recursive-depth assessment, model-profile aggregation, benchmark
  scoring, or benchmark-family projection by itself.
- Canonical `V44-D` release in `v134` is carried by the shipped
  `packages/adeu_reasoning_assessment` package additions, authoritative and mirrored
  `adeu_reasoning_probe_suite@1` schema export, deterministic `v44d` fixtures/tests,
  and the canonical `v44d_reasoning_probe_suite_evidence@1` evidence input under
  `artifacts/agent_harness/v134/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md` now marks `V44-D`
  closed on `main` and advances the branch-local default next path to `V44-E`; it
  does not complete the whole `V44` family by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#356` (`feat(v134): add reasoning probe suite library`)
- arc-completion merge commit: `f38148b700bf95b3b74fff802197c2789bb51a71`
- merged-at timestamp: `2026-04-05T14:51:45Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v134_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v134_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v134_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v134/evidence_inputs/metric_key_continuity_assertion_v134.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v134/evidence_inputs/runtime_observability_comparison_v134.json`
  - `V44-D` release evidence input:
    `artifacts/agent_harness/v134/evidence_inputs/v44d_reasoning_probe_suite_evidence_v134.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS134_EDGES.md`

## Exit-Criteria Check (vNext+134)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V44-D` merged with green CI | required | `pass` | PR `#356`, merge commit `f38148b700bf95b3b74fff802197c2789bb51a71`, checks `python/web/lean-formal = pass` |
| `packages/adeu_reasoning_assessment` remains the only active implementation package for the slice | required | `pass` | merged diff limited live implementation ownership to `packages/adeu_reasoning_assessment` only |
| Authoritative and mirror probe-suite schemas ship deterministically | required | `pass` | `packages/adeu_reasoning_assessment/schema/adeu_reasoning_probe_suite.v1.json`, `spec/adeu_reasoning_probe_suite.schema.json`, and schema export replay coverage |
| Released suite manifest validates and carries first-class member semantics across all four starter classes | required | `pass` | `reference_reasoning_probe_suite.json`, released `ReasoningProbeSuite` model law, and builder replay coverage |
| Positive widening references validate for branching, local repair, and both frozen invariance kinds | required | `pass` | committed `v44d` probe/trace fixtures plus `test_reasoning_assessment_probe_library.py` coverage |
| Local repair remains bounded to `local_only` and non-local rewrite fails closed | required | `pass` | released `repair_locality_posture` law, `reject_reasoning_template_probe_non_local_repair.json`, and helper validation coverage |
| Member-level taxonomy and differential compatibility remain explicit and replay deterministically | required | `pass` | `reference_v44d_taxonomy_compatibility_replay.json`, `reference_v44d_differential_compatibility_replay.json`, and suite-member compatibility checks |
| Unknown surface-variation kinds and invalid invariance anchors fail closed | required | `pass` | review hardening in `cc45feee9b5d754404ff59389105e63db8087812`, `reject_reasoning_template_probe_invariance_missing_anchor.json`, and the invalid-variation regression |
| No profile, benchmark, or recursive-depth fields ship in `V44-D` | required | `pass` | released schema/package exports contain widened-library surfaces only |
| Root `spec/` mirrors are claimed in docs and actually shipped | required | `pass` | merged `spec/adeu_reasoning_probe_suite.schema.json` and updated `spec/adeu_reasoning_template_probe.schema.json` |
| Local targeted validation passed for the touched package lane | required | `pass` | PR lane ran `ruff` plus `pytest packages/adeu_reasoning_assessment/tests` (`31 passed`) |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v134_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v134/evidence_inputs/metric_key_continuity_assertion_v134.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v134/evidence_inputs/runtime_observability_comparison_v134.json` |

## Stop-Gate Summary

```json
{
  "schema": "v134_closeout_stop_gate_summary@1",
  "arc": "vNext+134",
  "target_path": "V44-D",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v133": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 134,
  "runtime_observability_delta_ms": 8
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v133_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v134_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+133","current_arc":"vNext+134","baseline_source":"artifacts/stop_gate/report_v133_closeout.md","current_source":"artifacts/stop_gate/report_v134_closeout.md","baseline_elapsed_ms":126,"current_elapsed_ms":134,"delta_ms":8,"notes":"v134 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V44-D probe-library widening lane: one repo-owned adeu_reasoning_assessment package only, one released adeu_reasoning_probe_suite@1 contract plus deterministic build_reasoning_probe_suite helper, first-class suite_members over decomposition branching local-repair and invariance classes, explicit member-level consumer compatibility posture, positive invariance coverage for paraphrase_preserving and presentation_shift_preserving, compatibility replay through released V44-B taxonomy and released V44-C differential, fail-closed rejection for missing procedure-preservation anchors and non-local repair rewrite posture, and no profile aggregation recursive-depth release or V46 benchmark projection surfaces."}
```

## V44D Reasoning Probe Suite Evidence

```json
{"schema":"v44d_reasoning_probe_suite_evidence@1","evidence_input_path":"artifacts/agent_harness/v134/evidence_inputs/v44d_reasoning_probe_suite_evidence_v134.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS134.md#v134-continuation-contract-machine-checkable","merged_pr":"#356","merge_commit":"f38148b700bf95b3b74fff802197c2789bb51a71","implementation_packages":["adeu_reasoning_assessment"],"reasoning_assessment_package_root":"packages/adeu_reasoning_assessment","reasoning_assessment_pyproject_path":"packages/adeu_reasoning_assessment/pyproject.toml","reasoning_assessment_models_source_path":"packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/models.py","reasoning_assessment_probe_library_source_path":"packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/probe_library.py","reasoning_assessment_export_schema_source_path":"packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/export_schema.py","reasoning_assessment_package_init_source_path":"packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/__init__.py","reasoning_probe_suite_authoritative_schema_path":"packages/adeu_reasoning_assessment/schema/adeu_reasoning_probe_suite.v1.json","reasoning_probe_suite_mirror_schema_path":"spec/adeu_reasoning_probe_suite.schema.json","reference_suite_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_reasoning_probe_suite.json","branching_probe_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_reasoning_template_probe_branching.json","branching_trace_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_structural_reasoning_trace_branching.json","local_repair_probe_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_reasoning_template_probe_local_repair.json","local_repair_trace_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_structural_reasoning_trace_local_repair.json","invariance_paraphrase_probe_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_reasoning_template_probe_invariance_paraphrase.json","invariance_paraphrase_trace_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_structural_reasoning_trace_invariance_paraphrase.json","invariance_presentation_probe_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_reasoning_template_probe_invariance_presentation_shift.json","invariance_presentation_trace_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_structural_reasoning_trace_invariance_presentation_shift.json","suite_matrix_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_v44d_suite_matrix.json","taxonomy_compatibility_replay_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_v44d_taxonomy_compatibility_replay.json","differential_compatibility_replay_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reference_v44d_differential_compatibility_replay.json","reject_invariance_anchor_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reject_reasoning_template_probe_invariance_missing_anchor.json","reject_non_local_repair_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44d/reject_reasoning_template_probe_non_local_repair.json","test_reference_paths":["packages/adeu_reasoning_assessment/tests/test_reasoning_assessment_models.py","packages/adeu_reasoning_assessment/tests/test_reasoning_assessment_probe_library.py"],"template_class_vocabulary":["lane_preserving_decomposition","branching_under_uncertainty","local_repair_continuation","invariance_under_surface_variation"],"surface_variation_kind_vocabulary":["paraphrase_preserving","presentation_shift_preserving"],"repair_locality_posture_vocabulary":["local_only"],"member_level_consumer_compatibility_required":true,"suite_members_first_class_required":true,"review_hardening_commit":"cc45feee9b5d754404ff59389105e63db8087812","metric_key_continuity_assertion_path":"artifacts/agent_harness/v134/evidence_inputs/metric_key_continuity_assertion_v134.json","runtime_observability_comparison_path":"artifacts/agent_harness/v134/evidence_inputs/runtime_observability_comparison_v134.json","runtime_event_stream_path":"artifacts/agent_harness/v134/runtime/evidence/local/urm_events.ndjson","notes":"v134 evidence pins the released V44-D probe-library widening seam on main: one repo-owned adeu_reasoning_assessment package only, one released adeu_reasoning_probe_suite@1 contract and deterministic build_reasoning_probe_suite helper, first-class suite_members over decomposition branching local_repair and invariance classes, explicit member-level taxonomy versus differential compatibility posture, positive invariance coverage for both frozen surface-variation kinds, taxonomy replay and differential replay over released V44-B and V44-C consumers respectively, fail-closed rejection for invalid procedure-preservation anchors and non-local repair rewrite posture, and no profile aggregation recursive-depth or V46 benchmark projection surfaces."}
```

## Recommendation (Post v134)

- gate decision:
  - `V44D_PROBE_LIBRARY_WIDENING_COMPLETE_ON_MAIN`
  - `V44_REASONING_ASSESSMENT_FAMILY_CONTINUES_WITH_V44E_NEXT`
- rationale:
  - `v134` closes the bounded probe-library widening seam on `main` only after the
    contract-first `V44-A` substrate, the taxonomy-first `V44-B` lane, and the
    diagnosis-first `V44-C` lane were already released.
  - the released slice stays narrow and evidentiary: one package, one suite contract,
    deterministic widening helper, first-class suite-membership semantics, and no
    profile, ranking, or benchmark surfaces.
  - the widening is real law rather than summary prose: the shipped suite and fixtures
    now exercise branching, local repair, and both frozen invariance kinds while
    preserving explicit procedure anchors and local-only repair posture.
  - review hardening stayed bounded and fail-closed: `cc45feee9b5d754404ff59389105e63db8087812`
    removed redundant suite validation and added explicit unsupported
    `surface_variation_kind` rejection.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability regressed informationally by `+8 ms` versus the `v133`
    baseline, but the stop-gate remained fully passing and stable.
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md` should now be read with `V44-D` closed on
    `main` and `V44-E` as the branch-local default next path.
