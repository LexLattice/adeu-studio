# Draft Stop-Gate Decision (Post vNext+197)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md`

Status: draft decision note (post-closeout capture, April 26, 2026 UTC).

Authority layer: closeout evidence on `main` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS197.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v197_closeout_stop_gate_decision_on_main",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+197` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md`.
- This note captures bounded `V71-A` closeout evidence only on `main`; it does
  not authorize final ratification records, settlement records, dissent
  registers, amendment scope, post-ratification handoff, `V72` contained
  integration, commit / merge / release authority, `V73` outcome review, `V74`
  operator or product projection, `V75` dispatch, runtime permission, or
  external contest participation.
- Canonical `V71-A` shipment in `v197` is carried by bounded
  `adeu_repo_description` candidate ratification request, ratification
  authority profile, and ratification request-scope boundary models,
  validators, schema exports, deterministic `vnext_plus197` reference and
  reject fixtures, and canonical
  `v71a_candidate_ratification_request_evidence@1` evidence input under
  `artifacts/agent_harness/v197/evidence_inputs/`.

## Evidence Source

- merged implementation PR:
  - `#424` (`Implement V71-A ratification request surfaces`)
- arc-completion merge commit:
  - `bd5c3389f617ef725a88a2fa98c7e89c4cf30f15`
- merged-at timestamp:
  - `2026-04-26T13:59:02Z`
- implementation commits integrated by the merge:
  - `ab6395f9ce84c19ab03ce0e5917194b039586cb1`
    (`Implement V71-A ratification request surfaces`)
  - `bd937b455f513a4fcdddc04306958152bab4ef4f`
    (`Harden CI push range detection`)
- implementation verification recorded before PR / update:
  - focused pytest
  - `make check`
  - final workflow-only CI hardening checked with narrower local syntax review
    at maintainer request
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=197`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v197_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v197_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v197_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v197/evidence_inputs/metric_key_continuity_assertion_v197.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v197/evidence_inputs/runtime_observability_comparison_v197.json`
  - `V71-A` ratification request evidence input:
    `artifacts/agent_harness/v197/evidence_inputs/v71a_candidate_ratification_request_evidence_v197.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v197/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS197_EDGES.md`

## Exit-Criteria Check (vNext+197)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V71-A` merged on `main` | required | `pass` | PR `#424`, merge commit `bd5c3389f617ef725a88a2fa98c7e89c4cf30f15` |
| Implementation stayed in the repo-description lane | required | `pass` | merged implementation package is `adeu_repo_description` |
| Selected request / authority / request-scope surfaces shipped | required | `pass` | `repo_candidate_ratification_request@1`, `repo_ratification_authority_profile@1`, and `repo_ratification_request_scope_boundary@1` |
| V70-C summary and handoff substrate is consumed, not recreated | required | `pass` | request rows reference released summary and handoff refs |
| Ratification source rows are explicit | required | `pass` | request rows require non-empty source refs |
| Authority actor and authority grant source stay separated | required | `pass` | authority profile model separates actor kind from grant source kind |
| Model, tool, support, and transcript self-ratification are blocked | required | `pass` | reject fixtures cover model self-ratification, tool pass as proof, and support doc as authority |
| Blocked handoffs cannot become eligible requests | required | `pass` | blocked-handoff-marked-eligible reject fixture passed |
| Product wedge remains future-family routed | required | `pass` | product-wedge-to-`V71` reject fixture passed |
| Request-scope boundary cannot authorize downstream work | required | `pass` | release / downstream authority reject fixtures passed |
| `V71-B` and `V71-C` stayed deferred | required | `pass` | no final ratification, settlement, dissent, amendment-scope, or post-ratification handoff surface shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v197_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v197/evidence_inputs/metric_key_continuity_assertion_v197.json` records exact keyset equality versus `v196` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v197/evidence_inputs/runtime_observability_comparison_v197.json` records `70 ms` baseline, `78 ms` current, `8 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v197_closeout_stop_gate_summary@1",
  "arc": "vNext+197",
  "target_path": "V71-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v196": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 78,
  "runtime_observability_delta_ms": 8
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v196_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v197_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+196","baseline_elapsed_ms":70,"baseline_source":"artifacts/stop_gate/report_v196_closeout.md","current_arc":"vNext+197","current_elapsed_ms":78,"current_source":"artifacts/stop_gate/report_v197_closeout.md","delta_ms":8,"notes":"v197 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while closing the bounded V71-A candidate ratification request starter slice on main: repo-owned adeu_repo_description package only, three repo_* V71-A surfaces, explicit ratification source rows, authority actor/source separation, request-scope boundaries, source-bound consumption of V70-C summary and handoff substrate, and no final ratification, settlement, amendment scope, V72 integration, product authorization, release authority, runtime permission, or dispatch widening.","schema":"runtime_observability_comparison@1"}
```

## V71A Candidate Ratification Request Evidence

```json
{"authority_actor_and_grant_source_split_enforced":true,"authority_profile_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_ratification_authority_profile.v1.json","authority_profile_mirror_schema_path":"spec/repo_ratification_authority_profile.schema.json","authority_profile_reference_fixture_path":"apps/api/fixtures/repo_description/vnext_plus197/repo_ratification_authority_profile_v197_reference.json","blocked_handoff_marked_eligible_rejected":true,"ci_checks":["python","web","lean-formal"],"ci_push_range_hardening_commit":"bd937b455f513a4fcdddc04306958152bab4ef4f","consumed_record_shapes":["repo_candidate_review_classification_summary@1","repo_candidate_pre_ratification_handoff@1"],"contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md#machine-checkable-contract","evidence_input_path":"artifacts/agent_harness/v197/evidence_inputs/v71a_candidate_ratification_request_evidence_v197.json","export_test_reference_path":"packages/adeu_repo_description/tests/test_repo_description_export_schema.py","implementation_commit":"ab6395f9ce84c19ab03ce0e5917194b039586cb1","implementation_packages":["adeu_repo_description"],"implementation_source_path":"packages/adeu_repo_description/src/adeu_repo_description/candidate_ratification_review.py","local_full_python_gate":"make check before CI workflow-only hardening; final local check intentionally narrower at maintainer request","merge_commit":"bd5c3389f617ef725a88a2fa98c7e89c4cf30f15","merged_at":"2026-04-26T13:59:02Z","merged_pr":"#424","metric_key_continuity_assertion_path":"artifacts/agent_harness/v197/evidence_inputs/metric_key_continuity_assertion_v197.json","model_self_ratification_rejected":true,"notes":"v197 evidence pins the bounded V71-A closeout seam on main: ratification request rows consume released V70-C summary/handoff substrate, source rows bind request evidence explicitly, authority profiles separate actors from grant sources, request-scope boundaries remain non-downstream-authorizing, and all outputs remain requests or deferrals for later V71-B review rather than final ratification, settlement, adoption, integration, product authorization, release authority, runtime permission, or dispatch.","package_export_surface_path":"packages/adeu_repo_description/src/adeu_repo_description/__init__.py","product_wedge_to_v71_rejected":true,"ratification_source_rows_required":true,"reject_fixture_dir":"apps/api/fixtures/repo_description/vnext_plus197","request_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_candidate_ratification_request.v1.json","request_mirror_schema_path":"spec/repo_candidate_ratification_request.schema.json","request_reference_fixture_path":"apps/api/fixtures/repo_description/vnext_plus197/repo_candidate_ratification_request_v197_reference.json","request_rows_source_refs_non_empty_enforced":true,"request_scope_allows_release_rejected":true,"request_scope_boundary_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_ratification_request_scope_boundary.v1.json","request_scope_boundary_mirror_schema_path":"spec/repo_ratification_request_scope_boundary.schema.json","request_scope_boundary_reference_fixture_path":"apps/api/fixtures/repo_description/vnext_plus197/repo_ratification_request_scope_boundary_v197_reference.json","runtime_event_stream_path":"artifacts/agent_harness/v197/runtime/evidence/local/urm_events.ndjson","runtime_observability_comparison_path":"artifacts/agent_harness/v197/evidence_inputs/runtime_observability_comparison_v197.json","schema":"v71a_candidate_ratification_request_evidence@1","schema_export_source_path":"packages/adeu_repo_description/src/adeu_repo_description/export_schema.py","selected_product_authorization_for_v71a":false,"selected_record_shapes":["repo_candidate_ratification_request@1","repo_ratification_authority_profile@1","repo_ratification_request_scope_boundary@1"],"selected_runtime_permission_or_dispatch_for_v71a":false,"selected_v71b_ratification_record_for_v71a":false,"selected_v71b_settlement_or_dissent_for_v71a":false,"selected_v71c_amendment_scope_or_handoff_for_v71a":false,"selected_v72_integration_for_v71a":false,"support_doc_as_ratification_authority_rejected":true,"test_reference_path":"packages/adeu_repo_description/tests/test_candidate_ratification_review_v71a.py","tool_pass_as_ratification_rejected":true,"v70c_handoff_refs_required":true,"v70c_summary_refs_required":true,"v71a_final_ratification_rejected":true}
```

## Recommendation (Post v197)

- gate decision:
  - `V71A_CANDIDATE_RATIFICATION_REQUEST_AUTHORITY_SCOPE_COMPLETE_ON_MAIN`
- rationale:
  - `v197` closes the bounded `V71-A` request / authority-profile /
    request-scope starter seam on `main`;
  - the shipped slice stayed properly bounded:
    - same repo-owned implementation package (`adeu_repo_description`) only
    - three `repo_*` V71-A record surfaces
    - source-bound consumption of released `V70-C` summary and handoff rows
    - explicit ratification source rows
    - authority actor/source separation
    - request-scope boundaries that forbid downstream implementation, release,
      product, runtime, and dispatch roles
    - no final ratification, settlement, dissent, amendment scope,
      post-ratification handoff, integration, product authorization, release
      authority, runtime permission, or dispatch widening
  - stop-gate schema-family and metric-key continuity stayed intact.
  - runtime observability remained informational-only.
  - `V71-A` is now closed on `main`.
  - `V71` remains open for the reviewed `V71-B` lifecycle slice.
  - the next selected starter, if drafted, should be `V71-B`: settlement,
    ratification / rejection / deferral records, and dissent preservation.
