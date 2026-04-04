# Draft Stop-Gate Decision (Post vNext+127)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS127.md`

Status: draft decision note (post-hoc closeout capture, April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS127.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v127_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+127` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS127.md`.
- This note captures bounded `V52-A` package evidence only; it does not authorize the
  later mock workbench route, live worker bridge, advanced visualization seam, or
  imported overlay precedent by itself.
- Canonical `V52-A` release in `v127` is carried by the shipped
  `adeu_paper_semantics` package source, committed deterministic `v52a` fixtures,
  package tests, and the canonical `v52a_paper_semantic_contract_evidence@1`
  evidence input under `artifacts/agent_harness/v127/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` now marks `V52-A`
  closed on `main` and advances the branch-local default next path to `V52-B`; it
  does not select the `V52-B` workbench seam by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#349` (`feat(v127): add paper semantics contracts`)
- arc-completion merge commit: `5f923ae849d15315951d881929c443615da2cba2`
- merged-at timestamp: `2026-04-04T15:32:56Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v127_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v127_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v127_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v127/evidence_inputs/metric_key_continuity_assertion_v127.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v127/evidence_inputs/runtime_observability_comparison_v127.json`
  - `V52-A` release evidence input:
    `artifacts/agent_harness/v127/evidence_inputs/v52a_paper_semantic_contract_evidence_v127.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v127/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS127_EDGES.md`

## Exit-Criteria Check (vNext+127)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V52-A` merged with green CI | required | `pass` | PR `#349`, merge commit `5f923ae849d15315951d881929c443615da2cba2`, checks `python/web/lean-formal = pass` |
| Repo-owned `adeu_paper_semantics` package remains the sole live owner of the shipped `V52-A` code | required | `pass` | `packages/adeu_paper_semantics/pyproject.toml`, `packages/adeu_paper_semantics/src/adeu_paper_semantics/*.py`, and absence of overlay import into live package paths |
| The first release stays bounded to `paper.abstract` and `pasted.paragraph` only | required | `pass` | `SourceArtifactKind` in `models.py`, committed reference fixtures, and absence of `paper.abstract_digest` or full-paper widening |
| `V52-A` reuses released `V49` canonical hash law while keeping projection/support fields out of semantic identity | required | `pass` | `sha256_canonical_json` reuse from `adeu_semantic_forms`, `IDENTITY_FIELD_NAMES`, `PROJECTION_FIELD_NAMES`, and mutation fixture tests |
| Source text plus explicit span anchors remain authoritative and interpretation stays advisory-only | required | `pass` | `SOURCE_AUTHORITY_POSTURE`, `INTERPRETATION_AUTHORITY_POSTURE`, anchored-span validation, and committed artifact fixtures |
| One contract-only worker request surface ships without authorizing live workbench or worker execution | required | `pass` | `PaperSemanticWorkerRequest`, committed worker-request fixtures, and absence of route/domain bridge code |
| Bidirectional claim/fragment ownership now fails closed instead of allowing contradictory ownership | required | `pass` | `claim lane_fragment_ids must exactly match owned fragment claim_id bindings` validation and `test_claim_fragment_ownership_must_be_bidirectionally_consistent` |
| Deterministic accepted/reject fixtures replay exactly and prove projection-only vs identity-bearing changes | required | `pass` | committed `v52a` fixture pack under `packages/adeu_paper_semantics/tests/fixtures/v52a/` and `test_paper_semantics_models.py` |
| The package is bootstrapped into the repo Python environment so full-suite CI can import it without local `PYTHONPATH` hacks | required | `pass` | `Makefile` editable-install wiring for `packages/adeu_paper_semantics[dev]` |
| No live `/papers/semantic-workbench` route, worker bridge, or advanced visualization ships in this slice | required | `pass` | shipped scope limited to package/source/tests/fixtures and absence of `apps/web` / `urm_domain_*` widening in the merged diff |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v127_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v127/evidence_inputs/metric_key_continuity_assertion_v127.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v127/evidence_inputs/runtime_observability_comparison_v127.json` |

## Stop-Gate Summary

```json
{
  "schema": "v127_closeout_stop_gate_summary@1",
  "arc": "vNext+127",
  "target_path": "V52-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v126": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 119,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v126_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v127_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+126","current_arc":"vNext+127","baseline_source":"artifacts/stop_gate/report_v126_closeout.md","current_source":"artifacts/stop_gate/report_v127_closeout.md","baseline_elapsed_ms":119,"current_elapsed_ms":119,"delta_ms":0,"notes":"v127 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V52-A paper semantic contract lane: one repo-owned adeu_paper_semantics package, one bounded source-artifact family over paper.abstract and pasted.paragraph only, one explicit source-authority posture plus advisory-only interpretation posture, first-class typed models for source artifacts, spans, claims, lane fragments, inference bridges, diagnostics, projections, top-level artifacts, and worker requests, released V49 canonical hash-law reuse with explicit identity-vs-projection split, deterministic accepted/reject fixture replay, fail-closed span-anchor and request-posture validation, bidirectional claim/fragment ownership enforcement, Makefile bootstrap wiring for the package, and no live workbench route, worker bridge, or advanced visualization widening."}
```

## V52A Paper Semantic Contract Evidence

```json
{"schema":"v52a_paper_semantic_contract_evidence@1","evidence_input_path":"artifacts/agent_harness/v127/evidence_inputs/v52a_paper_semantic_contract_evidence_v127.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS127.md#v127-continuation-contract-machine-checkable","merged_pr":"#349","merge_commit":"5f923ae849d15315951d881929c443615da2cba2","implementation_packages":["adeu_paper_semantics"],"paper_semantics_package_root":"packages/adeu_paper_semantics","paper_semantics_pyproject_path":"packages/adeu_paper_semantics/pyproject.toml","paper_semantics_models_source_path":"packages/adeu_paper_semantics/src/adeu_paper_semantics/models.py","paper_semantics_package_init_source_path":"packages/adeu_paper_semantics/src/adeu_paper_semantics/__init__.py","repo_bootstrap_makefile_path":"Makefile","test_reference_paths":["packages/adeu_paper_semantics/tests/test_paper_semantics_models.py"],"reference_worker_request_fixture_paths":["packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_worker_request_abstract.json","packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_worker_request_paragraph.json"],"reference_artifact_fixture_paths":["packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_abstract.json","packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_paragraph.json"],"identity_mutation_fixture_path":"packages/adeu_paper_semantics/tests/fixtures/v52a/mutation_paper_semantic_artifact_identity_change.json","projection_only_mutation_fixture_path":"packages/adeu_paper_semantics/tests/fixtures/v52a/mutation_paper_semantic_artifact_projection_only.json","reject_fixture_paths":["packages/adeu_paper_semantics/tests/fixtures/v52a/reject_invalid_diagnostic_kind.json","packages/adeu_paper_semantics/tests/fixtures/v52a/reject_malformed_span_anchor.json","packages/adeu_paper_semantics/tests/fixtures/v52a/reject_invalid_worker_request_posture.json"],"released_semantic_forms_package_root":"packages/adeu_semantic_forms","metric_key_continuity_assertion_path":"artifacts/agent_harness/v127/evidence_inputs/metric_key_continuity_assertion_v127.json","runtime_observability_comparison_path":"artifacts/agent_harness/v127/evidence_inputs/runtime_observability_comparison_v127.json","runtime_event_stream_path":"artifacts/agent_harness/v127/runtime/evidence/local/urm_events.ndjson","notes":"v127 evidence pins the released V52-A paper semantic contract lane on main: one repo-owned adeu_paper_semantics package, one bounded source-artifact family over paper.abstract and pasted.paragraph only, one explicit source-authority posture, one advisory-only interpretation posture, first-class typed models for source artifacts, spans, claims, O/E/D/U lane fragments, inference bridges, diagnostics, projections, top-level artifacts, and worker requests, direct V49 canonical hash-law reuse through adeu_semantic_forms, explicit identity-vs-projection split with projection/support fields excluded from semantic identity, deterministic accepted/reject fixture replay, fail-closed request/anchor/hash validation, bidirectional claim/fragment ownership enforcement, repo bootstrap wiring for editable package installation, and no live workbench route, worker bridge, or advanced visualization widening."}
```

## Recommendation (Post v127)

- gate decision:
  - `V52A_PAPER_SEMANTIC_CONTRACT_COMPLETE_ON_MAIN`
  - `V52_PAPER_SEMANTICS_FAMILY_ACTIVE_ON_MAIN`
- rationale:
  - `v127` closes the bounded `V52-A` semantic-contract seam on `main` by shipping
    the first repo-owned `adeu_paper_semantics` package rather than laundering the
    imported paper-workbench overlay into authority.
  - the shipped slice remains narrow and substrate-disciplined: two bounded source
    artifact kinds only, explicit source-authority and advisory-only interpretation
    posture, first-class typed semantic substructures, direct `V49` hash-law reuse,
    and deterministic reference/reject fixtures.
  - review hardening materially improved the release: the lock now reflects the
    shipped diagnostic field names, the reject-fixture test keeps static type safety,
    and artifact validation now fails closed on contradictory bidirectional
    claim/fragment ownership rather than allowing inconsistent grouping.
  - the imported bundle remains support-only and non-precedent; the release re-authors
    live ownership entirely in repo-native package paths.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs `v126`
    baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` should now be read with `V52-A` closed on
    `main` and the branch-local default next path advanced to `V52-B` / `vNext+128`.
