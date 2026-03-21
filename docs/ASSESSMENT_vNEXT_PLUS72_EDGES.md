# Assessment vNext+72 Edges (Post Closeout)

This document records edge disposition for `vNext+72` (`V39-A` retrospective external
contribution alignment baseline) after arc closeout.

Status: post-closeout assessment (March 21, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS72_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v72_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V39-A` retrospective alignment for one imported single-PR
  contribution; canonical `external_contribution_alignment_packet@1`; canonical
  `module_conformance_report@1`; one deterministic localized subject bundle for the
  poetry utility contribution; pinned policy provenance; explicit three-layer scope
  modeling; default-negative precedent semantics; deterministic evidence materialization;
  and closeout evidence/guard coverage.
- Out of scope: generalized all-module conformance scoring, automatic merge-worthiness
  judgment, imported-history laundering into fake native ADEU provenance, live-GitHub
  canonicalization, automatic policy adoption, and any broader marketplace or runtime
  widening surface.

## Inputs

- `docs/DRAFT_EXTERNAL_CONTRIBUTION_ALIGNMENT_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v13.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS72.md`
- `packages/adeu_core_ir/src/adeu_core_ir/external_contribution_alignment.py`
- `packages/adeu_core_ir/src/adeu_core_ir/external_contribution_alignment_evidence.py`
- `packages/adeu_core_ir/tests/test_external_contribution_alignment.py`
- `packages/adeu_core_ir/tests/test_external_contribution_alignment_evidence.py`
- `apps/api/fixtures/external_contribution_alignment/vnext_plus72/`
- `artifacts/quality_dashboard_v72_closeout.json`
- `artifacts/stop_gate/metrics_v72_closeout.json`
- `artifacts/agent_harness/v72/evidence_inputs/metric_key_continuity_assertion_v72.json`
- `artifacts/agent_harness/v72/evidence_inputs/runtime_observability_comparison_v72.json`
- `artifacts/agent_harness/v72/evidence_inputs/v39a_external_contribution_alignment_evidence_v72.json`
- merged PR: `#294`

## Pre-Lock Edge Set Outcome (v72 Closeout)

1. Historical rewrite risk: `resolved`.
   - canonical packet/report/evidence now keep the imported lane explicit and do not
     claim pre-doc or pre-lock provenance that never existed.
2. Structural conformance overclaim: `resolved`.
   - the released lane checks structural ADEU alignment only and preserves explicit
     maintainer follow-ups rather than pretending to decide architecture or merge
     worthiness in full.
3. Code/process collapse: `resolved`.
   - `module_conformance_report@1` keeps `code_alignment_judgment` and
     `meta_sequence_alignment_judgment` separate and inspectable.
4. Surface-truth drift: `resolved`.
   - accepted shipped scope is now bound to observed reachable surfaces and the first
     reference closes as an internal-only utility rather than a user-facing surface.
5. Network-dependent canonicalization: `resolved`.
   - canonical evaluation now consumes only committed local packet/report/evidence
     inputs, and the evidence file sets `live_github_dependency_absent = true`.
6. Policy frame drift: `resolved`.
   - policy provenance is now pinned in the packet and evidence bundle with exact
     paths, exact file hashes, and evaluator version.
7. Observation/judgment collapse: `resolved`.
   - v72 now freezes the three-layer scope model:
     `claimed_scope`, `observed_reachable_surfaces`, and `accepted_shipped_scope`.
8. Silent precedent grant: `resolved`.
   - precedent now defaults to `non_precedent` and requires an explicit reason when a
     maintainer grants precedent-bearing status.
9. Premature generalization: `resolved`.
   - `V39-A` closes on one explicit imported reference bundle only; no generalized
     all-module conformance engine ships in v72.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_core_ir/src/adeu_core_ir/external_contribution_alignment.py`
  - `packages/adeu_core_ir/src/adeu_core_ir/external_contribution_alignment_evidence.py`
  - `apps/api/fixtures/external_contribution_alignment/vnext_plus72/`
- merged guard files:
  - `packages/adeu_core_ir/tests/test_external_contribution_alignment.py`
  - `packages/adeu_core_ir/tests/test_external_contribution_alignment_evidence.py`
- v72 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v39a_external_contribution_alignment_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v72/runtime/evidence/codex/copilot/v72-closeout-main-1/`
- review-driven hardening now includes:
  - committed closeout evidence fixture rather than ignored local-only state,
  - pinned `policy_sources` in the packet instead of mutable path-only provenance,
  - temp-repo replay that honors the supplied `repository_root`,
  - fail-closed rejection when maintainer-completed actions are not backed by actual
    accepted-diff evidence.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v72_edge_closeout_summary@1",
  "arc": "vNext+72",
  "target_path": "V39-A",
  "prelock_edge_count": 9,
  "resolved_edge_count": 9,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v70": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v72)

1. The released lane remains intentionally bounded to one imported single-PR reference
   rather than a broad intake marketplace.
2. Structural conformance remains distinct from architectural meaning, product value,
   and merge policy; those stay under explicit maintainer judgment.
3. The closeout runtime evidence is continuity-only provenance because v72 does not
   widen the runtime lane itself.
4. Future widening to more imported contribution classes or generalized module checks
   remains deferred by design to later planning.

## Recommendation (Post Closeout)

1. Mark the v72 edge set as closed with no blocking issues.
2. Treat canonical `external_contribution_alignment_packet@1`, canonical
   `module_conformance_report@1`, and canonical
   `v39a_external_contribution_alignment_evidence@1` as the released `V39-A`
   substrate going forward.
3. Keep the imported single-PR lane explicitly retrospective and local-subject-bound.
4. Keep broader multi-subject or all-module conformance generalization deferred unless
   it is released under new lock text.
