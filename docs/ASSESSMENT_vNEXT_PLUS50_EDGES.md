# Assessment vNext+50 Edges (Draft)

This document assesses the initial `vNext+50` planning candidate after `v49` closeout.

Status: draft planning assessment (March 6, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS50_EDGES.md",
  "phase": "prelock_assessment",
  "authoritative": true,
  "authoritative_scope": "v50_prelock_edge_assessment",
  "required_in_decision": true,
  "notes": "This document assesses whether V34-B is ready to draft as the next thin slice after v49 closeout."
}
```

## Scope

- In scope: post-v49 evaluation of `V34-B` matrix-lane parity work for the next arc.
- Out of scope: `V34-C` through `V34-G`, stop-gate schema-family fork, metric-key expansion,
  and `L2` boundary release.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS49.md`
- `docs/ASSESSMENT_vNEXT_PLUS49_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`
- `packages/adeu_agent_harness/tests/test_taskpack_runner.py`
- `packages/adeu_agent_harness/tests/test_taskpack_packaging.py`

## Current Harness Reality (Post v49)

1. Deployment mode is real and frozen.
   - `package_ux.py` already enforces `adeu_integrated` and `standalone` as the released
     deployment-mode enum.
2. Adapter identity is real, but adapter-kind breadth is not.
   - runner registry/provenance already carry `adapter_id`, but current code only supports
     `candidate_plan_passthrough`.
3. Runtime lane identity is still planning-only.
   - `runtime_id` exists in `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`, but it is not yet a real
     harness contract surface or emitted artifact field.
4. Cross-mode parity already exists, but only as current deployment-mode proof.
   - packaging tests already prove exact canonical subtree parity and
     `policy_equivalence` parity across integrated/standalone outputs.
5. Declared matrix registry/report artifacts do not exist yet.
   - there is no released `adapter_matrix@1` contract or deterministic
     `adapter_matrix_parity_report@1` artifact on `main`.

## Edge Set

1. Full-tuple overclaim risk: `open_if_v50_is_scoped_too_broadly`.
   - `V34-B` planning defines `(deployment_mode, adapter_id, runtime_id)`, but current code
     only makes the first two lanes real.
   - Remediation for v50:
     - scope `runtime_id` to a frozen singleton declared value only,
     - forbid multi-runtime expansion in this arc.

2. Enabled-lane ambiguity and declared-vs-discovered drift risk: `open`.
   - `V34-B` explicitly requires declared registry authority, but current parity coverage
     comes from direct test orchestration rather than a released matrix registry contract.
   - Without a frozen enabled-lane rule, two implementations could count different lane sets
     while both claiming compliance.
   - Remediation for v50:
     - add declared `adapter_matrix@1`,
     - define the registry as enabled-only and forbid disabled rows in this arc,
     - require matrix adapter ids to reuse the existing runner adapter registry namespace,
     - require deterministic lexicographic ordering and tuple uniqueness,
     - forbid runtime/host auto-discovery as lane authority.

3. False-positive singleton runtime drift risk: `open`.
   - if the harness infers `runtime_id` from host/container state, legitimate local runs
     could self-report a value outside the frozen singleton and fail for the wrong reason.
   - Remediation for v50:
     - require `runtime_id` to be contract-derived only,
     - allow explicit override only when it exactly equals the frozen singleton,
     - forbid host/container/environment inference from widening the runtime namespace.

4. Adapter-kind overexpansion risk: `open`.
   - current runner code hard-fails any adapter kind outside `candidate_plan_passthrough`,
     so a broad matrix draft would overstate real capability.
   - Remediation for v50:
     - freeze adapter-kind support to current passthrough behavior only,
     - treat broader adapter-kind matrixing as deferred follow-on work.

5. Parity-subject and source ambiguity risk: `open`.
   - current packaging parity already allows launcher/bundle difference by deployment mode
     while requiring exact canonical subtree parity and exact `policy_equivalence` parity.
   - Without a source lock, matrix reporting could drift into log parsing, repo-state
     inspection, or quiet recomputation.
   - Remediation for v50:
     - lock those exact comparison boundaries into the matrix contract,
     - require canonical subtree parity to reuse the existing packaging/verifier canonical
       artifact subject family rather than a new projection,
     - freeze the value shapes of the policy-equivalence subject keys,
      - limit parity extraction to schema-typed artifacts plus the deterministic matrix report,
      - do not let matrix reporting widen or narrow the existing parity subject.

6. Launcher exception loophole risk: `open`.
   - the current deployment-mode launcher difference is real, but the exception must stay
     fenced to non-canonical wrapper mechanics.
   - Remediation for v50:
     - state explicitly that only the non-canonical bundle launcher surface may differ,
     - require exact-match parity across the canonical subtree.

7. Lane-specific policy drift risk: `open`.
   - once a matrix registry exists, the main danger is treating lanes as policy-override
     points rather than as reporting/execution variants over frozen semantics.
   - Remediation for v50:
     - forbid lane-specific policy overrides,
     - require exact policy-equivalence matches per declared adapter id across current
       deployment modes.

8. Stop-gate churn risk: `open`.
   - `V34-B` is hardening/reporting work, not a metric-family change.
   - Remediation for v50:
     - keep stop-gate schema family frozen at `stop_gate_metrics@1`,
     - introduce no new metric keys,
     - capture matrix parity as canonical evidence rather than additive stop-gate metrics.

9. Matrix report completeness blind-spot risk: `open`.
   - without an explicit completeness rule, a report could omit a declared lane while still
     looking structurally valid.
   - Remediation for v50:
     - require every declared lane to appear exactly once in the matrix report,
     - fail closed on missing or duplicated report rows.

## Recommendation

1. Select `V34-B` for `vNext+50`, but only as a thin baseline slice.
2. Do not draft v50 as full multi-runtime or multi-adapter expansion.
3. Draft v50 around two narrow implementation slices:
   - `Y1` declared matrix registry + deterministic parity report baseline,
   - `Y2` registry-backed parity guard suite and canonical closeout evidence integration.
4. Keep `runtime_id` explicit in the contract, but freeze it to a singleton declared value in
   this arc so the docs stay aligned with current implementation reality.
5. Freeze the registry as enabled-only now rather than carrying disabled-lane ambiguity into
   the first matrix release.
6. Freeze `runtime_id` source policy now so container/host execution wrappers cannot create
   false-positive singleton runtime violations.
7. Require matrix-report completeness explicitly so the first released matrix baseline cannot
   silently drop declared lanes.

## Blocking Assessment

```json
{
  "schema": "v50_blocking_edge_summary@1",
  "arc": "vNext+50",
  "candidate_path": "V34-B",
  "blocking_if_full_scope_claimed": true,
  "blocking_if_scoped_to_thin_matrix_baseline": false,
  "recommended_scope": "declared_matrix_registry_plus_registry_backed_current_lane_parity_only",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality_baseline": 80
}
```

## Residual Deferred Work (Non-v50)

1. True multi-runtime lane expansion remains deferred because `runtime_id` is not yet a
   released harness surface.
2. Matrix parity beyond current released adapter/mode sets remains deferred.
3. Independent zero-trust recomputation, retry-context automation, and remote/enclave
   attestation remain deferred beyond v50.
4. Crypto portability and a fully in-memory secure orchestrator remain deferred and are not
   part of `V34-B`.
