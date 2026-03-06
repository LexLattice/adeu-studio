# Assessment vNext+51 Edges (Draft)

This document assesses the initial `vNext+51` planning candidate after `v50` closeout.

Status: draft planning assessment (March 6, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS51_EDGES.md",
  "phase": "prelock_assessment",
  "authoritative": true,
  "authoritative_scope": "v51_prelock_edge_assessment",
  "required_in_decision": true,
  "notes": "This document assesses whether V34-C is ready to draft as the next thin slice after v50 closeout."
}
```

## Scope

- In scope: post-v50 evaluation of `V34-C` verifier-lane policy recomputation for the next
  arc.
- Out of scope: `V34-D` through `V34-G`, stop-gate schema-family fork, metric-key expansion,
  packaging-equivalence recomputation beyond verifier lane, and `L2` boundary release.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS50.md`
- `docs/ASSESSMENT_vNEXT_PLUS50_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/matrix_parity.py`
- `packages/adeu_agent_harness/tests/test_taskpack_runner.py`
- `packages/adeu_agent_harness/tests/test_taskpack_verifier.py`

## Current Harness Reality (Post v50)

1. Runner-local policy validation is real and deterministic.
   - `_validate_policy(...)` in `run_taskpack.py` already derives policy issues from:
     - `ALLOWLIST.json`,
     - `FORBIDDEN.json`,
     - `COMMANDS.json`,
     - candidate change plan operations,
     - dry-run command policy.
2. Runner provenance exposes only a minimal policy outcome subject.
   - `taskpack_runner_provenance@1` records:
     - `passed`,
     - ordered issue tuples with `issue_code`, `target_path`, `hunk_index`,
     - `exit_status`.
3. Rich rejection-diagnostic fields are present, but they are runner-local detail today.
   - reason text, line ranges, and `policy_source` exist in
     `candidate_change_plan_rejection_diagnostic@1`, not in the runner provenance exact-match
     subject.
4. Verifier currently validates consistency, not independence.
   - `verify_taskpack_run.py` recomputes candidate/provenance hashes and checks runner
     self-consistency, but it does not independently derive policy outcome from canonical
     artifacts.
5. No released recompute artifact exists on `main`.
   - there is no `policy_recompute_result@1` contract, emitted artifact, or shared recompute
     helper surface in the current harness.
6. Packaging and matrix parity are downstream signals, not substitutes for verifier
   recompute.
   - `package_ux.py` and `matrix_parity.py` extract parity and policy-equivalence signals
     from emitted artifacts, but they do not close the verifier-lane runner-trust gap named
     by `V34-C`.

## Edge Set

1. Runner-private validator drift risk: `open`.
   - the current policy validator exists only as a runner-local helper.
   - without a shared recompute contract, runner and verifier can drift while both staying
     locally “valid”.
   - Remediation for v51:
     - define a shared canonical recompute engine or shared contract surface,
     - forbid verifier-side ad hoc reimplementation drift.

2. Exact-match subject ambiguity risk: `open`.
   - runner provenance carries a minimal policy subject, while rejection diagnostics carry
     richer fields.
   - without a frozen comparison subject, two implementations could both claim recompute
     parity while comparing different levels of detail.
   - Remediation for v51:
     - freeze exact-match subject to:
     - `passed`,
     - ordered issue tuples `(issue_code, target_path, hunk_index)`,
      - `exit_status`,
     - treat `exit_status` as the runner policy verdict status under the frozen validator
       scope rather than a verifier process exit code,
     - treat reason text, line ranges, and policy-source prose as non-authoritative for
       exact match.

3. Non-authoritative recompute source drift risk: `open`.
   - current repo already has downstream parity artifacts and runtime state available; a
     loose v51 draft could silently use those as a recompute shortcut.
   - Remediation for v51:
     - bind recompute authority only to canonical taskpack policy components, canonical
       candidate change plan, and runner dry-run input,
     - treat runner provenance, rejection diagnostics, and verified result as binding or
       continuity surfaces only rather than semantic policy sources,
     - forbid logs, live repo state, packaging projections, and ad hoc post-analysis.

4. Failure-artifact omission risk: `open`.
   - `V34-C` planning requires a deterministic recompute artifact even on mismatch or failure,
     but the current verifier emits no such artifact.
   - Remediation for v51:
     - require deterministic `policy_recompute_result@1` emission on exact-match and mismatch
       paths,
     - fail closed if verifier mismatch occurs without emitted recompute evidence.

5. Policy-scope overexpansion risk: `open`.
   - current runner validator covers a specific issue-code set and rule surface only.
   - a broader “zero-trust recompute” draft would overstate current code reality.
   - Remediation for v51:
     - freeze v51 to the current runner validator scope only,
     - freeze the allowed issue-code set as exact and closed for the arc,
     - treat broader policy recomputation as a future follow-on path.

6. Dry-run input ambiguity risk: `open`.
   - dry-run command prohibition is part of current policy behavior, but the candidate change
     plan alone does not encode dry-run state.
   - Remediation for v51:
     - freeze `runner_result.dry_run` as the authoritative dry-run input for recompute,
     - bind recompute to the same canonical candidate change plan hash already recorded in
       runner artifacts,
     - require runner policy-failure paths to still materialize canonical runner-result
       inputs needed for recompute binding.

7. Closeout evidence integration gap: `open`.
   - there is currently no v34c-specific closeout evidence block or recompute artifact path
     carried through the closeout surface.
   - Remediation for v51:
     - require canonical `v34c_policy_recompute_evidence@1`,
     - bind that evidence to the emitted recompute artifact by hash.

8. Partial verifier success-on-mismatch risk: `open`.
   - without an explicit rule, a recompute mismatch path could emit failure evidence but still
     leave behind a nominal success-class verification result artifact.
   - Remediation for v51:
     - require recompute artifact emission before failure,
     - forbid success-class verification result emission after recompute mismatch.

9. Duplicate issue-tuple canonicalization drift risk: `open`.
   - if duplicate `(issue_code, target_path, hunk_index)` tuples are silently deduplicated,
     two recompute implementations can produce the same canonical list while one is still
     semantically over-emitting.
   - Remediation for v51:
     - forbid duplicate issue tuples before canonicalization,
     - fail closed instead of silently collapsing them.

10. Stop-gate churn risk: `open`.
   - `V34-C` is verifier hardening and evidence work, not metric-family expansion.
   - Remediation for v51:
     - keep stop-gate schema family frozen at `stop_gate_metrics@1`,
     - introduce no new metric keys,
     - carry recompute proof as canonical evidence rather than additive stop-gate metrics.

## Recommendation

1. Select `V34-C` for `vNext+51`, but only as a thin verifier-lane baseline slice.
2. Do not draft v51 as full packaging-equivalence recomputation, remote attestation, or
   retry-context automation.
3. Draft v51 around two narrow implementation slices:
   - `Z1` shared canonical policy recompute engine + deterministic result baseline,
   - `Z2` verifier mismatch enforcement and canonical closeout evidence integration.
4. Freeze the exact-match subject now so runner provenance, rejection diagnostics, and
   recompute results cannot silently compare different abstractions.
5. Freeze recompute source authority now so downstream parity artifacts cannot masquerade as
   independent verifier recomputation.
6. Require deterministic recompute artifact emission on mismatch paths so the new trust lane
   is inspectable instead of purely negative/error-only.
7. Forbid success-class verifier artifacts on recompute mismatch so the lane cannot signal
   both failure evidence and nominal success at once.

## Blocking Assessment

```json
{
  "schema": "v51_blocking_edge_summary@1",
  "arc": "vNext+51",
  "candidate_path": "V34-C",
  "blocking_if_full_zero_trust_scope_claimed": true,
  "blocking_if_scoped_to_verifier_lane_policy_recompute_baseline": false,
  "recommended_scope": "shared_current_policy_recompute_plus_verifier_mismatch_fail_closed_only",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality_baseline": 80,
  "prelock_edge_count": 10
}
```

## Residual Deferred Work (Non-v51)

1. Packaging-equivalence recomputation beyond verifier lane remains deferred.
2. Retry-context automation, remote/enclave attestation, and standalone self-verification
   remain deferred beyond v51.
3. Matrix expansion beyond current released adapter/mode sets remains deferred.
4. Crypto portability and alternative verifier toolchains remain deferred and are not part of
   `V34-C`.
