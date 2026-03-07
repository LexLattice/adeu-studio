# Assessment vNext+54 Edges (Pre-Lock)

This document records pre-lock edge planning for `vNext+54` (`V34-F`
standalone bundle integrity self-verification baseline).

Status: pre-lock assessment (March 7, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS54_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": true,
  "authoritative_scope": "v54_prelock_edge_planning",
  "required_in_decision": true,
  "notes": "This document is authoritative for v54 pre-lock edge planning until superseded by post-closeout disposition."
}
```

## Scope

- In scope: thin `V34-F` baseline over standalone packaging-manifest integrity verification,
  deterministic integrity-result emission, and closeout evidence integration.
- Out of scope: installer/updater integration, archive fetch or unpack flows,
  detached distribution channels, deployment-mode expansion, `V34-G`, stop-gate
  schema-family fork, metric-key expansion, and generalized portability release.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS53.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS53.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux_standalone.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
- `packages/adeu_agent_harness/tests/test_taskpack_packaging.py`
- `artifacts/quality_dashboard_v53_closeout.json`
- `artifacts/stop_gate/metrics_v53_closeout.json`
- `artifacts/agent_harness/v53/evidence_inputs/runtime_observability_comparison_v53.json`
- `artifacts/agent_harness/v53/evidence_inputs/metric_key_continuity_assertion_v53.json`
- `artifacts/agent_harness/v53/evidence_inputs/v34e_attestation_evidence_v53.json`
- `artifacts/agent_harness/v50/matrix/standalone/taskpack_ux_packaging_manifest.json`
- `artifacts/agent_harness/v47/packaging/standalone/taskpack_ux_packaging_manifest.json`

## Current Repo Reality

1. Standalone packaging is real and deterministic on `main`.
   - `package_ux.py` emits deterministic packaging manifest and provenance artifacts for
     `standalone`.
2. Packaging manifest already carries deterministic emitted-file inventory and
   `packaging_bundle_hash` on `main`.
3. No released `standalone_integrity_verification_result@1` artifact exists on `main`.
4. No shared standalone integrity checker exists on `main`.
5. No closeout surface currently contains canonical `v34f_standalone_integrity_evidence@1`.
6. Installer/updater or archive-acquisition flows are not part of the current harness
   authority surface.

## Pre-Lock Edge Set (Draft)

1. Standalone integrity checker gap: `open`.
   - no shared standalone self-verification utility exists on `main`.
2. Packaging-manifest bundle-hash subject ambiguity risk: `open`.
   - the checker must freeze whether it recomputes the current manifest subject exactly or
     silently widens to a different bundle hash subject.
3. Packaging result versus manifest authority ambiguity risk: `open`.
   - `taskpack_packaging_result@1` exists, but the first integrity lane must clarify whether
     it is a binding sibling or a primary hash subject.
4. Standalone-only scope ambiguity risk: `open`.
   - the path goal is standalone end-user verification; integrated-mode handling should not
     be silently accepted in the first slice.
5. Missing or extra bundle-file acceptance risk: `open`.
   - a thin integrity checker must fail closed on inventory drift, not just validate files
     that happen to exist.
6. Stale packaging-output reuse risk: `open`.
   - the current standalone packaging output must be materialized in the v54 flow rather
     than compared against a stale external bundle directory by accident.
7. Bundle-root derivation ambiguity risk: `open`.
   - the checker needs an explicit single bundle-root resolution policy to avoid comparing
     mixed paths or stray files.
8. Raw repo-read authority leakage risk: `open`.
   - integrity verification should not depend on arbitrary source-tree reads outside the
     declared standalone bundle root.
9. Installer/updater overreach risk: `open`.
   - `V34-F` can widen into installer or updater behavior unless that is explicitly frozen
     out of scope.
10. Archive fetch/unpack overreach risk: `open`.
   - a standalone verifier could drift into acquisition/extraction logic unless artifact
     ingestion only is made explicit.
11. Packaging-manifest schema validation gap: `open`.
   - malformed but hashable manifest data must not be treated as acceptable integrity input.
12. Closeout evidence integration gap: `open`.
   - current closeout surfaces contain no canonical `v34f` integrity evidence slot.
13. Stop-gate churn risk: `open`.
   - v54 should not widen stop-gate schema family or metric cardinality.
14. File-inventory ordering drift risk: `open`.
   - emitted-file inventory needs a deterministic ordering rule for byte-stable verification.
15. Packaging materialization failure ambiguity risk: `open`.
   - if current standalone packaging output cannot be materialized in the v54 flow,
     integrity acceptance must fail closed.
16. Shared integrity-checker identifier comparability risk: `open`.
   - closeout evidence should require a frozen comparable checker identifier rather than free
     text.
17. Deployment-mode exactness ambiguity risk: `open`.
   - the standalone-only rule should be exact and case-sensitive, not “helpfully”
     normalized.
18. Detached distribution authority creep risk: `open`.
   - detached checksum or distribution channels should remain deferred unless explicitly
     locked in a future arc.
19. Manifest path-domain and bundle-root escape ambiguity risk: `open`.
   - manifest emitted-file paths need a bundle-relative domain rule, and normalized path or
     symlink escapes from the declared bundle root must fail closed.
20. Integrity-checker procedure ambiguity risk: `open`.
   - the first slice should freeze recomputing actual emitted-file hashes and exact inventory
     equality before bundle-hash equivalence, not allow trust-in-manifest-only shortcuts.
21. Packaging provenance full-artifact binding ambiguity risk: `open`.
   - provenance binding should be over the full canonical
     `taskpack_packaging_provenance@1` artifact hash, not an unspecified subset.
22. Failure-path integrity-result emission ambiguity risk: `open`.
   - the lane should decide explicitly whether deterministic result artifacts exist on
     failure paths or only on intact paths.
23. Verification-result sibling-artifact ambiguity risk: `open`.
   - `taskpack_verification_result@1` should remain a continuity sibling only and not drift
     into primary integrity authority.
24. Explicit bundle-root input versus heuristic derivation risk: `open`.
   - the checker should require an explicit bundle-root input rather than infer roots from
     manifest paths or common-prefix heuristics.
25. Symlink policy ambiguity risk: `open`.
   - the first slice should freeze whether symlinks are allowed at all and, if not, reject
     them deterministically.
26. Manifest duplicate normalized-path ambiguity risk: `open`.
   - duplicate normalized manifest `path` rows should fail closed just as duplicate bundle
     inventory paths do.
27. Input-validation result-emission ambiguity risk: `open`.
   - the lane should decide explicitly whether missing paths, invalid schema, or invalid
     bundle-root inputs still materialize deterministic result artifacts before failure.
28. Manifest schema invalidity operationalization gap: `open`.
   - schema validation should appear as an explicit fail-closed condition, not only an
     evidence boolean.
29. Non-regular file portability ambiguity risk: `open`.
   - the first standalone portability slice should freeze whether non-regular filesystem
     objects are accepted in manifest inventory.
30. Recomputed manifest-bundle-hash forensic gap: `open`.
   - closeout evidence should record the recomputed bundle hash, not only the declared one
     plus verification booleans.

## Recommended Thin Slice

1. Treat `v54` as a standalone integrity self-verification baseline only.
   - shared standalone integrity checker
   - deterministic `standalone_integrity_verification_result@1`
2. Freeze authority to current standalone packaging surfaces only.
   - reuse `taskpack_ux_packaging_manifest@1`
   - reuse packaging provenance and sibling packaging result bindings
   - no alternate bundle-hash subject in v54
3. Keep scope intentionally local and narrow.
   - explicit local artifact ingestion only
   - standalone mode only
   - no installer/updater or fetch/unpack behavior in v54
4. Make emitted-file inventory exact-match required and test-backed.
   - missing or extra bundle files fail closed
   - bundle root resolution stays deterministic
5. Add canonical closeout evidence and guard suites in the same arc.
   - the lane is not real until closeout can prove the integrity result, manifest-subject
     verification, and standalone-only posture on `main`
6. Freeze hash-subject and current-flow materialization semantics before implementation
   starts.
   - packaging-manifest bundle hash means emitted-file row inventory only
   - current standalone packaging output must be materialized in the current v54 flow
   - materialization failure fails closed
   - recompute actual emitted-file hashes, require exact inventory equality, then
     recompute the manifest bundle-hash subject
7. Freeze local-artifact-only and non-portability posture before implementation starts.
   - no raw repo reads outside bundle root
   - no installer/updater integration
   - no archive fetch or unpack behavior
   - no normalized path or symlink escape from the explicit bundle root
8. Freeze singleton checker and deployment-mode semantics before implementation starts.
   - shared checker identifier must be comparable
   - `deployment_mode == "standalone"` is exact and case-sensitive
9. Freeze explicit bundle-root and sibling-artifact semantics before implementation starts.
   - bundle root is an explicit local artifact input, not a heuristic derivation
   - packaging provenance binds by full canonical artifact hash
   - `taskpack_verification_result@1` remains a sibling continuity artifact only
   - deterministic integrity-result artifacts still materialize on failure paths
10. Freeze manifest/file-object and failure-artifact semantics before implementation starts.
   - duplicate normalized manifest paths fail closed
   - symlinks are forbidden
   - non-regular filesystem objects fail closed
   - input-validation failures still materialize deterministic typed result artifacts
   - recomputed manifest bundle hash is recorded in closeout evidence

## Pre-Lock Summary (Machine-Checkable)

```json
{
  "schema": "v54_prelock_edge_summary@1",
  "arc": "vNext+54",
  "target_path": "V34-F",
  "identified_edge_count": 30,
  "recommended_scope": "thin_v34f_standalone_integrity_baseline_only",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "blocking_themes": [
    "shared_standalone_integrity_checker_must_be_added",
    "packaging_manifest_bundle_hash_subject_must_be_frozen",
    "packaging_result_must_remain_binding_sibling_not_primary_hash_subject",
    "standalone_only_scope_must_be_exact",
    "emitted_file_inventory_exact_match_must_be_required",
    "current_packaging_output_must_be_materialized_in_flow",
    "bundle_root_resolution_must_be_deterministic",
    "manifest_paths_must_be_bundle_relative_and_bundle_root_escape_must_fail_closed",
    "duplicate_normalized_manifest_paths_must_fail_closed",
    "symlinks_must_be_forbidden",
    "non_regular_files_must_fail_closed",
    "actual_emitted_file_hashes_must_be_recomputed_from_bundle_bytes",
    "raw_repo_reads_must_be_forbidden",
    "installer_and_updater_integration_must_be_forbidden",
    "archive_fetch_and_unpack_must_be_forbidden",
    "packaging_manifest_schema_validation_must_precede_hash_verification",
    "manifest_schema_invalidity_must_be_a_named_fail_closed_condition",
    "packaging_provenance_must_bind_by_full_canonical_artifact_hash",
    "verification_result_must_remain_sibling_only_not_primary_integrity_authority",
    "failure_paths_must_still_emit_deterministic_integrity_results",
    "input_validation_failures_must_still_emit_deterministic_integrity_results",
    "recomputed_manifest_bundle_hash_should_be_recorded_for_forensics",
    "closeout_evidence_slot_must_be_added",
    "stop_gate_schema_family_and_metric_keyset_must_remain_frozen",
    "shared_integrity_checker_identifier_must_be_comparable",
    "detached_distribution_authority_must_remain_deferred"
  ]
}
```

## Recommendation

1. Draft `v54` as a thin `V34-F` baseline over standalone integrity verification only.
2. Keep installer/updater, archive acquisition, and detached distribution behavior deferred.
3. Require deterministic emitted-file inventory exact-match verification against the current
   standalone packaging manifest before treating the lane as acceptable in this arc.
4. Require deterministic integrity-result and canonical `v34f` evidence artifacts before
   treating the lane as closed.
