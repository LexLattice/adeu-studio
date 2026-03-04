# Locked Continuation vNext+45 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS44.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS44.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+44` (`S1`-`S2`, `V33-A`) is merged on `main` via PR `#236` and PR `#237` with green CI checks.
- `vNext+44` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS44.md` with `all_passed = true`.
- Post-v44 planning baseline remains `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`.
- Selected v45 thin-slice default is Codex SDK constrained runner path:
  - `V33-B` (taskpack-driven runner + deterministic pre-write policy validation).
- `vNext+45` is constrained to deterministic additive hardening for `V33-B` only:
  - no auditor/evidence-writer lane release (`V33-C`),
  - no integrated/standalone UX packaging release (`V33-D`),
  - no stop-gate metric-key expansion release in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS44.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v45,
  - v45 keyset must be exactly equal to v44 keyset (set equality, derived cardinality),
  - baseline derived cardinality at v45 start is `80` and must remain unchanged in this arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- v36-v44 continuity guarantees remain frozen as release preconditions:
  - worker-route governance continuity remains authoritative,
  - persistence-release continuity remains authoritative,
  - commitments IR continuity remains authoritative,
  - semantic-source continuity remains authoritative,
  - compiler-core continuity remains authoritative,
  - surface-governance continuity remains authoritative,
  - CI/closeout wiring continuity remains authoritative,
  - additive metric-extension continuity remains authoritative,
  - taskpack contract/compiler continuity remains authoritative.
- Boundary-release scope lock for v45 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- Taskpack authority continuity lock is frozen:
  - runner authority derives only from compiled taskpack components and taskpack manifest contract surfaces,
  - free-form repository prose and model natural-language self-claims are non-authoritative for policy decisions.
- Runner anti-injection boundary lock is frozen:
  - repository text is non-authoritative by default for instruction authority,
  - only taskpack-declared context blocks are authoritative instruction inputs for the runner lane.
- Runner portability boundary lock is frozen:
  - harness kernel must not import `apps/api` application-layer modules directly,
  - provider/runtime bindings in this arc must be adapter-boundary surfaces only.
- Closeout observability continuity lock is frozen:
  - v45 closeout must include a runtime-observability comparison row against v44 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `T1` Codex SDK constrained runner + candidate-change-plan policy-validation MVP (`V33-B`)
2. `T2` Runner determinism/fail-closed guard suite (`V33-B`)

Out-of-scope note:

- auditor/verifier/evidence-writer lane release (`V33-C`) in this arc,
- integrated + standalone UX packaging release (`V33-D`) in this arc,
- stop-gate metric-key expansion in this arc,
- stop-gate schema-family fork in this arc,
- taskpack compiler contract-surface expansion beyond v44 `V33-A` authority in this arc,
- cryptographic signing/key-management release in this arc,
- runtime/provider/proposer endpoint expansion in this arc,
- solver/runtime semantics contract release in this arc.

## Deferred Follow-on Candidates (Non-v45)

- v46+ deterministic auditor/verifier + evidence-writer lane (`V33-C`) under explicit lock text.
- v47+ integrated + standalone UX packaging (`V33-D`) under explicit lock text.
- v48+ optional taskpack signing and trust-anchor distribution under explicit lock text.
- v49+ optional matrix-lane parity checks for runner adapters under explicit lock text.

## V44 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS44.md",
  "target": "V33-B",
  "required_continuity_guards": [
    "V31_F_GOVERNANCE_CONTINUITY_GREEN",
    "V31_G_PERSISTENCE_CONTINUITY_GREEN",
    "V32_A_COMMITMENTS_CONTINUITY_GREEN",
    "V32_B_SEMANTIC_SOURCE_CONTINUITY_GREEN",
    "V32_C_COMPILER_CORE_CONTINUITY_GREEN",
    "V32_D_SURFACE_CODEGEN_CONTINUITY_GREEN",
    "V32_E_CI_CLOSEOUT_CONTINUITY_GREEN",
    "V32_F_METRIC_EXTENSION_CONTINUITY_GREEN",
    "V33_A_TASKPACK_CONTINUITY_GREEN"
  ],
  "expected_relation": "all_required_continuity_guards_remain_green"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v45.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V33-B Runner Contract Assertion (Machine-Checkable)

```json
{
  "schema": "v33b_runner_contract@1",
  "target_arc": "vNext+45",
  "target_path": "V33-B",
  "taskpack_authority_inputs": {
    "taskpack_manifest": "required",
    "taskpack_required_components": [
      "TASKPACK.md",
      "ACCEPTANCE.json",
      "ALLOWLIST.json",
      "FORBIDDEN.json",
      "COMMANDS.json",
      "EVIDENCE_SLOTS.json",
      "taskpack_manifest.json"
    ],
    "taskpack_component_schema_id_format": "taskpack/<component>@<version>"
  },
  "runner_execution_interface": {
    "kernel_package_authority": "packages/adeu_agent_harness",
    "runner_entrypoint": "python -m adeu_agent_harness.run_taskpack",
    "provider_binding_surface": "adapter_interface_only",
    "adapter_selection_key": "adapter_id",
    "adapter_registry_contract": "taskpack_runner_adapter_registry@1",
    "adapter_resolution_policy": "deterministic_single_match_fail_closed",
    "adapter_match_predicate": "exact_case_sensitive_adapter_id_equality",
    "apps_api_direct_import": "forbidden_non_v45",
    "dry_run_flag": "--dry-run",
    "dry_run_mode": "model_free_candidate_plan_required",
    "dry_run_model_invocation": "forbidden_non_v45",
    "dry_run_preview_output_root": "artifacts/agent_harness/v45/dry_run_preview"
  },
  "candidate_change_plan_policy": {
    "schema": "candidate_change_plan@1",
    "canonical_subject": "file_operations_and_unified_diff_payload_only",
    "file_operations_ordering": "deterministic_sorted_by_path_then_operation_kind",
    "input_source_policy": "explicit_candidate_plan_artifact_only_v45",
    "natural_language_claims_authority": "forbidden",
    "canonical_ast_policy": {
      "candidate_plan_ast_required": true,
      "validation_subject": "canonical_ast_only",
      "apply_subject": "same_canonical_ast_instance_only",
      "raw_diff_apply_path": "forbidden_non_v45",
      "fuzzy_hunk_application": "forbidden_non_v45",
      "malformed_or_overlapping_hunks": "fail_closed"
    },
    "diff_normalization": {
      "encoding": "utf-8",
      "line_endings": "lf",
      "header_policy": "strip_timestamps_keep_a_b_paths_only",
      "whitespace_policy": "preserve_non_header_content"
    },
    "policy_inputs": [
      "ALLOWLIST.json",
      "FORBIDDEN.json"
    ],
    "required_validation_phase": "pre_write_pre_commit",
    "validation_control_flow": "single_write_gate_no_bypass_even_on_exception_paths",
    "validation_failure_outcome": "fail_closed_block_apply_and_commit"
  },
  "command_authority_policy": {
    "authoritative_source": "COMMANDS.json_only",
    "model_suggested_commands": "forbidden",
    "execution_interception_surface": "subprocess_invocation_layer_required",
    "undeclared_command_execution": "fail_closed"
  },
  "forbidden_effect_policy": {
    "definition": "forbidden_touches_and_operation_kinds_only_v45",
    "forbidden_touch_authority": "FORBIDDEN.json",
    "forbidden_operation_kinds": [
      "delete",
      "rename",
      "chmod"
    ],
    "forbidden_operation_kinds_enum_policy": "closed_enum_v45",
    "semantic_inference_based_forbidden_effects": "deferred_non_v45"
  },
  "instruction_authority_policy": {
    "repository_text_authority": "non_authoritative_default",
    "authoritative_instruction_source": "taskpack_declared_context_blocks_only",
    "prompt_injection_runtime_claims_authority": "forbidden"
  },
  "dry_run_enforcement_policy": {
    "network_guard": "outbound_socket_and_http_client_calls_blocked_fail_closed",
    "workspace_mutation_guard": "repo_write_rename_delete_blocked_except_preview_output_root",
    "preview_output_root_allowed_ops": "directory_creation_and_file_writes_only",
    "subprocess_policy": "subprocess_execution_forbidden_non_v45",
    "guard_initialization_required": true
  },
  "rejection_diagnostics_policy": {
    "schema": "candidate_change_plan_rejection_diagnostic@1",
    "required_on_policy_failure": true,
    "required_fields": [
      "issue_code",
      "reason",
      "target_path",
      "hunk_index",
      "line_range",
      "policy_source"
    ],
    "deterministic_ordering": "stable_issue_code_then_target_path_then_hunk_index_integer_ascending",
    "hunk_index_sort_order": "ascending_integer",
    "output_path": "artifacts/agent_harness/v45/rejections"
  },
  "provenance_policy": {
    "run_provenance_schema": "taskpack_runner_provenance@1",
    "required_fields": [
      "taskpack_manifest_hash",
      "adapter_id",
      "candidate_change_plan_hash",
      "policy_validation_result",
      "exit_status"
    ],
    "hash_subject_fields": [
      "taskpack_manifest_hash",
      "adapter_id",
      "candidate_change_plan_hash",
      "policy_validation_result",
      "exit_status"
    ],
    "excluded_non_authoritative_fields": [
      "wall_clock_timestamp",
      "host_identity",
      "absolute_paths"
    ],
    "diagnostic_sort_order": "stable_issue_code_then_canonical_details",
    "deterministic_hash_profile": "sha256_canonical_json_frozen"
  },
  "closeout_doc_policy": {
    "decision_doc": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS45.md",
    "required_json_blocks": [
      "runtime_observability_comparison@1",
      "metric_key_continuity_assertion@1",
      "v33b_runner_wiring_evidence@1"
    ]
  },
  "stop_gate_continuity_policy": {
    "schema_family": "stop_gate_metrics@1",
    "metric_key_change": "forbidden",
    "expected_keyset_relation": "exact_set_equality_with_v44",
    "expected_cardinality": 80
  },
  "closeout_lint_severity_policy": {
    "required_contract_violations": "error",
    "optional_informational_fields": "warning_allowed_non_blocking",
    "required_violation_channel": "error_only_non_zero_exit",
    "required_error_namespace_warning_channel_use": "forbidden"
  },
  "fail_closed_conditions": [
    "taskpack_manifest_missing_or_invalid",
    "taskpack_component_missing_or_schema_id_drift",
    "taskpack_component_hash_mismatch",
    "runner_entrypoint_missing",
    "runner_adapter_binding_missing",
    "runner_adapter_registry_missing_or_malformed",
    "runner_adapter_resolution_ambiguous",
    "runner_kernel_imports_apps_api_detected",
    "pre_write_validation_bypass_detected",
    "pre_write_validation_exception_path_bypass_detected",
    "candidate_change_plan_missing_or_invalid",
    "candidate_change_plan_canonicalization_drift",
    "candidate_change_plan_file_operations_ordering_drift",
    "candidate_change_plan_ast_missing_or_invalid",
    "candidate_change_plan_validation_apply_ast_mismatch",
    "candidate_change_plan_raw_diff_apply_path_detected",
    "candidate_change_plan_fuzzy_hunk_apply_detected",
    "candidate_change_plan_malformed_hunk_detected",
    "candidate_change_plan_overlapping_hunks_detected",
    "candidate_change_plan_diff_normalization_drift",
    "candidate_change_plan_policy_validation_failed",
    "model_suggested_command_execution_detected",
    "command_execution_interception_unavailable",
    "undeclared_command_execution_detected",
    "allowlist_violation_detected",
    "forbidden_effect_detected",
    "adapter_id_unknown",
    "dry_run_payload_nondeterminism",
    "dry_run_model_invocation_detected",
    "dry_run_network_guard_unavailable",
    "dry_run_subprocess_execution_detected",
    "dry_run_outbound_network_attempt_detected",
    "dry_run_workspace_mutation_detected",
    "policy_rejection_diagnostic_missing_or_malformed",
    "provenance_artifact_missing_or_hash_drift",
    "provenance_hash_subject_contains_nondeterministic_fields",
    "required_closeout_block_missing",
    "stop_gate_metric_keyset_drift",
    "required_contract_violation_reported_as_warning",
    "required_structural_violation_captured_as_warning_channel"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## T1) Codex SDK Constrained Runner + Policy Validation MVP (`V33-B`)

### Goal

Introduce deterministic, taskpack-driven runner execution with canonical candidate-change-plan evaluation before any write/commit side effects.

Lock-class rationale:

- this slice is `L1` because it introduces a governance-critical execution surface, even though runtime/provider semantics remain unchanged.

### Scope

- Add deterministic runner entrypoint:
  - consume compiled taskpack bundle and verify manifest/component integrity,
  - resolve adapter surface through deterministic adapter registry + adapter id selection (no direct `apps/api` imports in kernel),
  - adapter match predicate is exact case-sensitive `adapter_id` equality only (no prefix/partial matching),
  - fail closed on missing/malformed registry, ambiguous adapter resolution, or unknown adapter id.
- Add canonical candidate-change-plan artifact generation:
  - normalize model output into deterministic file-operations + unified-diff payload object and canonical AST,
  - enforce deterministic file-operation ordering (`path`, then `operation_kind`) in canonical candidate plans,
  - enforce unified-diff normalization (`utf-8`, `LF`, timestamp-stripped headers, preserved non-header whitespace),
  - require validator and apply engine to consume the same canonical AST object (raw diff apply paths and fuzzy hunk application are forbidden),
  - reject malformed or overlapping hunks fail closed,
  - hash canonical candidate-change-plan payload for provenance.
- Add command authority enforcement:
  - command execution authority derives from `COMMANDS.json` only,
  - enforce command authority at subprocess invocation interception surface,
  - model-suggested commands outside `COMMANDS.json` are non-authoritative and fail closed.
- Add deterministic policy-validation pass before writes/commit:
  - evaluate canonical candidate AST against `ALLOWLIST.json` and `FORBIDDEN.json`,
  - in v45, forbidden-effect evaluation is restricted to forbidden touches and closed-enum forbidden operation kinds (no inferred semantic-effects lane),
  - enforce single no-bypass pre-write gate semantics across normal and exception paths,
  - emit structured deterministic rejection diagnostics on policy failure,
  - block apply/commit on policy failure (fail closed).
- Add deterministic dry-run mode (`--dry-run`):
  - dry-run is model-free in v45 and requires explicit candidate-change-plan artifact input,
  - render final execution payload and candidate-change-plan/provenance preview artifacts only,
  - initialize explicit dry-run network guards that block outbound socket/HTTP client calls,
  - forbid subprocess execution in dry-run in v45 (to prevent guard-scope escape),
  - perform no outbound network execution and no workspace mutation outside designated preview output root (`artifacts/agent_harness/v45/dry_run_preview`),
  - allow only directory creation and file writes under the preview output root in dry-run.
- Emit deterministic runner provenance artifact:
  - include taskpack manifest hash, adapter identity, candidate-change-plan hash, policy-validation result, and exit status.
  - exclude non-deterministic fields (`wall_clock_timestamp`, host identity, absolute paths) from hashed provenance subject.
- Preserve stop-gate continuity:
  - no metric-key additions,
  - no schema-family fork.

### Locks

- Runner-authority lock is frozen:
  - execution authority is taskpack-driven only.
- Adapter-boundary lock is frozen:
  - harness kernel defines runner interface and may not hard-depend on `apps/api`.
- Adapter-selection lock is frozen:
  - adapter selection is deterministic by `adapter_id` against runner adapter registry contract,
  - match predicate is exact case-sensitive `adapter_id` equality only.
- Pre-write validation lock is frozen:
  - candidate-change-plan policy validation must pass before any workspace write/commit.
- Pre-write no-bypass lock is frozen:
  - write/apply/commit paths must pass through one deterministic validation gate under both normal and exception/error control flow.
- Candidate-plan authority lock is frozen:
  - policy decisions derive from canonical candidate-change-plan artifact only.
- Candidate-plan AST coupling lock is frozen:
  - policy validation and patch application must consume the same canonical AST object,
  - raw diff application and fuzzy hunk application are forbidden in this arc.
- Candidate-plan normalization lock is frozen:
  - unified-diff normalization profile is frozen (`utf-8`, `LF`, timestamp-free headers, preserved non-header whitespace).
- Candidate-plan file-operations ordering lock is frozen:
  - canonical candidate-plan `file_operations` ordering is deterministic (`path`, then `operation_kind`).
- Command-authority lock is frozen:
  - command execution authority derives from `COMMANDS.json` only,
  - model-suggested commands are non-authoritative,
  - subprocess-level command execution interception is required.
- Anti-injection lock is frozen:
  - repository content and model natural-language claims cannot override taskpack authority.
- Forbidden-effect definition lock is frozen:
  - v45 forbidden-effect evaluation is restricted to forbidden touches and forbidden operation kinds from `FORBIDDEN.json`,
  - forbidden operation kinds are closed-enum values in this arc (`delete`, `rename`, `chmod`),
  - inferred semantic-effect enforcement is deferred beyond v45.
- Dry-run lock is frozen:
  - `--dry-run` path is model-free, side-effect free, and deterministic for identical taskpack + candidate-change-plan input bytes.
- Dry-run network/mutation lock is frozen:
  - explicit network guard initialization is required and missing/disabled network guard fails closed,
  - subprocess execution is forbidden in dry-run in v45,
  - outbound socket/HTTP attempts in dry-run fail closed,
  - dry-run mutation is forbidden under repo root except designated preview output root,
  - only directory creation and file writes are allowed under preview output root.
- Rejection-diagnostics lock is frozen:
  - policy-validation failures must emit deterministic structured rejection diagnostics artifacts,
  - diagnostics ordering includes integer-ascending `hunk_index` tie-break after issue code and target path,
  - missing or malformed rejection diagnostics on policy failure is invalid and fail closed.
- Provenance hash-subject lock is frozen:
  - deterministic hashed provenance excludes non-deterministic environment/time/host fields.
- Severity lock is frozen:
  - required violations are errors and fail closed.

### Acceptance

- Constrained runner rejects non-authorized edits/commands deterministically.
- Policy validation blocks apply/commit deterministically on allowlist/forbidden violations.
- Policy-validation failures emit deterministic structured rejection diagnostics with path/hunk/line-range context.
- Dry-run mode emits byte-identical payload/provenance preview artifacts for identical taskpack + candidate-change-plan input bytes.
- Runner provenance artifacts are deterministic and hash-stable across reruns.

## T2) Runner Determinism/Fail-Closed Guard Suite (`V33-B`)

### Goal

Prove v45 runner integration behavior is deterministic, fail-closed, and continuity-preserving.

### Scope

- Add/adjust deterministic tests/guards for:
  - taskpack manifest/component integrity enforcement,
  - runner entrypoint and adapter-binding presence checks,
  - adapter-registry schema presence and deterministic adapter-resolution checks,
  - static import-graph guard for harness-kernel `apps/api` isolation,
  - detection of harness-kernel direct `apps/api` import attempts,
  - pre-write no-bypass validation gate checks under normal and exception-path flows,
  - candidate-change-plan canonicalization determinism under fixed inputs,
  - candidate-plan `file_operations` ordering determinism under fixed inputs,
  - candidate-change-plan AST coupling enforcement (validation/apply same AST object),
  - fail-closed handling for malformed or overlapping diff hunks,
  - fail-closed handling for raw diff/fuzzy patch application path attempts,
  - candidate-change-plan diff-normalization drift handling under fixed inputs,
  - command-authority enforcement for model-suggested or undeclared commands,
  - fail-closed policy-validation handling for allowlist violations,
  - fail-closed policy-validation handling for forbidden-effect detection,
  - fail-closed handling for malformed/missing candidate-change-plan artifacts,
  - fail-closed handling for unknown adapter id selection,
  - dry-run model-invocation prohibition,
  - dry-run network-guard initialization requirement enforcement,
  - dry-run subprocess-execution prohibition enforcement,
  - dry-run side-effect prohibition (no outbound network execution, no workspace mutation outside preview output root),
  - dry-run payload/provenance artifact determinism across reruns,
  - deterministic structured rejection-diagnostic emission on policy-validation failure,
  - provenance hash-subject exclusion of non-deterministic fields,
  - required-error-channel enforcement (no warning downgrade for required violations),
  - stop-gate keyset continuity and deterministic cardinality assertions (`80`),
  - continuity-preservation assertions for v36-v44 frozen suites.
- Preserve deterministic environment posture for guard commands:
  - command examples run under `TZ=UTC`, `LC_ALL=C`, and `PYTHONHASHSEED=0` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v45 tests/guards may not introduce new stop-gate metric keys.
- Required-deterministic-env lock is frozen:
  - v45 guards fail closed if deterministic env contract drifts from `TZ=UTC`, `LC_ALL=C`, `PYTHONHASHSEED=0`.
- Required-policy-validation lock is frozen:
  - v45 guards fail closed if apply/commit can occur after policy-validation failure.
- Required-policy-validation-no-bypass lock is frozen:
  - v45 guards fail closed if write/apply/commit can bypass deterministic pre-write validation in any control flow path.
- Required-candidate-plan-ast-coupling lock is frozen:
  - v45 guards fail closed if validation and patch application are not coupled to the same canonical AST object.
- Required-candidate-plan-file-operations-ordering lock is frozen:
  - v45 guards fail closed if canonical candidate-plan `file_operations` ordering drifts from frozen ordering rules.
- Required-dry-run-side-effect lock is frozen:
  - v45 guards fail closed if dry-run performs model invocation, subprocess execution, outbound network execution, or workspace mutation outside preview output root.
- Required-adapter-selection lock is frozen:
  - v45 guards fail closed on adapter-registry drift, ambiguous adapter selection, unknown adapter id resolution, or non-exact adapter-id matching behavior.
- Required-command-authority lock is frozen:
  - v45 guards fail closed on model-suggested or undeclared command execution attempts and missing subprocess interception.
- Required-rejection-diagnostics lock is frozen:
  - v45 guards fail closed if policy failures do not produce deterministic structured rejection diagnostics with stable integer-ascending `hunk_index` ordering.
- Required-provenance-hash-subject lock is frozen:
  - v45 guards fail closed if deterministic provenance hash subject includes non-deterministic fields.
- Required-severity-policy lock is frozen:
  - v45 guards fail closed if required violations are emitted as warnings instead of errors.
- Continuity-preservation lock is frozen:
  - v45 guards fail closed if v36-v44 continuity suites regress.

### Acceptance

- Guard suites pass deterministically across reruns.
- Required runner wiring and fail-closed assertions are green.
- v36-v44 continuity guard suites remain green under v45 scope.

## Stop-Gate Impact (v45)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v45 closeout must include runtime-observability comparison row against v44 baseline.
- v45 closeout must include runner wiring evidence block:
  - block schema is docs-only `v33b_runner_wiring_evidence@1`,
  - required keys are:
    - `schema`
    - `runner_entrypoint`
    - `adapter_surface`
    - `dry_run_supported`
    - `candidate_change_plan_schema`
    - `pre_write_policy_validation_passed`
    - `allowlist_enforcement_passed`
    - `forbidden_effect_enforcement_passed`
    - `provenance_hash`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v44`
    - `notes`

## Error/Exit Policy (v45)

- No new URM error-code family is introduced in this arc.
- Harness diagnostics namespace (`AHK[0-9]{4}`) in this arc is contract-diagnostics authority only and is not a URM runtime error-code family.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add V33-B constrained taskpack runner + candidate-change-plan policy validation`
2. `tests: add v45 runner determinism and fail-closed guard suite`

## Intermediate Preconditions (for v45 start)

1. v44 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v44 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS44.md`
3. Existing v44 taskpack compiler entrypoint remains available at v45 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/compile.py`
4. Existing v44 closeout taskpack artifacts remain available at v45 start:
   - `artifacts/agent_harness/v44/taskpack_profile_registry.json`
   - `artifacts/agent_harness/v44/profiles/v44_closeout_profile.json`
   - `artifacts/agent_harness/v44/taskpacks/v41/v44_closeout/taskpack_manifest.json`
5. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
6. No additional `L2` boundary release beyond v44 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `T1` and `T2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic constrained runner MVP (`V33-B`) is closed and test-covered.
- v45 closeout evidence includes runtime-observability comparison row against v44 baseline and `v33b_runner_wiring_evidence@1` block.
- v36-v44 continuity remains green and unreverted.
- No solver semantics contract delta and no trust-lane regression introduced.
