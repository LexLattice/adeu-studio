# Assessment vNext+112 Edges

Status: post-closeout edge assessment for `V48-A` (April 2, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS112_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Hidden Policy Composition

- Risk:
  `V48-A` could have quietly become a policy-composition algebra instead of a bounded
  single-policy bridge starter.
- Response:
  freeze exactly one released `V47-E` policy source and fail closed on extra carriers.
- Closeout Evidence:
  cardinality validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`,
  reject fixture
  `packages/adeu_agent_harness/tests/fixtures/v48a/reject_multiple_policy_sources_spec.json`,
  and test `test_v48a_rejects_multiple_policy_sources`.

### Edge 2: Hidden Scope Union

- Risk:
  the bridge could silently widen from one released scope source into implicit scope
  union, scope widening, or ambient repo discovery.
- Response:
  require exactly one released `V45` scope source plus exactly one released `V45-F`
  admission entry and reject mismatched lineage.
- Closeout Evidence:
  lineage checks in
  `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`,
  reject fixture
  `packages/adeu_agent_harness/tests/fixtures/v48a/reject_scope_binding_entry_mismatch_spec.json`,
  and test `test_v48a_rejects_mismatched_scope_binding_entry`.

### Edge 3: `V47-E` Carrier Authority Laundering

- Risk:
  because `V48-A` admits a released `V47-E` row as its starter policy carrier, the row
  itself could be overread as terminal authority rather than a carrier whose bound
  released `D-IR` clause remains upstream authority.
- Response:
  resolve the admitted `V47-E` row to one explicit `policy_authority_clause_ref` and
  keep the row non-self-authorizing apart from that clause lineage.
- Closeout Evidence:
  bound-clause resolution in
  `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`,
  committed profile fixture
  `packages/adeu_agent_harness/tests/fixtures/v48a/reference_anm_taskpack_binding_profile.json`,
  and tests `test_v48a_reference_profile_replays_deterministically` plus
  `test_v48a_model_accepts_committed_reference_payload`.

### Edge 4: `V45-F` Admission Overreach

- Risk:
  the admitted `V45-F` binding entry could be overread as direct execution-envelope
  authority rather than an admission-only prerequisite for constrained scope use.
- Response:
  require the entry to resolve to the same scope surface and binding subject while
  keeping it admission-only.
- Closeout Evidence:
  `V45-F` admission checks in
  `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`,
  committed profile fixture,
  and test `test_v48a_rejects_mismatched_scope_binding_entry`.

### Edge 5: Projection-Conflict Drift

- Risk:
  because no precedence algebra is selected in `V48-A`, contradictory allowlist /
  forbidden / command / evidence-slot projections could otherwise validate while
  remaining semantically ambiguous.
- Response:
  make contradictory projections invalid and fail closed rather than choosing a local
  winner.
- Closeout Evidence:
  projection-conflict validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`,
  reject fixture
  `packages/adeu_agent_harness/tests/fixtures/v48a/reject_projection_conflict_spec.json`,
  and test `test_v48a_rejects_projection_conflicts`.

### Edge 6: Kernel Category / Shape Drift

- Risk:
  command or evidence-slot projection could quietly turn into prose-shaped guidance or
  ad hoc categories instead of released kernel-shaped carriers.
- Response:
  keep mappings exact to allowlist, forbidden, commands, and evidence slots, with
  command/evidence payloads frozen to released kernel shapes.
- Closeout Evidence:
  authoritative/mirror schema pair
  `packages/adeu_agent_harness/schema/anm_taskpack_binding_profile.v1.json` and
  `spec/anm_taskpack_binding_profile.schema.json`,
  export logic in
  `packages/adeu_agent_harness/src/adeu_agent_harness/export_schema.py`,
  and test `test_exported_schema_has_stable_contract_markers`.

### Edge 7: Prompt Authority Drift

- Risk:
  prompt text, chat prose, or `AGENTS.md` could remain de facto execution authority
  even after a typed boundary exists.
- Response:
  freeze projection-only posture and make prompt-boundary conflict fail closed.
- Closeout Evidence:
  prompt-authority validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`,
  reject fixture
  `packages/adeu_agent_harness/tests/fixtures/v48a/reject_prompt_authority_drift_spec.json`,
  and test `test_v48a_rejects_prompt_authority_drift`.

### Edge 8: Stale-Lineage Reuse

- Risk:
  a seemingly valid binding profile could reuse stale or dangling released policy /
  scope lineage and still look structurally plausible.
- Response:
  require snapshot coherence, scope-entry coherence, and fail-closed unresolved-lineage
  handling across the released `V45` / `V47` joins.
- Closeout Evidence:
  same-snapshot/source-scope validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`,
  committed reference spec
  `packages/adeu_agent_harness/tests/fixtures/v48a/reference_taskpack_binding_spec.json`,
  and reject coverage in `test_v48a_rejects_mismatched_scope_binding_entry`.

### Edge 9: Malformed Command Payload Leakage

- Risk:
  malformed command projection payloads could leak raw `TypeError` or ambient coercion
  instead of structured fail-closed binding errors.
- Response:
  validate command rows and `env_overrides` explicitly and raise typed binding errors.
- Closeout Evidence:
  command validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`
  and test `test_v48a_rejects_malformed_command_env_overrides_fail_closed`.

### Edge 10: Absolute-Path Schema Contamination

- Risk:
  exported schemas could accidentally embed repo-local or Windows absolute path
  material and undermine deterministic replay.
- Response:
  guard exported schema payloads against absolute path material and rerun export
  deterministically.
- Closeout Evidence:
  path guard in
  `packages/adeu_agent_harness/src/adeu_agent_harness/export_schema.py`
  and tests `test_schema_export_rerun_is_clean_and_deterministic`,
  `test_exported_schema_contains_no_absolute_path_material`, and
  `test_absolute_path_guard_rejects_single_backslash_windows_paths`.

### Edge 11: Early Compiler / Manifest Widening

- Risk:
  a first bridge slice could silently widen into taskpack manifest, bundle,
  attestation, or conformance release before the binding doctrine is stable.
- Response:
  keep `V48-A` bounded to one binding-profile surface only and leave actual compiled
  taskpack carriers to `V48-B`.
- Closeout Evidence:
  bounded lock scope in `docs/LOCKED_CONTINUATION_vNEXT_PLUS112.md`,
  shipped implementation footprint under
  `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py` plus
  `packages/adeu_agent_harness/src/adeu_agent_harness/export_schema.py`,
  and absence of new manifest / attestation / conformance schema surfaces in the
  committed `v112` release.

### Edge 12: Single-Worker Topology Drift

- Risk:
  a first binding slice could quietly grow worker-count, topology, or decomposition
  semantics before the single-worker boundary is proven.
- Response:
  freeze exactly one worker subject kind and keep multi-worker topology deferred.
- Closeout Evidence:
  worker-kind const in the released schema pair,
  committed profile fixture
  `packages/adeu_agent_harness/tests/fixtures/v48a/reference_anm_taskpack_binding_profile.json`,
  and test `test_exported_schema_has_stable_contract_markers`.

### Edge 13: Authority Expansion Through Binding Rows

- Risk:
  because `V48` terminates in execution-envelope carriers, the first slice could be
  overread as granting execution, approval, waiver, or deferral authority directly.
- Response:
  keep the released surface doctrine-first and non-executive, with no authority
  expansion beyond what upstream released policy already allows.
- Closeout Evidence:
  frozen anti-overreach scope in `docs/LOCKED_CONTINUATION_vNEXT_PLUS112.md`,
  released profile fixture, and absence of any widened execution/approval surfaces in
  the shipped `adeu_agent_harness` implementation files.

### Edge 14: Package-Boundary Sprawl

- Risk:
  the bridge could sprawl back into `adeu_repo_description`,
  `adeu_semantic_source`, or `adeu_commitments_ir` instead of first stabilizing as a
  harness-owned bridge surface.
- Response:
  keep `V48-A` bounded to `adeu_agent_harness` and consume released `V45` / `V47`
  artifacts as upstream authority inputs only.
- Closeout Evidence:
  shipped implementation footprint in
  `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`,
  `packages/adeu_agent_harness/src/adeu_agent_harness/export_schema.py`,
  and bounded package selection in `docs/LOCKED_CONTINUATION_vNEXT_PLUS112.md`.

## Current Judgment

- `V48-A` was the right first `V48` move because `V45` already shipped descriptive
  scope lineage, `V47` already shipped downstream policy-carrying consumer lineage,
  and the harness already shipped generic kernel categories, while the typed bridge
  between those released surfaces remained missing.
- the shipped result is properly narrow: one binding profile, one policy carrier, one
  scope carrier, one admission entry, one worker, and kernel-shaped projection only.
- `V48-B` is now the right next move because the binding doctrine is released on
  `main`, while actual deterministic taskpack derivation remains a separate and still
  unshipped family lane.
