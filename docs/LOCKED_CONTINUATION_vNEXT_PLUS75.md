# Locked Continuation vNext+75

Status: `V39-D` implementation contract.

## V75 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v39d_synthetic_pressure_mismatch_fix_plan_contract@1",
  "target_arc": "vNext+75",
  "target_path": "V39-D",
  "target_scope": "synthetic_pressure_mismatch_fix_plan_and_policy_projection_baseline",
  "registry_schema": "synthetic_pressure_mismatch_rule_registry@1",
  "observation_schema": "synthetic_pressure_mismatch_observation_packet@1",
  "report_schema": "synthetic_pressure_mismatch_conformance_report@1",
  "fix_plan_schema": "synthetic_pressure_mismatch_fix_plan@1",
  "implementation_package": "adeu_core_ir",
  "conformance_reference_fixture": "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/synthetic_pressure_mismatch_conformance_report_v74_reference.json"
}
```

## Slice

- Arc label: `vNext+75`
- Family label: `V39-D`
- Scope label: pressure-mismatch fix-plan and policy projection baseline

## Objective

Introduce a bounded repo-native way to consume the released pressure-mismatch
conformance lane and emit a canonical fix plan with explicit forward-agent and
post-optimizer projections.

This slice freezes the first canonical planning substrate for:

- `synthetic_pressure_mismatch_fix_plan@1`
- role-separated policy projection
- bounded safe-autofix planning only for released candidate findings
- valid no-op fix-plan replay for no-finding and non-plannable conformance inputs

The slice remains deliberately prior to actual repo mutation and hybrid oracle
execution. Its job is to establish the first released plan surface that later
execution lanes may consume without confusing planning with action.

Planning law note:

- fix plans materialize proposed next-step structure from released conformance inputs;
- they may project different guidance to different agent roles;
- they must stay advisory and must not authorize repo mutation by themselves.

## Frozen Implementation Decisions

1. First implementation package:
   - place the initial fix-plan schema, model, builders, exports, and replay helpers
     in `packages/adeu_core_ir`.
2. Input dependency strategy:
   - `V39-D` must consume the released
     `synthetic_pressure_mismatch_conformance_report@1` substrate from `V39-C`;
   - it may not bypass that substrate by deriving plans directly from raw subjects or
     repo-wide scans.
3. Policy projection strategy:
   - the fix plan must keep forward-agent and post-optimizer projections structurally
     separate;
   - it may not collapse both roles into one undifferentiated advice list.
4. Safe-autofix planning strategy:
   - `V39-D` may plan safe autofix only when the source conformance report already
     carries the finding as a released `safe_autofix_candidate`;
   - that planning remains candidate-only and must not execute diffs or file changes.
5. Source finding binding strategy:
   - every projected plan item must trace back to one exact released source finding or
     source candidate identity rather than only to a finding-shaped area;
   - `V39-D` must therefore freeze a stable `source_finding_id` or equivalent exact
     source item identity in the canonical artifact.

## Required Deliverables

1. New typed ADEU core artifact:
   - canonical `synthetic_pressure_mismatch_fix_plan@1`
   - mirrored JSON schema exports in:
     - `packages/adeu_core_ir/schema/`
     - `spec/`
2. Fix-plan law that makes source, route, and projected next-step semantics explicit,
   including:
   - plan-level binding to:
     - released registry schema id,
     - released registry fixture path,
     - released conformance report schema id,
     - released conformance report fixture or deterministic report provenance,
     - aggregated observation packet ids or equivalent report-carried packet set;
   - separate projection surfaces for:
     - forward-agent policy projection,
     - post-optimizer policy projection;
   - projected plan items that bind:
     - `projected_item_id`,
     - `source_finding_id`,
     - `rule_id`,
     - `signal_kind`,
     - `harm_kind`,
     - `allowed_action`,
     - `resolution_route`,
     - source `observation_packet_id`,
     - source `local_observation_locator` or equivalent bounded anchor,
     - `plan_posture`,
     - `projection_kind`,
     - `projected_next_step_text`;
   - `plan_posture` must be a bounded vocabulary, for example:
     - `safe_autofix_candidate`,
     - `review_required`,
     - `forward_guidance_only`,
     - `post_optimizer_guidance_only`,
     - `meta_artifact_correction_only`,
     - `no_op`;
   - `projection_kind` must be a bounded vocabulary, for example:
     - `guidance`,
     - `candidate_action`,
     - `review_prompt`,
     - `meta_artifact_correction`;
   - one source finding may project to zero, one, or multiple role-scoped plan items,
     but exact duplicate projected-item identities remain forbidden.
3. Plan integrity law that:
   - requires any carried-through rule metadata to match the released registry rule
     exactly;
   - requires any carried-through finding refs to match the released conformance
     report exactly;
   - rejects exact duplicate projected item identities inside one fix plan;
   - rejects plan items that claim direct mutation authority.
4. Projection semantics that:
   - derive forward-agent guidance from released `forward_agent_policy`;
   - derive post-optimizer guidance from released `post_optimizer_policy`;
   - may summarize or select from released role policy, but may not invent
     contradictory policy;
   - keep `safe_autofix` planning restricted to the narrow deterministic-local subset
     already surfaced by `V39-C`;
   - keep review-required planning distinct from safe-autofix planning;
   - preserve the anti-authorship and anti-score boundaries.
5. Committed reference fixtures that include:
   - one accepted fix plan derived from the released v74 reference conformance report;
   - one valid no-op / no-finding fix plan derived from the released v74 no-finding
     report;
   - one rejected invalid plan-input case proving fail-closed behavior when the source
     report does not authorize the claimed planning route.
6. Python tests covering:
   - schema/model validation for the new artifact;
   - schema export parity;
   - deterministic fix-plan replay from released report fixtures;
   - valid empty/no-op fix-plan behavior;
   - fail-closed rejection for plan items that bypass source report candidates;
   - duplicate projected-item rejection;
   - preservation of anti-authorship and anti-score boundaries;
   - bounded linkage back to the released registry and conformance fixtures.

## Hard Constraints

- `V39-D` may not govern against "AI-ness" or authorship. The governed object remains
  pressure-mismatch drift only.
- `V39-D` may not ship:
  - patch artifacts,
  - automatic repo mutation,
  - file-edit payloads,
  - oracle request artifacts,
  - oracle resolution artifacts,
  - checkpoint adjudication logic.
- The fix plan must remain advisory:
  - no direct mutation authorization;
  - no implicit "apply now" field;
  - no hidden merge-worthiness or urgency scalar.
- Safe-autofix planning in this slice is limited to findings already surfaced by
  released `safe_autofix_candidates` in `V39-C`.
- `safe_autofix` in `V39-D` means proposed next-step candidate only:
  - never an executable payload;
  - never an edit instruction;
  - never direct mutation authority.
- `V39-D` may not silently widen into repo-wide scanning, new detector execution, or
  semantic-ambiguous adjudication.
- Valid no-op outputs are allowed in this slice:
  - a fix plan may validly contain zero projected items when the source report carries
    zero findings;
  - a fix plan may also validly contain zero projected items when findings are present
    but none are plannable inside the bounded `V39-D` route.
- `resolution_route` remains carried-through descriptive metadata in this slice and
  may not be interpreted as proof that `V39-E` hybrid infrastructure already exists.

## PR Shape

- Single integrated PR.

Rationale:

- the new fix-plan schema, builders, fixtures, tests, and arc docs are tightly coupled
  and should land together to keep the policy-projection lane internally consistent.
