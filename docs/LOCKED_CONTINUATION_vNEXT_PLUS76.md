# Locked Continuation vNext+76

Status: `V39-E` implementation contract.

## V76 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v39e_synthetic_pressure_mismatch_hybrid_execution_contract@1",
  "target_arc": "vNext+76",
  "target_path": "V39-E",
  "target_scope": "synthetic_pressure_mismatch_hybrid_checkpoint_and_oracle_execution_baseline",
  "registry_schema": "synthetic_pressure_mismatch_rule_registry@1",
  "observation_schema": "synthetic_pressure_mismatch_observation_packet@1",
  "report_schema": "synthetic_pressure_mismatch_conformance_report@1",
  "fix_plan_schema": "synthetic_pressure_mismatch_fix_plan@1",
  "oracle_request_schema": "synthetic_pressure_mismatch_oracle_request@1",
  "oracle_resolution_schema": "synthetic_pressure_mismatch_oracle_resolution@1",
  "checkpoint_trace_schema": "synthetic_pressure_mismatch_checkpoint_trace@1",
  "implementation_package": "adeu_core_ir",
  "registry_reference_fixture": "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus73/synthetic_pressure_mismatch_rule_registry_v73_reference.json",
  "conformance_reference_fixture": "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/synthetic_pressure_mismatch_conformance_report_v74_reference.json",
  "fix_plan_reference_fixture": "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus75/synthetic_pressure_mismatch_fix_plan_v75_reference.json"
}
```

## Slice

- Arc label: `vNext+76`
- Family label: `V39-E`
- Scope label: pressure-mismatch hybrid checkpoint and oracle-execution baseline

## Objective

Introduce a bounded repo-native way to classify pressure-mismatch checkpoints,
materialize typed oracle request and resolution artifacts, and record final checkpoint
disposition under deterministic adjudicator ownership.

This slice freezes the first canonical hybrid execution substrate for:

- `synthetic_pressure_mismatch_oracle_request@1`
- `synthetic_pressure_mismatch_oracle_resolution@1`
- `synthetic_pressure_mismatch_checkpoint_trace@1`
- explicit checkpoint classification
- replay/cache/version pinning
- bounded human escalation and fail-closed hybrid adjudication

The slice remains deliberately prior to patch generation and repo mutation. Its job is
to establish the first released mixed-confidence checkpoint lane that later execution
surfaces may consume without confusing advice, adjudication, and action.

Hybrid adjudication law note:

- the deterministic harness classifies checkpoints first and owns final checkpoint
  disposition;
- the resident coding agent may advise only through typed oracle request/resolution
  artifacts;
- oracle output is never itself authoritative repo mutation;
- oracle output may only feed deterministic adjudication, report materialization, or
  a later advisory artifact under current harness policy.

## Frozen Implementation Decisions

1. First implementation package:
   - place the initial hybrid schemas, models, builders, exports, and replay helpers
     in `packages/adeu_core_ir`.
2. Upstream dependency strategy:
   - `V39-E` must consume released `V39-B`, `V39-C`, and `V39-D` artifacts when a
     checkpoint derives from already-released rules, findings, reports, or fix-plan
     projections;
   - `V39-E` may bind either to released conformance findings or to released
     fix-plan projections depending on the checkpoint source surface;
   - neither released source surface is mandatory for every checkpoint;
   - it may not bypass those released artifacts by synthesizing hybrid checkpoints
     directly from raw repo scans when released bindings already exist.
3. Coverage honesty strategy:
   - the released `V39-C` / `V39-D` fixtures currently exercise deterministic-local
     safe-autofix coverage only;
   - `V39-E` may therefore add committed local hybrid fixtures for
     `oracle_assisted` and `human_only` branches, but those fixtures must bind back to
     released registry rule ids and local subject provenance and must not overclaim
     themselves as released `V39-C` findings.
4. Checkpoint classifier strategy:
   - the canonical classifier in `V39-E` must emit exactly:
     - `deterministic_pass`
     - `deterministic_fail`
     - `oracle_needed`
     - `human_needed`
   - no fifth fallback class is allowed in the first baseline.
5. Adjudication authority strategy:
   - the deterministic harness owns final adjudication and checkpoint trace
     materialization;
   - oracle output remains advisory only and may not write repo state by itself.
6. Final adjudication strategy:
   - the canonical `final_adjudication` vocabulary in `V39-E` must be exactly:
     - `resolved_pass`
     - `resolved_fail`
     - `escalated_human`
   - legal transition law must be frozen exactly as:
     - `deterministic_pass -> resolved_pass`
     - `deterministic_fail -> resolved_fail`
     - `oracle_needed -> resolved_pass | resolved_fail | escalated_human`
     - `human_needed -> escalated_human`
   - no other `checkpoint_class -> final_adjudication` transition is allowed in the
     first baseline.
7. Escalation strategy:
   - the first released baseline permits at most one oracle request / resolution cycle
     per checkpoint;
   - unresolved, contradictory, or unstable oracle output must fail closed into
     `human_needed`.
8. Replay and cache strategy:
   - oracle request identity must pin:
     - source artifact identity,
     - source content or fixture hash,
     - policy source hashes,
     - model id,
     - model version,
     - reasoning effort,
     - request template or evaluator version;
   - cache reuse is allowed only when the full pinned request identity matches
     exactly.

## Required Deliverables

1. New typed ADEU core artifacts:
   - canonical `synthetic_pressure_mismatch_oracle_request@1`
   - canonical `synthetic_pressure_mismatch_oracle_resolution@1`
   - canonical `synthetic_pressure_mismatch_checkpoint_trace@1`
   - mirrored JSON schema exports for all three in:
     - `packages/adeu_core_ir/schema/`
     - `spec/`
2. Checkpoint trace law that makes source binding, checkpoint class, and adjudication
   explicit, including:
   - trace-level binding to:
     - released registry schema id,
     - released registry fixture path,
     - released conformance report schema id or fix-plan schema id when applicable,
     - released source fixture path or explicit local hybrid fixture path,
     - deterministic adjudicator provenance;
   - checkpoint entries that bind:
     - `checkpoint_id`,
     - `checkpoint_class`,
     - `source_kind`,
     - `rule_id`,
     - `signal_kind`,
     - `harm_kind`,
     - `evidence_regime`,
     - `allowed_action`,
     - `resolution_route`,
     - `subject_kind`,
     - `subject_ref`,
     - `local_subject_anchor` or equivalent bounded local anchor,
     - exact `source_finding_id` and `source_projected_item_id` when the checkpoint
       derives from released `V39-C` / `V39-D` artifacts,
     - `oracle_request_id` when `checkpoint_class = oracle_needed`,
     - `oracle_resolution_id` when an oracle resolution exists,
     - `final_adjudication`;
   - `source_kind` must be the exact starter vocabulary:
     - `released_conformance_finding`,
     - `released_fix_plan_projection`,
     - `local_hybrid_fixture`;
   - `final_adjudication` must be the exact starter vocabulary:
     - `resolved_pass`,
     - `resolved_fail`,
     - `escalated_human`;
   - exact duplicate checkpoint identities inside one trace must be rejected;
   - checkpoint identity must minimally be determined by the tuple:
     - `source_kind`,
     - exact source binding:
       - `source_finding_id`, or
       - `source_projected_item_id`, or
       - local hybrid fixture identity,
     - `rule_id`,
     - `subject_ref`,
     - `local_subject_anchor`;
   - final adjudication must obey the frozen transition law:
     - `deterministic_pass -> resolved_pass`
     - `deterministic_fail -> resolved_fail`
     - `oracle_needed -> resolved_pass | resolved_fail | escalated_human`
     - `human_needed -> escalated_human`;
   - any carried-through rule, report, or fix-plan metadata must match the released
     upstream artifact exactly when such an artifact is referenced.
3. Oracle request law that:
   - binds one request to one exact checkpoint;
   - may be emitted only when `checkpoint_class = oracle_needed`;
   - `deterministic_pass`, `deterministic_fail`, and `human_needed` checkpoints must
     not emit an oracle request;
   - carries pinned replay identity across:
     - source ids,
     - source hashes,
     - policy source hashes,
     - model id,
     - model version,
     - reasoning effort,
     - request-template or evaluator version;
   - carries only bounded local context needed for interpretation;
   - may not embed direct repo mutation authority, hidden tool grants, or live network
     state as canonical evidence.
4. Oracle resolution law that:
   - binds one resolution to one exact request;
   - records model id, model version, reasoning effort, and bounded resolution
     provenance;
   - records whether the oracle output was:
     - `advisory_support`,
     - `advisory_reject`,
     - `inconclusive`,
     - `contradictory`;
   - records raw-output hash or equivalent deterministic local provenance;
   - remains advisory only and may not itself authorize repo mutation;
   - may interpret a checkpoint but may not mint:
     - new rule metadata,
     - new subject provenance,
     - new mutation authority;
   - must fail closed into `human_needed` when resolution state is unstable,
     contradictory, or replay identity is inconsistent.
5. Deterministic adjudicator/builders that:
   - consume released registry, conformance, and fix-plan fixtures where applicable;
   - consume committed local hybrid fixtures for `oracle_assisted` and `human_only`
     route coverage where no released deterministic observation path exists yet;
   - emit `oracle_needed` only for checkpoints whose released or fixture-bound
     `resolution_route = oracle_assisted`;
   - emit `human_needed` directly for checkpoints whose `resolution_route = human_only`;
   - keep `deterministic_only` checkpoints fully deterministic in this slice;
   - may derive checkpoints either from released conformance findings or from
     released fix-plan projections depending on source surface;
   - reject unsupported route/class combinations;
   - reject cache reuse when pinned identity does not match exactly.
6. Committed reference fixtures that include:
   - one accepted deterministic checkpoint trace derived from the released v75 fix
     plan reference;
   - one oracle-assisted hybrid fixture set derived from committed local subject
     evidence and a released registry rule with `resolution_route = oracle_assisted`,
     including request, resolution, and trace artifacts;
   - one human-only checkpoint trace fixture derived from committed local subject
     evidence and a released registry rule with `resolution_route = human_only`;
   - one rejected invalid replay/cache or contradictory-resolution case proving
     fail-closed behavior.
7. Python tests covering:
   - schema/model validation for all three new artifacts;
   - schema export parity;
   - deterministic checkpoint replay from released fixtures;
   - oracle-assisted replay from committed local hybrid fixtures;
   - human-only direct escalation without oracle request emission;
   - replay/cache identity exact-match enforcement;
   - fail-closed rejection for contradictory or unstable oracle resolutions;
   - single-round oracle-attempt enforcement;
   - preservation of anti-authorship and anti-score boundaries;
   - bounded linkage back to released upstream artifacts or explicitly declared local
     hybrid fixtures.

## Hard Constraints

- `V39-E` may not govern against "AI-ness" or authorship. The governed object remains
  pressure-mismatch drift only.
- `V39-E` may not ship:
  - patch artifacts,
  - automatic repo mutation,
  - file-edit payloads,
  - generic resident-agent orchestration outside typed checkpoint requests.
- Oracle output is advisory only in this slice:
  - never authoritative repo mutation;
  - never direct edit instruction;
  - never standalone merge-worthiness or urgency signal.
- Oracle resolutions may interpret checkpoints only:
  - never mint new rule metadata;
  - never mint new subject provenance;
  - never mint new mutation authority.
- The deterministic harness remains the only authority over final checkpoint
  adjudication and trace materialization.
- The released `V39-C` / `V39-D` baseline remains intentionally deterministic-local;
  any oracle-assisted or human-only coverage added in `V39-E` must remain explicitly
  local-fixture-driven until a later lock widens released observation coverage.
- `V39-E` may not silently widen into repo-wide scanning, new detector rollout, or a
  hidden second policy-authoring lane.
- `V39-E` may not depend on live GitHub state or live network responses as canonical
  evaluation evidence.
- One oracle round trip is the maximum in the first released baseline.
- Cache reuse requires exact replay identity equality.
- Requests may be emitted only for `oracle_needed`.
- `deterministic_pass`, `deterministic_fail`, and `human_needed` checkpoints must not
  emit oracle requests.
- `checkpoint_class`, `source_kind`, `final_adjudication`, and any posture labels
  must remain bounded vocabularies rather than hidden scalar scores.

## PR Shape

- Single integrated PR.

Rationale:

- the new hybrid schemas, builders, fixtures, tests, and arc docs are tightly coupled
  and should land together to keep the checkpoint/oracle lane internally consistent.
