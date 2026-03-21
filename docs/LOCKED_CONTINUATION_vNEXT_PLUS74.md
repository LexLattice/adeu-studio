# Locked Continuation vNext+74

Status: `V39-C` implementation contract.

## V74 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v39c_synthetic_pressure_mismatch_observation_contract@1",
  "target_arc": "vNext+74",
  "target_path": "V39-C",
  "target_scope": "synthetic_pressure_mismatch_observation_and_conformance_baseline",
  "registry_schema": "synthetic_pressure_mismatch_rule_registry@1",
  "observation_schema": "synthetic_pressure_mismatch_observation_packet@1",
  "report_schema": "synthetic_pressure_mismatch_conformance_report@1",
  "implementation_package": "adeu_core_ir",
  "registry_reference_fixture": "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus73/synthetic_pressure_mismatch_rule_registry_v73_reference.json"
}
```

## Slice

- Arc label: `vNext+74`
- Family label: `V39-C`
- Scope label: pressure-mismatch observation and conformance baseline

## Objective

Introduce a bounded repo-native way to apply the released pressure-mismatch rule
registry to concrete local subjects through typed observation packets and typed
conformance reports.

This slice freezes the first canonical observation/report substrate for:

- `synthetic_pressure_mismatch_observation_packet@1`
- `synthetic_pressure_mismatch_conformance_report@1`
- deterministic-local detector execution only
- registry-linked observed findings
- local-subject-only replay and deterministic conformance aggregation

The slice remains deliberately prior to fix-plan artifacts and hybrid oracle
execution. Its job is to establish the first released observed-finding lane that later
`V39-D` and `V39-E` slices may consume.

Observation law note:

- observation packets materialize concrete findings against concrete local subjects;
- each observation packet in `V39-C` binds exactly one concrete local subject;
- they must bind back to released registry rule ids;
- they do not authorize repo mutation by themselves.

## Frozen Implementation Decisions

1. First implementation package:
   - place the initial observation/report schemas, models, builders, exports, and
     replay helpers in `packages/adeu_core_ir`.
2. Registry dependency:
   - `V39-C` must consume the released
     `synthetic_pressure_mismatch_rule_registry@1` substrate from `V39-B`;
   - it may not redefine the rule vocabulary locally.
3. Subject source strategy:
   - first released subject inputs must be committed local fixtures;
   - do not treat live repo-wide scans, live GitHub state, or network-dependent inputs
     as canonical evidence in `V39-C`.

## Required Deliverables

1. New typed ADEU core artifacts:
   - canonical `synthetic_pressure_mismatch_observation_packet@1`
   - canonical `synthetic_pressure_mismatch_conformance_report@1`
   - mirrored JSON schema exports for both in:
     - `packages/adeu_core_ir/schema/`
     - `spec/`
2. Observation packet law that makes the subject and finding explicit, including:
   - packet-level binding to:
     - released registry schema id,
     - released registry fixture path,
     - subject kind,
     - subject reference,
     - subject content hash or equivalent deterministic local provenance;
   - finding entries that bind:
     - `rule_id`,
     - `signal_kind`,
     - `harm_kind`,
      - `evidence_regime`,
      - `allowed_action`,
      - `resolution_route`,
      - deterministic detector provenance,
      - local observation locator or equivalent bounded subject anchor;
   - finding entries may carry through rule metadata for replay and debugging
     convenience, but any carried-through `signal_kind`, `harm_kind`,
     `evidence_regime`, `allowed_action`, and `resolution_route` values must match
     the referenced released registry rule exactly;
   - the same `rule_id` may appear more than once for a subject only when each
     finding has a distinct bounded local observation locator;
   - exact duplicate finding identity tuples inside one packet must be rejected.
3. Conformance report law that:
   - summarizes one or more explicit observation packets and must identify the packet
     set it aggregates;
   - aggregates observed findings by evidence regime and allowed action;
   - uses count-based and list-based aggregation only rather than weighted rollups;
   - exposes deterministic-safe candidates separately from broader findings;
   - distinguishes:
     - `safe_autofix_candidates`,
     - `deterministic_high_severity_findings`,
     - `review_only_findings`,
     - `meta_governance_findings`;
   - treats `safe_autofix_candidates` as report-level candidates only and never as
     direct mutation authority;
   - may carry `overall_pressure_mismatch_posture` as a convenience label only;
   - must not introduce a hidden scalar score or merge-worthiness field.
4. Deterministic detector/builders that:
   - consume the released `V39-B` registry and committed local subject fixtures;
   - execute only rules with `evidence_regime = deterministic_local`;
   - fail closed for non-deterministic or unsupported rules in this slice;
   - preserve the anti-authorship boundary;
   - preserve the released `safe_autofix` contract when materializing findings and
     report summaries.
5. Committed reference fixtures that include:
   - one or more accepted local subject fixtures;
   - one or more accepted single-subject observation packet fixtures derived from
     those subjects;
   - one accepted conformance report fixture derived from the packet set;
   - at least one positive deterministic-local finding case;
   - one valid no-finding packet/report case;
   - one rejected unsupported-execution case.
6. Python tests covering:
   - schema/model validation for both new artifacts;
   - schema export parity;
   - deterministic packet/report replay;
   - valid empty packet/report behavior for no-finding replay;
   - fail-closed rejection for unsupported evidence regimes in detector execution;
   - duplicate finding identity rejection;
   - preservation of anti-authorship and anti-score boundaries;
   - bounded linkage back to the released registry fixture.

## Hard Constraints

- `V39-C` may not govern against "AI-ness" or authorship. The governed object remains
  pressure-mismatch drift only.
- `V39-C` may not ship:
  - fix-plan artifacts,
  - automatic repo mutation,
  - oracle request artifacts,
  - oracle resolution artifacts,
  - checkpoint adjudication logic.
- Deterministic execution in this slice is limited to the deterministic-local subset.
- `V39-C` may not silently widen into semantic-ambiguous, static-contextual, or
  meta-governance detector execution.
- The report must remain anti-score by construction:
  - no hidden scalar drift score;
  - no automatic merge-worthiness field;
  - no numeric score masquerading as `overall_pressure_mismatch_posture`.
- Valid no-finding outputs are allowed in this slice:
  - an observation packet may validly contain zero findings;
  - a conformance report may validly summarize zero findings.
- Subject inputs must remain local and committed in this slice:
  - no live GitHub canonicalization;
  - no network-dependent evidence;
  - no repo-wide implicit crawl as the released baseline.
- `resolution_route` remains descriptive carried-through metadata in this slice and may
  not be interpreted as proof that `V39-E` hybrid infrastructure already exists.

## PR Shape

- Single integrated PR.

Rationale:

- the new schemas, builders, fixtures, tests, and arc docs are tightly coupled and
  should land together to keep the observation/report lane internally consistent.
