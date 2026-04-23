# Draft ADEU UX Ergonomic Instantiation Adjudication V67C Implementation Mapping v0

Status: support note for the planned `V67-C` advisory runtime / conformance
hardening pass after the bounded `V67-B` adjudication engine is expected to ship
on `main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a bounded
`V67-C` slice should bridge shipped ergonomic adjudication expectations to
realized runtime or conformance evidence without introducing sovereign runtime
personalization, overriding the released UX governance conformance family, or
minting new design authority from runtime traces alone.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v52.md`
- `docs/ARCHITECTURE_ADEU_UX_ERGONOMIC_INSTANTIATION_ADJUDICATION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_UX_ERGONOMIC_INSTANTIATION_ADJUDICATION_V67_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_UX_ERGONOMIC_INSTANTIATION_ADJUDICATION_V67A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_UX_ERGONOMIC_INSTANTIATION_ADJUDICATION_V67B_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- the shipped `V67-A` ergonomic language and validators
- the shipped `V67-B` bounded adjudication behavior
- the released UX governance diagnostics / conformance family:
  - `ux_morph_diagnostics@1`
  - `ux_conformance_report@1`
- the rule that runtime evidence may constrain but may not mint new constitutional
  semantics
- the rule that runtime measurement does not by itself authorize adaptive runtime
  morph switching.

## Re-Author With Repo Alignment

`V67-C` should remain advisory and bridge-oriented.

It should decide only:

- whether a realized runtime / conformance evidence bundle is consistent with a
  shipped ergonomic adjudication expectation;
- whether the adjudication was missing runtime evidence that was explicitly
  required by measurement obligations;
- whether there is visible drift between:
  - expected targetability / visibility / readability posture
  - observed realized posture
- whether the family deserves later hardening or fixture expansion.

It should keep:

- no autonomous runtime morph selection
- no self-updating ergonomic policy
- no runtime override of released constitutional or projection law
- no screenshot-only authority
- no opening of a generic personalization engine.

`V67-C` should choose a typed advisory output posture rather than staying test-
helper-only.

Candidate `V67-C` surfaces:

- `ux_ergonomic_runtime_measurement_evidence@1`
- `ux_ergonomic_runtime_bridge_report@1`

## Runtime Bridge Posture

Expected consumed basis:

- shipped `ux_ergonomic_adjudication_request@1`
- shipped computed `ux_ergonomic_adjudication_result@1`
- released `ux_morph_diagnostics@1`
- released `ux_conformance_report@1`
- runtime or replay measurement evidence only where explicitly available.

Expected bridge duties:

- verify source refs and hashes across adjudication and realized evidence
- compare measurement obligations against realized measurement evidence
- surface mismatch families such as:
  - `runtime_source_hash_mismatch`
  - `runtime_missing_measurement_for_required_obligation`
  - `runtime_measurement_provenance_inadmissible`
  - `runtime_candidate_profile_not_realized`
  - `runtime_targetability_below_adjudicated_floor`
  - `runtime_text_floor_below_adjudicated_floor`
  - `runtime_visibility_drift_from_adjudicated_claim`
  - `runtime_same_context_reveal_drift`
  - `runtime_required_evidence_not_observed`
  - `runtime_trust_boundary_not_observed`
  - `runtime_commit_gate_not_observed_or_not_targetable`
  - `runtime_unexpected_route_transition`
  - `runtime_unknown_component_ref`
- keep outcomes advisory unless a later lock explicitly upgrades them.

## Output Posture

`V67-C` should not mutate `ux_morph_diagnostics@1` or
`ux_conformance_report@1`. Its bounded replayable output should instead be:

- one typed realized-measurement evidence artifact:
  - `ux_ergonomic_runtime_measurement_evidence@1`
- one typed advisory bridge report:
  - `ux_ergonomic_runtime_bridge_report@1`

Those artifacts should remain:

- non-entitling
- non-sovereign
- source-hash-bound
- explicit about consumed adjudication and conformance lineage
- explicit about advisory-only bridge status.

Recommended `ux_ergonomic_runtime_measurement_evidence@1` row direction:

- `component_ref`
- `candidate_profile_id`
- `measured_bounding_box_css_px`
- `computed_font_size_css_px`
- `computed_line_height_css_px`
- `observed_visibility_state`
- `observed_reveal_transition_or_none`
- `provenance_state`
- `source_kind`
- `source_ref`

Required evidence-level fields:

- `reference_surface_family`
- `reference_instance_id`
- `candidate_profile_id`
- `request_ref`
- `adjudication_result_ref`
- `source_artifact_refs`
- `source_artifact_hashes`
- `measurement_rows`

Recommended advisory bridge statuses:

- `advisory_clean`
- `advisory_drift_detected`
- `advisory_incomplete_missing_evidence`
- `invalid_basis_mismatch`
- `invalid_runtime_evidence_shape`

## Do Not Import

- a runtime adaptation daemon
- automatic personalized layout mutation
- platform-specific hidden override paths
- new generic UX diagnostic sovereignty outside the released conformance family
- heuristically “improved” layout choice without explicit family authorization.

## Likely Implementation Surfaces

- bridge helpers near the ergonomic family implementation
- `packages/adeu_core_ir/schema/ux_ergonomic_runtime_measurement_evidence.v1.json`
- `packages/adeu_core_ir/schema/ux_ergonomic_runtime_bridge_report.v1.json`
- `spec/ux_ergonomic_runtime_measurement_evidence.schema.json`
- `spec/ux_ergonomic_runtime_bridge_report.schema.json`
- additional runtime/conformance comparison tests, likely in a dedicated
  `test_ux_ergonomic_runtime_bridge.py` or equivalent repo-chosen file
- replay/runtime fixtures under the next global fixture/event number after the
  planned `V67-B` family fixtures.

Fixture numbering note:

- `apps/api/fixtures/ux_ergonomics/vnext_plus187/` should follow the global
  next-arc / agent-harness event number, not the highest existing `apps/api`
  fixture directory number.

## Planned Acceptance Shape

`V67-C` should be read as successful only when:

- runtime evidence is compared against shipped adjudication expectations rather than
  replacing them
- missing runtime evidence is visible as a distinct advisory condition
- realized drift is surfaced with stable mismatch families
- advisory bridge statuses stay separate from ergonomic `overall_judgment` and
  released UX conformance judgments
- no advisory output is mistaken for direct layout authority
- no adaptive runtime control loop is smuggled in under the name of conformance.
