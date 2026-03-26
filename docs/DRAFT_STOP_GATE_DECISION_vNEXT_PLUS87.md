# Draft Stop-Gate Decision vNext+87

Status: proposed gate for `V41-E`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS87.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- deterministic alignment helpers land in `packages/adeu_architecture_compiler`
  without redefining any released `V41-A` through `V41-D` upstream schema surface;
- the alignment entrypoint consumes the released `V41-A` request, `V41-B`
  settlement, `V41-C` observation, and `V41-D` intended boundary exactly through:
  - `analysis_request_id`
  - `analysis_request_ref`
  - `settlement_frame_id`
  - `settlement_frame_ref`
  - `observation_frame_id`
  - `observation_frame_ref`
  - `architecture_id`
  - `semantic_hash`
  - `source_set_hash`
  - `authority_boundary_policy`;
- the first concrete alignment baseline treats released
  `adeu_architecture_semantic_ir@1` as the authoritative intended comparison
  surface, and any companion intended root-family support refs are consumed only
  through an explicit declared support contract;
- `adeu_architecture_alignment_report@1` is the only newly released artifact family
  in this slice, with authoritative schema under
  `packages/adeu_architecture_compiler/schema/` and mirrored export under `spec/`;
- the request boundary plus settlement frame remain the normative driver of intended
  truth, while the observation frame may constrain, block, or force
  ambiguity/advisory posture but may not become the hidden source of intended
  architecture;
- starter mismatch classes are released at least for:
  - `declared_not_observed`
  - `observed_not_declared`
  - `authority_boundary_drift`
  - `workflow_or_state_drift`
  - `evidence_or_observability_gap`
  - `unresolved_unknown`;
- stable finding-id families start with:
  - `ALIGN-DNO-xxx`
  - `ALIGN-OND-xxx`
  - `ALIGN-ABD-xxx`
  - `ALIGN-WSD-xxx`
  - `ALIGN-EOG-xxx`
  - `ALIGN-UNK-xxx`;
- every finding carries at least:
  - `finding_id`
  - `mismatch_class`
  - `basis_kind`
  - `severity`
  - `summary`
  - `intended_refs`
  - `observed_refs`
  - `request_support_refs`
  - `settlement_support_refs`;
- each `finding_id` suffix is derived from a canonical hash over:
  - `mismatch_class`
  - `basis_kind`
  - sorted `intended_refs`
  - sorted `observed_refs`
  - sorted `request_support_refs`
  - sorted `settlement_support_refs`;
- duplicate findings collapse on that canonical support tuple, findings are emitted
  in ascending `finding_id` order, and `severity_counts` is derived from the
  deduplicated canonical set;
- the report classifies severity exactly as:
  - `advisory`
  - `warning`
  - `blocking`
  and overall posture exactly as:
  - `aligned`
  - `drifted`
  - `blocked`;
- `alignment_posture = aligned` is impossible when findings exist or
  `blocking_finding_ids` is non-empty;
- `alignment_posture = blocked` is required when any finding has
  `severity = blocking`;
- report-level `alignment_posture = blocked` is only an alignment diagnostic posture
  over an already entitled comparison world and is not the same thing as upstream
  settlement `compile_entitlement = blocked`;
- the slice consumes released `compile_entitlement = entitled` as-is from `V41-B`
  and does not recompute settlement posture locally;
- no finding may be supported solely by prose notes, free text, or advisory-only
  upstream fields;
- unresolved unknowns that matter to comparison remain explicit as
  `unresolved_unknown` findings instead of being normalized away;
- the accepted fixture ladder under `apps/api/fixtures/architecture/vnext_plus87/`
  proves deterministic alignment replay, stable finding-id emission, explicit
  non-empty drift, honest `aligned` / `drifted` / `blocked` posture, and at least
  one upstream ambiguity or unresolved observation that survives into an explicit
  `unresolved_unknown` finding;
- Python tests cover deterministic replay, lineage-drift rejection, severity/blocking
  honesty, schema export parity, and rejection of remediation/runner/merged-truth
  creep.

## Do Not Accept If

- the slice redefines released `V41-A`, `V41-B`, `V41-C`, or `V41-D` upstream
  schemas or bytes;
- the alignment entrypoint reads ambient repo state outside the released request
  world;
- the alignment lane silently merges intended and observed into one blended artifact;
- settlement entitlement is recomputed locally instead of consumed from the released
  `V41-B` frame;
- observation becomes the hidden source of intended truth rather than a constraining
  companion artifact;
- a report claims `aligned` while findings remain;
- a blocking finding is omitted from `blocking_finding_ids`;
- finding ids or `severity_counts` depend on traversal order rather than the
  canonical deduplicated finding set;
- findings are materially supported only by notes or other prose-only upstream
  surfaces;
- unresolved unknowns disappear into notes or are silently omitted;
- the slice widens into runner behavior, remediation, repo mutation, checkpoint,
  projection, or UX practical outputs.

## Local Gate

- run `make check`
