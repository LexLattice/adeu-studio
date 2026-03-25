# Draft Stop-Gate Decision vNext+85

Status: proposed gate for `V41-C`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS85.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- `adeu_architecture_observation_frame@1` validates and exports cleanly from
  `packages/adeu_architecture_compiler` with byte-identical authoritative and mirrored
  schemas;
- the observation frame consumes the released `V41-A` request boundary exactly
  through:
  - `analysis_request_id`
  - `analysis_request_ref`
  - `source_set_hash`
  - `authority_boundary_policy`;
- the observation frame consumes the released `V41-B` settlement frame exactly
  through:
  - `settlement_frame_id`,
  - `settlement_frame_ref`,
  - `upstream_compile_entitlement`,
  - `upstream_blocking_refs`;
- every observed entry remains explicitly provenance-linked to concrete `source_set`
  items admitted by the released request boundary;
- every `observed_units` entry carries at least:
  - `unit_id`
  - `unit_kind`
  - `fact_kind`
  - `observation_mode`
  - `source_refs`
  - `summary`;
- every `observed_boundaries` entry carries at least:
  - `boundary_id`
  - `boundary_kind`
  - `fact_kind`
  - `observation_mode`
  - `source_refs`
  - `crossing_refs`;
- every `observed_workflows` entry carries at least:
  - `workflow_id`
  - `fact_kind`
  - `observation_mode`
  - `source_refs`
  - `step_refs`;
- every `observed_authority_sources` entry carries at least:
  - `authority_source_id`
  - `mechanism_kind`
  - `fact_kind`
  - `observation_mode`
  - `source_refs`;
- every `observed_evidence_hooks` entry carries at least:
  - `evidence_hook_id`
  - `hook_kind`
  - `fact_kind`
  - `observation_mode`
  - `source_refs`;
- every `observed_observability_hooks` entry carries at least:
  - `observability_hook_id`
  - `hook_kind`
  - `fact_kind`
  - `observation_mode`
  - `source_refs`;
- every `unresolved_observations` entry carries at least:
  - `observation_id`
  - `observation_kind`
  - `observation_mode`
  - `source_refs`
  - `unresolved_reason_kind`
  - `rationale`;
- every observed entry declares whether it is `direct` file-grounded observation or
  bounded `derived` structural extraction;
- observation remains facts-only:
  - no intended semantics,
  - no settlement deontic typing,
  - no alignment severity,
  - no remediation plans;
- observation may consume a released settlement frame with
  `compile_entitlement = blocked`, but may not upgrade, reinterpret, or erase that
  settlement posture;
- every provenance ref resolves to:
  - one released `source_set` item; or
  - one released upstream request/settlement artifact ref;
- every `step_ref` and `crossing_ref` resolves to another typed observation entry in
  the same frame and does not float above ungrounded cross-entry structure;
- unresolved observations remain explicit rather than silently invented or defaulted;
- unresolved observations carry bounded reason typing rather than prose-only
  rationales;
- if the released repo world is valid but bounded extraction cannot determine a fact,
  the frame preserves that state as unresolved observation rather than failing open or
  inventing structure;
- deterministic fixture replay rejects ordering drift and provenance drift for the
  observed frame;
- one committed fixture ladder proves deterministic observation replay over the
  released v83/v84 boundary;
- Python tests cover:
  - schema/model validation,
  - schema export parity,
  - deterministic observation replay,
  - provenance closure,
  - duplicate-id rejection,
  - unresolved-observation requirements,
  - rejection of intended/alignment/remediation creep.

## Do Not Accept If

- observation reads ambient repo state outside the released request boundary;
- the frame claims to observe a different `source_set_hash` or authority policy than
  the released request boundary;
- the frame consumes a settlement artifact outside the released request world;
- source provenance is missing, empty, or outside the released request boundary;
- implementation facts are silently invented instead of emitted as unresolved
  observations;
- intended architecture semantics, deontic classes, alignment verdicts, or remediation
  plans land inside the observed lane;
- blocked settlement posture is erased or upgraded by observation output;
- upstream compile-entitlement and blocking lineage are omitted or drift from the
  released settlement frame;
- direct-vs-derived observation mode is omitted from resolved observed entries;
- cross-entry workflow or boundary refs float without typed in-frame targets and
  concrete source anchoring;
- observed extraction depends on free-floating prose rather than released request /
  settlement / source-set artifacts;
- a notes-like field introduces intended semantics, alignment claims, remediation
  hints, or hidden provenance outside typed fields;
- the slice widens into intended compile, alignment, runner release, or inspection
  surfaces.

## Local Gate

- run `make check`
