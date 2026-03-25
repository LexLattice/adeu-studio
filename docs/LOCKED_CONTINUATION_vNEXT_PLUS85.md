# Locked Continuation vNext+85

Status: `V41-C` implementation contract.

## V85 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v41c_practical_analysis_observation_contract@1",
  "target_arc": "vNext+85",
  "target_path": "V41-C",
  "target_scope": "practical_analysis_observed_implementation_frame_baseline",
  "analysis_request_schema": "adeu_architecture_analysis_request@1",
  "analysis_settlement_schema": "adeu_architecture_analysis_settlement_frame@1",
  "observation_frame_schema": "adeu_architecture_observation_frame@1",
  "implementation_package": "adeu_architecture_compiler",
  "upstream_request_package": "adeu_architecture_ir",
  "upstream_settlement_package": "adeu_architecture_ir",
  "observed_lane_facts_only": true,
  "observed_lane_provenance_required": true,
  "intended_observed_lane_separation_required": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "decomposition_doc": "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v23.md"
}
```

## Slice

- Arc label: `vNext+85`
- Family label: `V41-C`
- Scope label: practical analysis observed-implementation frame baseline

## Objective

Introduce the first concrete observed-implementation slice by activating the observed
fact lane only and freezing the typed artifact that deterministic repo observation
will emit over the released request and settlement boundary before any intended
compile, alignment, or runner widening is released.

This slice establishes the first repo-native practical-analysis substrate for:

- canonical `adeu_architecture_observation_frame@1`;
- exact consumption of the released `V41-A` analysis request boundary;
- exact consumption of the released `V41-B` settlement frame;
- explicit carry-through of upstream compile-entitlement and blocking-lineage posture;
- deterministic extraction of bounded implementation facts from the released
  `source_set`;
- explicit provenance refs back to concrete source-set files;
- explicit distinction between directly observed facts and bounded derived structural
  extraction;
- explicit unresolved observation markers instead of silent invention;
- authoritative and mirrored schema exports.

This slice remains deliberately prior to:

- repo-grounded intended `adeu_architecture_semantic_ir@1` compile;
- `adeu_architecture_alignment_report@1`;
- CLI runner release;
- API or web inspection surfaces;
- remediation or repo-mutation planning.

Its job is to make observed implementation facts inspectable and provenance-linked
before later slices compare them to intended architecture or orchestrate the full
practical loop.

## Frozen Implementation Decisions

1. Active package strategy:
   - activate the practical observation lane in `packages/adeu_architecture_compiler`
     for `vNext+85`;
   - `packages/adeu_architecture_ir` remains authoritative for the released `V41-A`
     request and `V41-B` settlement artifacts and may not be silently redefined by
     compiler-local vocabulary.
2. Upstream consumption strategy:
   - `vNext+85` must consume the released `V41-A` analysis request and released
     `V41-B` settlement frame or exact validated derivatives thereof;
   - it may not bypass the released repo world with ambient working-tree reads,
     unbound file selection, free-floating prose, or a settlement frame outside the
     released request boundary;
   - the observation frame must bind back to the same:
     - `analysis_request_id`
     - `analysis_request_ref`
     - `settlement_frame_id`
     - `settlement_frame_ref`
     - `source_set_hash`
     - `authority_boundary_policy`
     carried by the released upstream artifacts.
3. Observation artifact strategy:
   - `adeu_architecture_observation_frame@1` is the only newly released artifact
     family in this slice;
   - authoritative JSON schema must live under
     `packages/adeu_architecture_compiler/schema/`;
   - mirrored export must live under `spec/`;
   - mirrored export must match the authoritative schema byte-for-byte after
     canonical export.
4. Facts-only observation strategy:
   - the observed lane is limited to extracted implementation facts and unresolved
     observations only;
   - extracted facts may be either:
     - directly observed from released `source_set` items; or
     - bounded structural derivations over those same items;
   - every observed entry must declare whether it is `direct` or `derived`;
   - it may not mint intended architecture truth, settlement semantics, alignment
     verdicts, remediation plans, or repo-mutation instructions;
   - observation may consume either `compile_entitlement = entitled` or
     `compile_entitlement = blocked` from the released settlement frame, but may not
     upgrade, reinterpret, or erase that settlement posture in this slice;
   - the frame must carry the released settlement posture forward explicitly through:
     - `upstream_compile_entitlement`
     - `upstream_blocking_refs`
     rather than forcing later slices to reopen settlement state implicitly.
5. Provenance strategy:
   - every observed entry must remain explicitly provenance-linked to concrete
     `source_set` items admitted by the released request boundary;
   - every provenance ref in the observation frame must resolve to:
     - one source-set item in the released request boundary; or
     - one upstream released request/settlement artifact ref;
   - any `step_ref` or `crossing_ref` emitted by the frame must resolve to another
     typed observation entry inside the same frame;
   - no cross-entry reference graph may float without at least one concrete
     `source_ref` anchor on the referenced observation entry;
   - no observation entry may be supported only by ambient reasoning text or by a
     prose note outside typed fields.
6. Observation-surface strategy:
   - the frame must carry explicit observed surfaces at least for:
     - implementation units
     - boundaries
     - workflows
     - authority sources
     - evidence hooks
     - observability hooks
     - unresolved observations
   - the lane must preserve unknown / unresolved observations explicitly rather than
     silently inventing missing facts;
   - unresolved observations in this slice must also carry a bounded
     `unresolved_reason_kind` so later lanes can distinguish honest unknowns from
     contract failures.
7. Canonicalization strategy:
   - the observed frame must use deterministic canonical JSON serialization
     compatible with the repo's existing fail-closed artifact discipline;
   - fixture replay must reject provenance drift and ordering drift for the observed
     frame.
8. Path decomposition strategy:
   - `vNext+85` is the first concrete `V41-C` arc;
   - intended compile, alignment, and runner release remain available for later
     concrete `V41` arcs only.

## Required Deliverables

1. New typed practical-analysis observation surface:
   - extend `packages/adeu_architecture_compiler` with deterministic helpers that
     materialize canonical `adeu_architecture_observation_frame@1`;
   - export schema helpers needed for authoritative and mirrored JSON-schema output;
   - keep intended compile, alignment, and runner helpers out of scope.
2. Canonical practical-analysis observation artifact:
   - `adeu_architecture_observation_frame@1`
3. Deterministic observation entrypoints that:
   - consume one released `adeu_architecture_analysis_request@1` plus one released
     `adeu_architecture_analysis_settlement_frame@1`;
   - extract bounded implementation facts only from released `source_set` items or
     exact validated derivatives thereof;
   - materialize `adeu_architecture_observation_frame@1`;
   - fail closed when request lineage, settlement lineage, provenance closure,
     cross-entry reference closure, or observed-entry shape is invalid;
   - preserve unresolved observations explicitly when the released repo world is
     valid but bounded extraction cannot determine a fact.
4. Top-level schema anchors for `adeu_architecture_observation_frame@1`:
   - `schema`
   - `observation_frame_id`
   - `analysis_request_id`
   - `analysis_request_ref`
   - `settlement_frame_id`
   - `settlement_frame_ref`
   - `source_set_hash`
   - `authority_boundary_policy`
   - `upstream_compile_entitlement`
   - `upstream_blocking_refs`
   - `observed_units`
   - `observed_boundaries`
   - `observed_workflows`
   - `observed_authority_sources`
   - `observed_evidence_hooks`
   - `observed_observability_hooks`
   - `unresolved_observations`
5. Minimum observed-entry anchors in this slice:
   - every `observed_units` entry must bind at least:
     - `unit_id`
     - `unit_kind`
     - `fact_kind`
     - `observation_mode`
     - `source_refs`
     - `summary`
   - every `observed_boundaries` entry must bind at least:
     - `boundary_id`
     - `boundary_kind`
     - `fact_kind`
     - `observation_mode`
     - `source_refs`
     - `crossing_refs`
   - every `observed_workflows` entry must bind at least:
     - `workflow_id`
     - `fact_kind`
     - `observation_mode`
      - `source_refs`
      - `step_refs`
   - every `observed_authority_sources` entry must bind at least:
      - `authority_source_id`
      - `mechanism_kind`
      - `fact_kind`
      - `observation_mode`
      - `source_refs`
   - every `observed_evidence_hooks` entry must bind at least:
      - `evidence_hook_id`
      - `hook_kind`
      - `fact_kind`
      - `observation_mode`
      - `source_refs`
   - every `observed_observability_hooks` entry must bind at least:
      - `observability_hook_id`
      - `hook_kind`
      - `fact_kind`
      - `observation_mode`
      - `source_refs`
   - every `unresolved_observations` entry must bind at least:
      - `observation_id`
      - `observation_kind`
      - `observation_mode`
      - `source_refs`
      - `unresolved_reason_kind`
      - `rationale`
6. Deterministic observation laws that fail closed on at least:
   - any provenance ref outside the released request boundary;
   - any missing or empty `source_refs` in an observed entry;
   - any missing `fact_kind` or `observation_mode` in an observed entry that claims
     resolved implementation fact status;
   - any duplicate root-local ids where the observation contract requires uniqueness;
   - any `step_ref` or `crossing_ref` that does not resolve to another typed
     observation entry in the same frame;
   - any attempt to materialize intended semantics, alignment severity, or
     remediation fields inside the observation frame;
   - any unresolved observation that lacks explicit rationale,
     `unresolved_reason_kind`, or source support.
7. Committed reference fixtures:
   - one accepted observation fixture ladder under
     `apps/api/fixtures/architecture/vnext_plus85/` covering:
     - released request input
     - released settlement input
     - canonical observation-frame output
   - the accepted fixture ladder must prove:
     - deterministic observation replay,
     - exact provenance closure to released `source_set` items,
     - explicit unresolved observation preservation,
     - blocked settlement can be consumed without entitlement laundering.
8. Python tests covering:
   - schema/model validation for `adeu_architecture_observation_frame@1`;
   - authoritative/mirrored schema export parity;
   - deterministic observation replay from the accepted fixture ladder;
   - provenance closure and duplicate-id rejection;
   - rejection of intended, alignment, or remediation fields inside the observed
     lane;
   - explicit unresolved-observation requirements.

## Hard Constraints

- `vNext+85` may not reopen or redefine the released `V41-A` request or `V41-B`
  settlement contracts.
- `vNext+85` may not ship:
  - repo-grounded intended `adeu_architecture_semantic_ir@1` compile,
  - `adeu_architecture_alignment_report@1`,
  - CLI runner release,
  - API or web inspection surfaces,
  - remediation or repo-mutation planning,
  - direct prompt-to-code generation.
- The observed lane may not mint intended architecture truth.
- The observed lane may not carry settlement deontic classes, chosen-interpretation
  authority, alignment severity, or downstream compile readiness as if those were
  observation facts.
- `compile_entitlement = blocked` in the released settlement frame may not be erased
  or upgraded by this slice.
- No free-text or notes-like field in this slice may introduce intended semantics,
  alignment claims, remediation hints, or hidden provenance outside typed fields.
- The formal Lean sidecar remains irrelevant to slice validity:
  - it is not required for observation-frame release,
  - it may not silently redefine the practical-analysis contract.

## PR Shape

- Single integrated PR.

Rationale:

- request/settlement consumption, observation-frame schemas, provenance guards,
  committed fixture ladder, and tests are tightly coupled and should land together so
  the first observed-implementation surface freezes as one coherent baseline.
