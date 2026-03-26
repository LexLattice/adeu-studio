# Locked Continuation vNext+87

Status: `V41-E` implementation contract.

## V87 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v41e_practical_analysis_alignment_contract@1",
  "target_arc": "vNext+87",
  "target_path": "V41-E",
  "target_scope": "practical_analysis_alignment_and_drift_diagnostics_baseline",
  "analysis_request_schema": "adeu_architecture_analysis_request@1",
  "analysis_settlement_schema": "adeu_architecture_analysis_settlement_frame@1",
  "observation_frame_schema": "adeu_architecture_observation_frame@1",
  "semantic_ir_schema": "adeu_architecture_semantic_ir@1",
  "alignment_report_schema": "adeu_architecture_alignment_report@1",
  "implementation_package": "adeu_architecture_compiler",
  "authoritative_request_package": "adeu_architecture_ir",
  "authoritative_intended_package": "adeu_architecture_ir",
  "authoritative_intended_comparison_surface": "adeu_architecture_semantic_ir@1",
  "alignment_requires_distinct_intended_and_observed_artifacts": true,
  "settlement_context_required": true,
  "remediation_deferred": true,
  "runner_deferred": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "decomposition_doc": "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v23.md"
}
```

## Slice

- Arc label: `vNext+87`
- Family label: `V41-E`
- Scope label: practical analysis alignment and drift diagnostics baseline

## Objective

Introduce the first concrete practical alignment slice by activating only the
deterministic comparison lane and freezing one canonical
`adeu_architecture_alignment_report@1` artifact over the released `V41-A` request
boundary, `V41-B` settlement frame, `V41-C` observation frame, and `V41-D` intended
semantic-root outputs before any habitual runner, remediation, or repo-mutation
surface is released.

This slice establishes the first repo-native practical-analysis substrate for:

- canonical `adeu_architecture_alignment_report@1`;
- exact consumption of the released `V41-A` analysis request boundary;
- exact consumption of the released `V41-B` settlement frame;
- exact consumption of the released `V41-C` observation frame;
- exact consumption of the released `V41-D` intended root-family outputs;
- deterministic starter mismatch classes and stable finding ids;
- explicit severity and blocking posture for alignment findings;
- explicit unresolved-unknown carry-through rather than silent normalization;
- authoritative and mirrored schema exports.

This slice remains deliberately prior to:

- CLI runner release;
- API or web inspection surfaces;
- remediation or repo-mutation planning;
- automatic reconciliation of intended and observed lanes;
- repo-grounded checkpoint/oracle reuse, projection, or UX practical outputs.

Its job is to make intended-vs-observed drift inspectable and deterministic before a
later slice habitualizes the full practical runner over real repo scopes.

## Frozen Implementation Decisions

1. Active package strategy:
   - activate the practical alignment lane in `packages/adeu_architecture_compiler`
     for `vNext+87`;
   - `packages/adeu_architecture_ir` remains authoritative for the released `V41-A`,
     `V41-B`, and `V41-D` upstream artifacts and may not be silently redefined by
     compiler-local vocabulary.
2. Upstream consumption strategy:
   - `vNext+87` must consume one released `V41-A` analysis request, one released
     `V41-B` settlement frame, one released `V41-C` observation frame, and one
     released `V41-D` intended semantic root, or exact validated derivatives thereof;
   - it may not bypass the released repo world with ambient working-tree reads,
     unbound file selection, free-floating prose, or an intended/observed artifact
     outside the released request boundary;
   - the alignment report must bind back to the same:
     - `analysis_request_id`
     - `analysis_request_ref`
     - `settlement_frame_id`
     - `settlement_frame_ref`
     - `observation_frame_id`
     - `observation_frame_ref`
     - `architecture_id`
     - `semantic_hash`
     - `source_set_hash`
     - `authority_boundary_policy`
     carried by the released upstream artifacts.
   - the first concrete alignment baseline treats released
     `adeu_architecture_semantic_ir@1` as the authoritative intended comparison
     surface;
   - companion released intended root-family refs may appear only through an
     explicitly declared support contract and may not silently widen the first
     baseline into implicit whole-root-family comparison.
3. Alignment-report strategy:
   - `adeu_architecture_alignment_report@1` is the only newly released artifact
     family in this slice;
   - authoritative JSON schema must live under
     `packages/adeu_architecture_compiler/schema/`;
   - mirrored export must live under `spec/`;
   - mirrored export must match the authoritative schema byte-for-byte after
     canonical export;
   - the report may compare intended and observed artifacts, but it may not rewrite,
     reconcile, or merge them into one new truth surface.
4. Comparison strategy:
   - intended and observed remain distinct companion artifacts throughout this slice;
   - the request boundary plus settlement frame remain the governing context for the
     comparison and may not be recomputed locally;
   - the request boundary plus settlement frame remain the normative driver of
     intended truth in this slice;
   - the observation frame may constrain overreach, force ambiguity or advisory
     posture, or trigger fail-closed refusal, but it may not become the hidden source
     of intended architecture;
   - any intended-side claim materially supported by observation must also resolve to
     request-bound brief or accepted-doc lineage or else remain explicit as ambiguity,
     advisory posture, or refusal to settle rather than being emitted as settled
     intended truth;
   - the report may classify drift, missing coverage, and unresolved unknowns, but
     it may not auto-accept mismatches or silently suppress them;
   - unresolved or advisory posture already present upstream may constrain the report
     and may force `blocked`, but may not vanish by omission.
5. Starter mismatch-class strategy:
   - the report must release starter mismatch classes at least for:
     - `declared_not_observed`
     - `observed_not_declared`
     - `authority_boundary_drift`
     - `workflow_or_state_drift`
     - `evidence_or_observability_gap`
     - `unresolved_unknown`
   - stable finding-id families must start with:
     - `ALIGN-DNO-xxx`
     - `ALIGN-OND-xxx`
     - `ALIGN-ABD-xxx`
     - `ALIGN-WSD-xxx`
     - `ALIGN-EOG-xxx`
     - `ALIGN-UNK-xxx`
   - each finding-id suffix must be derived from a canonical hash of the tuple:
     - `mismatch_class`
     - `basis_kind`
     - sorted `intended_refs`
     - sorted `observed_refs`
     - sorted `request_support_refs`
     - sorted `settlement_support_refs`
   - duplicate findings with the same canonical support tuple must collapse into one
     canonical finding before report materialization;
   - findings must be emitted in ascending canonical `finding_id` order;
   - `severity_counts` must be derived from the deduplicated canonical finding set
     rather than traversal order;
   - the starter class set is intentionally bounded and not the whole future ontology
     of drift.
6. Severity posture strategy:
   - every finding must classify severity as exactly:
     - `advisory`
     - `warning`
     - `blocking`
   - the report must classify overall alignment posture as exactly:
     - `aligned`
     - `drifted`
     - `blocked`
   - `aligned` is legal only when no findings are emitted and
     `blocking_finding_ids` is empty;
   - `drifted` is legal only when findings are emitted but none have
     `severity = blocking`;
   - `blocked` must carry explicit `blocking_finding_ids` lineage and is required
     when any finding has `severity = blocking`.
   - report-level `alignment_posture = blocked` is a diagnostic posture over an
     already entitled comparison world and is not equivalent to upstream settlement
     `compile_entitlement = blocked`.
7. Upstream-settlement strategy:
   - `vNext+87` must consume the released settlement posture as-is and may not
     recompute compile entitlement locally;
   - the first concrete alignment arc must consume a released settlement frame with
     `compile_entitlement = entitled` and no blocking lineage, because it compares
     against the released `V41-D` intended outputs emitted over that same entitled
     world;
   - blocked settlement worlds remain out of scope for the first concrete `V41-E`
     arc.
8. Path decomposition strategy:
   - `vNext+87` is the first concrete `V41-E` arc;
   - habitual runner rollout, remediation planning, and practical-loop widening
     remain available only for later concrete `V41` arcs.

## Required Deliverables

1. New typed practical-analysis alignment surface:
   - extend `packages/adeu_architecture_compiler` with deterministic helpers that
     materialize canonical `adeu_architecture_alignment_report@1`;
   - export schema helpers needed for authoritative and mirrored JSON-schema output;
   - keep runner, remediation, checkpoint, projection, and UX practical outputs out
     of scope.
2. Canonical practical-analysis alignment artifact:
   - `adeu_architecture_alignment_report@1`
3. Deterministic alignment entrypoints that:
   - consume one released `adeu_architecture_analysis_request@1`, one released
     `adeu_architecture_analysis_settlement_frame@1`, one released
     `adeu_architecture_observation_frame@1`, and one released
     `adeu_architecture_semantic_ir@1`;
   - compare intended and observed lanes deterministically without mutating either;
   - materialize `adeu_architecture_alignment_report@1`;
   - fail closed when request lineage, settlement lineage, observation lineage,
     intended lineage, source-set identity, or released report validation is invalid.
4. Top-level schema anchors for `adeu_architecture_alignment_report@1`:
   - `schema`
   - `alignment_report_id`
   - `analysis_request_id`
   - `analysis_request_ref`
   - `settlement_frame_id`
   - `settlement_frame_ref`
   - `observation_frame_id`
   - `observation_frame_ref`
   - `architecture_id`
   - `semantic_hash`
   - `source_set_hash`
   - `authority_boundary_policy`
   - `alignment_posture`
   - `blocking_finding_ids`
   - `severity_counts`
   - `findings`
5. Minimum finding anchors in this slice:
   - every finding must bind at least:
     - `finding_id`
     - `mismatch_class`
     - `basis_kind`
     - `severity`
     - `summary`
     - `intended_refs`
     - `observed_refs`
     - `request_support_refs`
     - `settlement_support_refs`
   - `basis_kind` must classify the comparison basis at least for:
     - `contradictory_evidence`
     - `missing_observation`
     - `missing_intended_declaration`
     - `authority_mismatch`
     - `unresolved_upstream_unknown`
6. Deterministic alignment laws that fail closed on at least:
   - any request / settlement / observation / intended lineage drift against the
     released repo world;
   - any `source_set_hash` or `authority_boundary_policy` mismatch across the
     consumed upstream artifacts;
   - any finding ref that does not resolve to a consumed intended or observed item or
     to a released request / settlement support ref;
   - any report that claims `alignment_posture = aligned` while findings or
     `blocking_finding_ids` remain;
   - any report that omits a `severity = blocking` finding from
     `blocking_finding_ids`;
   - any finding whose support resolves only to prose notes, free text, or
     non-authoritative advisory fields rather than typed upstream refs;
   - any attempt to suppress a material `unresolved_unknown` into notes or by
     omission;
   - any attempt to embed remediation plans, repo-mutation instructions, runner
     state, checkpoint state, projection state, or UX state into the alignment
     report;
   - any attempt to emit a merged intended/observed artifact payload in place of an
     alignment report.
7. Committed reference fixtures:
   - one accepted alignment fixture ladder under
     `apps/api/fixtures/architecture/vnext_plus87/` covering:
     - released request input
     - released settlement input
     - released observation input
     - released intended input
     - canonical alignment-report output
   - the accepted fixture ladder must prove:
     - deterministic alignment replay,
     - stable starter finding-id emission,
     - explicit non-empty drift classification,
     - explicit unresolved-unknown or evidence-gap carry-through,
     - at least one case where upstream ambiguity or unresolved observation survives
       into an explicit `unresolved_unknown` finding rather than being downgraded
       into a weaker mismatch class,
     - honest `aligned` / `drifted` / `blocked` posture classification.
8. Python tests covering:
   - schema/model validation for `adeu_architecture_alignment_report@1`;
   - authoritative/mirrored schema export parity;
   - deterministic alignment replay from the accepted fixture ladder;
   - request / settlement / observation / intended lineage drift rejection;
   - severity and blocking-posture honesty;
   - rejection of remediation, runner, or merged-truth creep inside the alignment
     lane.

## Hard Constraints

- `vNext+87` may not reopen or redefine the released `V41-A`, `V41-B`, `V41-C`, or
  `V41-D` upstream contracts.
- `vNext+87` may not emit:
  - CLI runner outputs,
  - API or web inspection routes,
  - remediation or repo-mutation plans,
  - repo-grounded checkpoint traces,
  - repo-grounded oracle request/resolution artifacts,
  - repo-grounded projection bundle / manifest artifacts,
  - repo-grounded UX artifacts.
- `vNext+87` may not collapse intended and observed lanes into one blended artifact.
- `vNext+87` may not silently auto-reconcile or auto-accept drift.
- `vNext+87` may not emit shadow advisory intended artifacts under released
  root-family names when settlement or alignment posture is blocking.
- The formal Lean sidecar may mirror frozen finite law only:
  - it is not required for slice validity,
  - it may not silently redefine the released practical alignment contract.

## PR Shape

- Single integrated PR.

Rationale:

- the alignment entrypoints, schema family, stable finding-id/report grammar,
  committed comparison fixture ladder, and fail-closed tests are tightly coupled and
  should land together so the first practical alignment lane freezes as one coherent
  baseline.
