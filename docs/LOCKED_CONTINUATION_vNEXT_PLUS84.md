# Locked Continuation vNext+84

Status: `V41-B` implementation contract.

## V84 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v41b_practical_analysis_settlement_contract@1",
  "target_arc": "vNext+84",
  "target_path": "V41-B",
  "target_scope": "practical_analysis_settlement_deontic_typing_and_entitlement_baseline",
  "analysis_request_schema": "adeu_architecture_analysis_request@1",
  "settlement_frame_schema": "adeu_architecture_analysis_settlement_frame@1",
  "implementation_package": "adeu_architecture_ir",
  "upstream_request_package": "adeu_architecture_ir",
  "settlement_entry_grounding_required": true,
  "settlement_blocking_lineage_required": true,
  "settlement_notes_authoritative": false,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "decomposition_doc": "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v23.md"
}
```

## Slice

- Arc label: `vNext+84`
- Family label: `V41-B`
- Scope label: practical analysis settlement, deontic typing, and entitlement
  baseline

## Objective

Introduce the first concrete practical settlement slice by activating the settlement
artifact only and freezing the interpretive and entitlement frame that later observed
extraction, intended compile, alignment, and runner lanes must consume without
silently redefining it.

This slice establishes the first repo-native practical-analysis substrate for:

- canonical `adeu_architecture_analysis_settlement_frame@1`;
- exact consumption of the released `V41-A` request / `source_set` boundary;
- explicit interpretation register plus chosen interpretation;
- deontic typing over request-bound brief / document / affordance surfaces;
- explicit `affordance_decisions`;
- explicit claim-posture classification;
- explicit escalation-trigger policy;
- pre-compile `compile_entitlement` classified as exactly:
  - `entitled`
  - `blocked`

This slice remains deliberately prior to:

- `adeu_architecture_observation_frame@1`;
- repo-grounded intended `adeu_architecture_semantic_ir@1` compile;
- `adeu_architecture_alignment_report@1`;
- CLI runner release;
- API or web inspection surfaces;
- remediation or repo-mutation planning.

Its job is to make the chosen interpretation and entitlement posture explicit before
any later slice tries to compile claims about that world.

## Frozen Implementation Decisions

1. Active package strategy:
   - continue in `packages/adeu_architecture_ir` for `vNext+84`;
   - `packages/adeu_architecture_compiler` remains a downstream consumer and may not
     become active for observation, intended compile, alignment, or runner behavior in
     this arc.
2. Upstream consumption strategy:
   - `vNext+84` must consume the released `V41-A` analysis request and committed v83
     request/reference fixture or exact validated derivatives thereof;
   - it may not bypass the released request boundary with free-floating maintainer
     prose, ad hoc file reads, or an unbound repo snapshot;
   - the settlement frame must bind back to the same:
     - `analysis_request_id`
     - `analysis_request_ref`
     - `source_set_hash`
     - `authority_boundary_policy`
     carried by the released request boundary.
3. Settlement artifact strategy:
   - `adeu_architecture_analysis_settlement_frame@1` is the only newly released
     artifact family in this slice;
   - authoritative JSON schema must live under
     `packages/adeu_architecture_ir/schema/`;
   - mirrored export must live under `spec/`;
   - mirrored export must match the authoritative schema byte-for-byte after
     canonical export.
4. Interpretation strategy:
   - the settlement frame must carry an explicit `interpretation_register`;
   - `chosen_interpretation_id` is required and must resolve to exactly one register
     entry in the same frame;
   - every `interpretation_register` entry must remain explicitly addressable and
     grounded at least by:
     - `interpretation_id`
     - canonical summary
     - `support_refs`
     - `linked_ambiguity_refs`;
   - no chosen interpretation may be implied only by prose or by omitted siblings.
5. Deontic typing and affordance strategy:
   - `deontic_typing_register` uses the frozen starter vocabulary:
     - `required`
     - `forbidden`
     - `permitted`
     - `optional_hint`
     - `fallback_affordance`
   - `affordance_decisions` uses the frozen starter vocabulary:
     - `used`
     - `deferred`
     - `intentionally_declined`
   - every `deontic_typing_register` entry must remain explicitly addressable and
     grounded at least by:
     - `typing_id`
     - `target_ref`
     - `target_kind`
     - `deontic_class`
     - rationale;
   - every `affordance_decisions` entry must remain explicitly addressable and
     grounded at least by:
     - `decision_id`
     - `target_ref`
     - `decision_class`
     - rationale;
   - any `deferred` or `intentionally_declined` affordance decision must record an
     explicit rationale;
   - any request-bound surface typed as:
     - `permitted`
     - `optional_hint`
     - `fallback_affordance`
     must also have an explicit affordance-decision record in the same frame;
   - `vNext+84` may not silently promote:
     - `permitted`
     - `optional_hint`
     - `fallback_affordance`
     into `required`.
6. Claim posture and entitlement strategy:
   - `claim_posture_register` uses the frozen starter vocabulary:
     - `observed`
     - `inferred`
     - `conjectural`
     - `unentitled_negative_claim`
   - every `claim_posture_register` entry must remain explicitly addressable and
     grounded at least by:
     - `claim_id`
     - `claim_ref`
     - `posture_class`
     - rationale;
   - the starter negative-claim posture may not collapse bounded search absence into
     proved impossibility;
   - any `unentitled_negative_claim` entry must also bind a bounded-support marker
     from the frozen starter set:
     - `search_absence`
     - `proof_not_attempted`
     - `ambiguity_dependent`
     - `assumption_pressure`;
   - `compile_entitlement` must classify as exactly:
     - `entitled`
     - `blocked`
   - `compile_entitlement` in this slice means settlement-entitled to proceed to
     downstream compile; it does not guarantee downstream compile will succeed;
   - `compile_entitlement = entitled` is legal only when:
     - `unresolved_high_impact_ambiguity_refs` is empty;
     - `active_escalation_records` is empty; and
     - no `claim_posture_register` entry remains
       `unentitled_negative_claim`;
   - `compile_entitlement = blocked` must preserve explicit `blocking_lineage`.
7. Escalation trigger strategy:
   - `escalation_trigger_policy` must freeze at least:
     - `unresolved_high_impact_ambiguity`
     - `silent_semantic_assumption_needed`
     - `impossibility_claim_without_proof`
     - `externalized_search_or_check_required`
   - `active_escalation_records` must remain explicitly addressable and grounded at
     least by:
     - `trigger_id`
     - `supporting_refs`
   - every active escalation record must resolve to one policy-defined trigger id in
     the same frame.
8. Ref-closure and prose-boundary strategy:
   - every interpretation support ref, deontic target, affordance-decision target,
     claim ref, linked ambiguity ref, escalation support ref, and blocking-lineage ref
     must resolve either:
     - to the released `V41-A` request; or
     - to an explicit artifact named by that request boundary;
   - `advisory_notes` is non-authoritative in this slice;
   - `advisory_notes` may not introduce new:
     - interpretations
     - deontic classes
     - claim postures
     - escalation triggers
     - source refs
     - blocking reasons
     not already present in typed fields.
9. Path decomposition strategy:
   - `vNext+84` is the first concrete `V41-B` arc;
   - observation, intended compile, alignment, and runner release remain available for
     later concrete `V41` arcs only.

## Required Deliverables

1. New typed practical-analysis settlement surface:
   - extend `packages/adeu_architecture_ir` with deterministic helpers that
     materialize canonical `adeu_architecture_analysis_settlement_frame@1`;
   - export schema helpers needed for authoritative and mirrored JSON-schema output;
   - keep observation, intended compile, alignment, and runner helpers out of scope.
2. Canonical practical-analysis settlement artifact:
   - `adeu_architecture_analysis_settlement_frame@1`
3. Deterministic settlement entrypoints that:
   - consume one released `adeu_architecture_analysis_request@1` plus interpretation,
     deontic typing, affordance, claim-posture, and escalation inputs over that
     request boundary;
   - materialize `adeu_architecture_analysis_settlement_frame@1`;
   - fail closed when request lineage, chosen interpretation, deontic typing,
     entitlement, or escalation posture is invalid.
4. Top-level schema anchors for `adeu_architecture_analysis_settlement_frame@1`:
   - `schema`
   - `settlement_frame_id`
   - `analysis_request_id`
   - `analysis_request_ref`
   - `source_set_hash`
   - `authority_boundary_policy`
   - `interpretation_register`
   - `chosen_interpretation_id`
   - `unresolved_high_impact_ambiguity_refs`
   - `deontic_typing_register`
   - `claim_posture_register`
   - `affordance_decisions`
   - `escalation_trigger_policy`
   - `active_escalation_records`
   - `compile_entitlement`
   - `blocking_lineage`
   - `advisory_notes`
5. Minimum register-entry anchors in this slice:
   - every `interpretation_register` entry must bind at least:
     - `interpretation_id`
     - `summary`
     - `support_refs`
     - `linked_ambiguity_refs`
   - every `deontic_typing_register` entry must bind at least:
     - `typing_id`
     - `target_ref`
     - `target_kind`
     - `deontic_class`
     - `rationale`
   - every `affordance_decisions` entry must bind at least:
     - `decision_id`
     - `target_ref`
     - `decision_class`
     - `rationale`
   - every `claim_posture_register` entry must bind at least:
     - `claim_id`
     - `claim_ref`
     - `posture_class`
     - `rationale`
     - `support_limit_class` when `posture_class = unentitled_negative_claim`
   - every `active_escalation_records` entry must bind at least:
     - `trigger_id`
     - `supporting_refs`
   - every `blocking_lineage` entry must bind at least:
     - `blocking_ref_id`
     - `blocking_kind`
     - `supporting_refs`
6. Deterministic settlement laws that fail closed on at least:
   - any `analysis_request_ref` that does not resolve to a released `V41-A` request or
     whose `analysis_request_id` / `source_set_hash` drifts from the released request
     boundary;
   - any frame missing `chosen_interpretation_id` or naming a chosen interpretation
     not present in `interpretation_register`;
   - any deontic typing outside the frozen starter set in this slice;
   - any affordance decision outside the frozen starter set in this slice;
   - any `deferred` or `intentionally_declined` affordance decision missing an
     explicit rationale;
   - any `unentitled_negative_claim` missing either explicit rationale or bounded
     support marker;
   - any request-bound affordance surfaced by deontic typing as:
     - `permitted`
     - `optional_hint`
     - `fallback_affordance`
     without a corresponding affordance-decision record;
   - any active escalation record whose `trigger_id` is not declared by
     `escalation_trigger_policy`;
   - any interpretation support ref, deontic target, affordance-decision target,
     claim ref, ambiguity ref, escalation support ref, or blocking-lineage ref that
     resolves neither to the released `V41-A` request nor to an explicit artifact
     named by that request;
   - any `compile_entitlement = entitled` frame with:
     - non-empty `unresolved_high_impact_ambiguity_refs`;
     - non-empty `active_escalation_records`; or
     - any `claim_posture_register` entry classified as
       `unentitled_negative_claim`;
   - any `compile_entitlement = blocked` frame missing explicit `blocking_lineage`;
   - any settlement frame that silently promotes:
     - `permitted`
     - `optional_hint`
     - `fallback_affordance`
     into `required`;
   - any `advisory_notes` payload that introduces load-bearing interpretations,
     deontic classes, claim postures, escalation triggers, source refs, or blocking
     reasons not already present in typed fields;
   - any settlement frame that smuggles in:
     - observed implementation facts,
     - intended semantic IR payload,
     - alignment diagnostics,
     - remediation instructions, or
     - repo-mutation plans
     as if those were already in scope for this lane.
7. Committed reference fixtures:
   - one accepted settlement fixture ladder under
     `apps/api/fixtures/architecture/vnext_plus84/` covering:
     - released analysis request input;
     - canonical settlement frame output
   - the accepted fixture ladder must prove:
     - request / `source_set` identity carry-through;
     - deterministic interpretation and deontic typing replay;
     - explicit affordance-decision recording;
     - explicit escalation-trigger posture;
      - honest `compile_entitlement` classification.
8. Python tests covering:
   - schema/model validation for
     `adeu_architecture_analysis_settlement_frame@1`;
   - authoritative/mirrored schema export parity;
   - deterministic settlement replay from the accepted fixture ladder;
   - rejection of request/source-set lineage drift;
   - rejection of missing chosen interpretation;
   - rejection of unsupported deontic typing, affordance-decision, or claim-posture
     classes;
   - rejection of missing rationale for deferred / declined affordances;
   - rejection of `compile_entitlement = entitled` when unresolved high-impact
     ambiguity, active escalation records, or unentitled negative claims remain;
   - rejection of missing `blocking_lineage` on blocked settlement;
   - rejection of prose-only semantic additions through `advisory_notes`;
   - rejection of observation, alignment, remediation, or repo-mutation fields inside
     the settlement lane.

## Hard Constraints

- `vNext+84` may not activate observation, intended compile, alignment, or runner
  entrypoints in `packages/adeu_architecture_compiler`.
- `vNext+84` may not ship:
  - `adeu_architecture_observation_frame@1`,
  - repo-grounded intended `adeu_architecture_semantic_ir@1` compile,
  - `adeu_architecture_alignment_report@1`,
  - CLI orchestration of the full loop,
  - API or web inspection routes,
  - automatic repo mutation,
  - direct prompt-to-code generation.
- `vNext+84` may not reinterpret released `V41-A` request capture as already-earned
  settlement, drift, or impossibility authority.
- `vNext+84` may not treat bounded search absence as proved impossibility without a
  later explicit proof surface.
- `vNext+84` may not silently promote permissions or fallback affordances into
  obligations.
- `vNext+84` may not let `advisory_notes` become a hidden semantic backchannel.
- `vNext+84` may not weaken the released `V40` root/sibling artifact boundaries or the
  released `V41-A` request / `source_set` boundary.

## PR Shape

- Single integrated PR.

Rationale:

- the settlement schema, released-request consumption rules, interpretation/deontic
  typing model, entitlement gating, reference fixtures, and guard tests are tightly
  coupled and should land together so the first practical settlement boundary freezes
  as one coherent baseline.
