# Locked Continuation vNext+73

Status: `V39-B` implementation contract.

## V73 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v39b_synthetic_pressure_mismatch_registry_contract@1",
  "target_arc": "vNext+73",
  "target_path": "V39-B",
  "target_scope": "synthetic_pressure_mismatch_taxonomy_and_registry_baseline",
  "registry_schema": "synthetic_pressure_mismatch_rule_registry@1",
  "implementation_package": "adeu_core_ir",
  "glossary_strategy": "registry_local_vocabulary"
}
```

## Slice

- Arc label: `vNext+73`
- Family label: `V39-B`
- Scope label: pressure-mismatch taxonomy and canonical registry baseline

## Objective

Introduce a bounded repo-native way to express pressure-mismatch drift as typed
registry law rather than style folklore.

This slice freezes the first canonical registry substrate for:

- `signal_kind`
- `harm_kind`
- `evidence_mode`
- `evidence_regime`
- `allowed_action`
- `resolution_route`
- bounded `expected_utility_gain`
- `counterexample_policy`

The slice remains deliberately prior to detectors, reports, fix plans, and hybrid
oracle execution. Its job is to establish the vocabulary and admissibility law that
later `V39-C`, `V39-D`, and `V39-E` slices will consume.

## Frozen Implementation Decisions

1. First implementation package:
   - place the initial schema, models, validators, exports, and registry helpers in
     `packages/adeu_core_ir`.
2. Glossary strategy for `V39-B`:
   - keep the pressure-mismatch vocabulary registry-local in this slice;
   - do not introduce a separate glossary artifact in `V39-B`;
   - do not overload the `V36-A` same-context reachability glossary.

## Required Deliverables

1. New typed ADEU core artifact:
   - canonical `synthetic_pressure_mismatch_rule_registry@1`
   - mirrored JSON schema export in both:
     - `packages/adeu_core_ir/schema/`
     - `spec/`
2. Registry law that makes the subject explicit, including:
   - canonical `signal_kind` vocabulary:
     - `state_model_drift`
     - `abstraction_pressure_drift`
     - `semantic_communication_drift`
     - `shape_regularity_drift`
     - `meta_intent_failure`
   - canonical `subject_kind` starter vocabulary:
     - `code_span`
     - `diff_hunk`
     - `function_or_method`
     - `test_case_or_fixture`
     - `comment_block`
     - `error_message`
     - `commit_message`
     - `review_note`
     - `recap_artifact`
   - canonical `evidence_regime` vocabulary:
     - `deterministic_local`
     - `static_contextual`
     - `semantic_ambiguous`
     - `meta_governance`
   - canonical `allowed_action` vocabulary:
     - `safe_autofix`
     - `deterministic_finding`
     - `review_only_finding`
     - `forbid`
     - `discourage`
     - `allow_with_justification`
     - `meta_artifact_correction`
   - canonical `resolution_route` vocabulary:
     - `deterministic_only`
     - `oracle_assisted`
     - `human_only`
   - bounded `expected_utility_gain` vocabulary:
     - `correctness_protection`
     - `failure_signal_recovery`
     - `trust_boundary_clarity`
     - `maintainability_improvement`
     - `semantic_density_gain`
     - `review_load_reduction`
     - `intent_clarity_gain`
3. Deterministic validators or builders that:
   - reject authorship or origin claims as registry dimensions;
   - reject free-prose `expected_utility_gain`;
   - require `counterexample_policy` rather than optional notes;
   - require explicit `resolution_route`;
   - keep `overall_pressure_mismatch_posture` out of the registry substrate;
   - fail closed on unknown vocabulary members or unsupported field combinations.
4. One committed reference registry fixture that:
   - validates as `synthetic_pressure_mismatch_rule_registry@1`;
   - contains seed rules spanning all five `signal_kind` families;
   - demonstrates deterministic-local, contextual, ambiguous, and meta-governance
     regimes without yet implementing detector logic.
5. Python tests covering:
   - schema/model validation;
   - schema export parity;
   - canonical fixture replay;
   - fail-closed rejection for invalid vocabulary or forbidden combinations;
   - preservation of the non-authorship boundary.

## Hard Constraints

- `V39-B` may not govern against "AI-ness" or authorship. The governed object remains
  pressure-mismatch drift only.
- `V39-B` may not ship detector rollout, observation packets, conformance reports,
  fix-plan artifacts, oracle request artifacts, or checkpoint adjudication logic.
- The registry must remain anti-score by construction:
  - no hidden scalar drift score;
  - no automatic merge-worthiness field;
  - no `overall_pressure_mismatch_posture` summary field in the registry artifact.
- `safe_autofix` may not be assigned to:
  - `semantic_ambiguous` rules,
  - `meta_governance` rules,
  - `shape_regularity_drift` rules in this first slice.
- `resolution_route` remains advisory routing metadata in this slice and may not
  imply that hybrid execution infrastructure already exists.
- The vocabulary remains registry-local in `V39-B`; no separate glossary artifact may
  be minted here, and the `V36-A` same-context glossary must remain untouched.
- Package placement for the first slice remains `adeu_core_ir`; do not split the
  family into a new package during `V39-B`.
- Seed rules may illustrate later lanes, but they may not claim that oracle-assisted
  or human-only routes are already executable repo surfaces.

## PR Shape

- Single integrated PR.

Rationale:

- the schema, mirrored exports, canonical fixture, validators, docs, and tests are
  tightly coupled and should land together to keep the registry law internally
  consistent.
