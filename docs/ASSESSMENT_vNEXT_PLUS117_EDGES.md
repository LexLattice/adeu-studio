# Assessment vNext+117 Edges

Status: planning-edge assessment for `V49-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS117_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Starter Semantic Unit Drift

- Risk:
  the first substrate slice could claim a semantic language while leaving the smallest
  starter ADEU statement / calculus unit implicit.
- Response:
  freeze one starter statement shape, one operator / relation posture, and one
  semantic-kind / lane-tag posture in `V49-A` itself.

### Edge 2: Identity-Law Softness

- Risk:
  canonical semantic identity could be described narratively while remaining
  operationally underdefined.
- Response:
  require one explicit canonical identity law, one canonical hash subject, and one
  explicit split between identity-participating fields and projection-only /
  support-only fields.

### Edge 3: Schema-Family Placeholder Drift

- Risk:
  the first semantic substrate slice could ship package scaffolding while leaving the
  actual schema family names unresolved until implementation taste takes over.
- Response:
  freeze the first schema family in the lock itself:
  `adeu_semantic_parse_profile@1`, `adeu_semantic_statement_core@1`,
  `adeu_semantic_normal_form@1`, `adeu_semantic_parse_result@1`, and
  `adeu_semantic_transform_contract@1`.

### Edge 4: Ambiguity / Unsupported Split Drift

- Risk:
  `parse_result` could be shipped while ambiguity and unsupported posture remain only
  half-frozen.
- Response:
  freeze both ambiguity posture and unsupported posture inside the first contract
  slice, with one contract-only outcome vocabulary.

### Edge 5: Equivalence Doctrine Drift

- Risk:
  later parser behavior could silently decide what counts as the same canonical object,
  a typed alternative, clarification need, or unsupported rejection.
- Response:
  freeze those distinctions inside `V49-A` as contract doctrine rather than leaving
  them to `V49-B` behavior.

### Edge 6: Recovery Laundering

- Risk:
  the first semantic substrate move could quietly smuggle in parser behavior or
  natural-language heuristics.
- Response:
  keep `V49-A` contract-first only and defer all `NL -> ADEU` behavior to `V49-B`.

### Edge 7: Lowering Laundering

- Risk:
  the first slice could overreach into `V48`-adjacent lowering before the substrate
  contract is stable.
- Response:
  defer all deterministic `ADEU -> ADEU` lowering to `V49-C` and all downstream bridge
  behavior to `V49-D`.

### Edge 8: Imported-Bundle Precedent Drift

- Risk:
  the normalized external prototype pack could be overread as the authority source for
  the shipped semantic substrate.
- Response:
  keep the intake bundle support-only / non-precedent and require repo-owned package
  code, tests, and fixtures for the first release.

### Edge 9: Starter-Domain Drift

- Risk:
  the substrate could widen into a generic semantic metalanguage before proving one
  bounded domain.
- Response:
  freeze the starter domain to `repo_policy_work` in `V49-A`.

### Edge 10: Fixtureless Substrate Law

- Risk:
  the slice could claim a substrate law without committed accepted/reject fixtures that
  actually prove identity, equivalence, ambiguity, and unsupported posture.
- Response:
  require fixture-based acceptance for hash stability, projection-only drift,
  identity-field drift, accepted outcomes, and invalid outcome rejection.

### Edge 11: Consumer Prematurity

- Risk:
  later consumers such as symbol audit, paper semantics, or `V48` bridge helpers
  could leak into the first slice and blur ownership.
- Response:
  keep `V49-A` bounded to the substrate contract only and defer all consumers to later
  slices or later families.

## Current Judgment

- `V49-A` is worth implementing now because the repo has already closed `V45`, `V47`,
  and `V48`, has normalized the imported prototype bundles into support-only intake
  packs, and still lacks one repo-owned canonical semantic substrate family.
- the first implementation move should remain narrowly contract-first: freeze the
  semantic unit, identity law, equivalence posture, ambiguity / unsupported posture,
  and starter-domain boundary before accepting any parser or lowering behavior.
