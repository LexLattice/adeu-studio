# Assessment vNext+117 Edges

Status: post-closeout edge assessment for `V49-A` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS117_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Starter Semantic Unit Drift

- Risk:
  the first substrate slice could claim semantic language ownership while leaving the
  smallest starter ADEU statement / calculus unit implicit.
- Response:
  freeze one starter statement core, one relation vocabulary, one lane vocabulary,
  one object-kind vocabulary, and one bounded starter qualifier posture in
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`.
- Closeout Evidence:
  constants, typed literals, and model validation in
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, plus committed
  reference fixtures under `packages/adeu_semantic_forms/tests/fixtures/v49a/`.

### Edge 2: Identity-Law Softness

- Risk:
  canonical semantic identity could still be described narratively while remaining
  operationally soft.
- Response:
  freeze `relation_kind` plus `object_value` as the only identity-participating
  fields and compute semantic hashes deterministically from the canonical basis.
- Closeout Evidence:
  `IDENTITY_FIELD_NAMES`, semantic-hash validators, mutation fixtures
  `mutation_semantic_normal_form_projection_only.json` and
  `mutation_semantic_normal_form_identity_change.json`, and tests in
  `packages/adeu_semantic_forms/tests/test_semantic_forms_models.py`.

### Edge 3: Projection / Support Leakage

- Risk:
  support-only or projection-only fields could quietly change semantic identity.
- Response:
  freeze `lane_tag`, `object_kind`, `evidence`, `confidence_band`, and
  `uncertainty_notes` as validated but non-identity fields in the starter slice.
- Closeout Evidence:
  `PROJECTION_FIELD_NAMES` and semantic-hash basis logic in
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, plus the
  projection-only mutation replay test.

### Edge 4: Schema-Family Placeholder Drift

- Risk:
  the first semantic substrate slice could ship scaffolding while leaving the actual
  contract family unresolved.
- Response:
  select the first schema family concretely in the lock and code:
  `adeu_semantic_parse_profile@1`, `adeu_semantic_statement_core@1`,
  `adeu_semantic_normal_form@1`, `adeu_semantic_parse_result@1`, and
  `adeu_semantic_transform_contract@1`.
- Closeout Evidence:
  exported schema constants in
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py` and
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/__init__.py`.

### Edge 5: Ambiguity / Unsupported Split Drift

- Risk:
  parse results could ship while ambiguity and unsupported posture remain only
  half-frozen.
- Response:
  keep both ambiguity and unsupported posture typed in the shipped contract surface
  before any recovery engine is introduced.
- Closeout Evidence:
  `ParseStatus`, `AmbiguityKind`, `RejectedReasonCode`, parse-result validators in
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, and committed
  accepted/reject fixtures.

### Edge 6: Recovery Laundering

- Risk:
  the first substrate move could quietly smuggle in parser behavior or natural-language
  heuristics.
- Response:
  keep `V49-A` contract-first only and defer all `NL -> ADEU` behavior to `V49-B`.
- Closeout Evidence:
  implementation footprint limited to `models.py`, `parse_profile.py`, fixtures,
  tests, and bootstrap integration; no parser source exists under
  `packages/adeu_semantic_forms`.

### Edge 7: Lowering / Bridge Laundering

- Risk:
  the first substrate slice could overreach into deterministic lowering or released
  `V48` bridge behavior before the semantic contracts are stable.
- Response:
  defer lowering to `V49-C` and downstream `V48` bridge helpers to `V49-D`.
- Closeout Evidence:
  absence of lowering / bridge implementation files under
  `packages/adeu_semantic_forms`, and no `V48` helper surface shipped in `v117`.

### Edge 8: Imported-Bundle Precedent Drift

- Risk:
  the normalized external prototype pack could still be overread as the live authority
  surface for the package.
- Response:
  re-author the live package in repo-owned paths and keep the external intake bundle
  support-only / non-precedent.
- Closeout Evidence:
  live package sources under `packages/adeu_semantic_forms/`, imported bundle retained
  under `examples/external_prototypes/adeu-semantic-forms-v0-bundle`, and no direct
  prototype-tree import into live package paths.

### Edge 9: Support-Only Intake Collection Leakage

- Risk:
  support-only prototype intake could leak into default repo lint/test collection and
  become accidental live surface.
- Response:
  keep the intake area excluded from default Ruff and pytest discovery.
- Closeout Evidence:
  `extend-exclude = ["examples/external_prototypes"]` and
  `norecursedirs = ["examples/external_prototypes"]` in `pyproject.toml`.

### Edge 10: Starter-Domain Drift

- Risk:
  the substrate could widen into a generic semantic metalanguage before proving one
  bounded domain.
- Response:
  freeze the starter domain to `repo_policy_work`.
- Closeout Evidence:
  `SemanticDomainKind = Literal["repo_policy_work"]` in
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, reference builder
  in `packages/adeu_semantic_forms/src/adeu_semantic_forms/parse_profile.py`, and the
  committed parse-profile fixture.

### Edge 11: Fixtureless Substrate Law

- Risk:
  the slice could claim substrate law without committed fixtures that prove identity,
  projection-only drift, ambiguity posture, unsupported posture, and fail-closed
  rejection.
- Response:
  require committed accepted, mutation, and reject fixtures in the first release.
- Closeout Evidence:
  fixture set under `packages/adeu_semantic_forms/tests/fixtures/v49a/` and replay
  coverage in package tests.

### Edge 12: Canonical Helper Inventory Drift

- Risk:
  the new package could introduce canonical JSON helpers without being recorded in the
  repo-wide frozen helper inventory.
- Response:
  extend the existing `vnext+27` canonical JSON conformance guard explicitly rather
  than weakening it.
- Closeout Evidence:
  `apps/api/tests/test_canonical_json_conformance_vnext_plus27.py` includes
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py::canonical_json`
  and `::sha256_canonical_json`.

### Edge 13: Consumer Prematurity

- Risk:
  symbol audit, paper semantics, simulation, or product consumers could leak into the
  first semantic substrate release and blur ownership.
- Response:
  keep `V49-A` bounded to substrate contracts only and defer all consumers to later
  slices or later families.
- Closeout Evidence:
  shipped scope limited to package contracts, fixtures, tests, and bootstrap
  integration; no consumer packages or routes changed in the merged `v117` slice.

## Current Judgment

- `V49-A` was the right first `V49` move because the repo had already closed `V45`,
  `V47`, and `V48`, had normalized the imported prototype bundles into support-only
  intake packs, and still lacked one repo-owned canonical semantic substrate family.
- the shipped result is properly narrow: one repo-owned `adeu_semantic_forms`
  package, one bounded `repo_policy_work` starter domain, one frozen starter
  statement-core/relation/lane/object contract set, one canonical semantic identity
  law, one typed ambiguity/unsupported posture, deterministic fixtures, and no parser,
  lowering, bridge, or product-surface widening.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` should now be read with `V49-A` closed on
  `main` and the branch-local default next path advanced to `V49-B`.
