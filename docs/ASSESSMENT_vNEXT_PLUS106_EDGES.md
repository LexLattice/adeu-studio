# Assessment vNext+106 Edges

Status: post-closeout edge assessment for `V47-A` (April 1, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS106_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Prose-Inference Leakage

- Risk:
  the slice could claim markdown-native policy while still recovering obligations from
  ordinary prose outside `D@1`.
- Response:
  keep authoritative policy semantics fenced and fail closed on prose-only obligation
  claims.
- Closeout Evidence:
  parsing/compiler enforcement in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  reject fixture
  `packages/adeu_semantic_source/tests/fixtures/v47a/reject_prose_only_obligation.md`,
  and rejection coverage in `packages/adeu_semantic_source/tests/test_anm.py`.

### Edge 2: Source / IR / Facts / Results / Ledger Collapse

- Risk:
  the first release could flatten the pipeline into one mixed evaluator artifact,
  making later authority boundaries hard to inspect.
- Response:
  keep source, normalized semantics, checker facts, result sets, and ledger state as
  distinct first-class surfaces.
- Closeout Evidence:
  shipped models in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  schema exports under `packages/adeu_commitments_ir/schema/`,
  and deterministic reference-chain replay in
  `packages/adeu_semantic_source/tests/test_anm.py`.

### Edge 3: Bootstrap Ownership Overreach

- Risk:
  bootstrap string selectors or bootstrap predicate contracts could silently harden into
  broader O-owned selector or E-owned predicate-registry doctrine.
- Response:
  keep selector and predicate ownership explicitly bootstrap-only in `V47-A` and defer
  the ownership transition lane.
- Closeout Evidence:
  bounded starter doctrine in `docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md`,
  predicate contract models in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  and accepted predicate-contract fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47a/reference_predicate_contracts_bootstrap.json`.

### Edge 4: Result-To-Ledger Drift

- Risk:
  `applicability`, `observed_outcome`, `effective_verdict`, and `ledger_state` could
  drift apart or be only partially represented.
- Response:
  freeze explicit mapping and preserve `latest_applicability`,
  `latest_observed_outcome`, and `latest_effective_verdict` on ledger rows.
- Closeout Evidence:
  result/ledger models in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  ledger projection in `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  and accepted fixtures
  `reference_policy_evaluation_result_set.json` plus
  `reference_policy_obligation_ledger.json`.

### Edge 5: Zero-Match / `GatedOff` Confusion

- Risk:
  selector zero-match and `gated_off` could be treated as the same operational posture,
  obscuring whether an obligation instance was ever formed.
- Response:
  keep zero-match as notice-only with no first row, while preserving `gated_off` as a
  non-active instantiated row when subject resolution succeeded.
- Closeout Evidence:
  `packages/adeu_semantic_source/tests/test_anm.py::test_v47a_zero_match_emits_notice_without_ledger_rows`,
  `packages/adeu_commitments_ir/tests/fixtures/v47a/zero_match_fact_bundle.json`,
  and ledger projection logic in `anm.py`.

### Edge 6: Clause-Scope Blocker Row Collapse

- Risk:
  result rows could be modeled as if every row were subject-scoped, making
  clause-scope blocker postures impossible to represent cleanly.
- Response:
  support both:
  - subject-scoped result rows with `subject_ref`;
  - clause-scope blocker rows without `subject_ref`.
- Closeout Evidence:
  `PolicyEvaluationResultRow` validation in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  accepted fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47a/reference_policy_evaluation_result_set.json`,
  and blocker-handling coverage in `packages/adeu_semantic_source/tests/test_anm.py`.

### Edge 7: Clause-Scope `UnknownResolution` Fabrication

- Risk:
  clause-scope `unknown_resolution` could fabricate ledger rows even when no
  `subject_ref` was formed.
- Response:
  keep that posture as a blocking evaluator result only until a resolvable subject
  exists.
- Closeout Evidence:
  reject fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47a/reject_clause_scope_blocker_fabricated_ledger_row.json`,
  rejection coverage in
  `packages/adeu_commitments_ir/tests/test_anm_models.py`,
  and unknown-selector coverage in
  `packages/adeu_semantic_source/tests/test_anm.py::test_v47a_unsupported_selector_stays_clause_scope_blocker_without_ledger_row`.

### Edge 8: Fact-Row Shape Flattening

- Risk:
  the starter fact vocabulary could be flattened into one universal fact-row shape,
  forcing fields like `path` or `values` onto fact kinds that do not naturally carry
  them.
- Response:
  keep checker facts as a tagged union by `fact_type` and make payload fields
  fact-kind-specific.
- Closeout Evidence:
  checker-fact union models in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  accepted fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47a/reference_fact_bundle.json`,
  and reject fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47a/reject_fact_bundle_with_verdict.json`.

### Edge 9: Checker Authority Laundering

- Risk:
  fact bundles could quietly become pseudo-evaluators that decide compliance or carry
  policy verdicts.
- Response:
  keep the checker surface fact-only and forbid verdict ownership in typed fact rows.
- Closeout Evidence:
  `CheckerFactBundle` validation in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  reject fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47a/reject_fact_bundle_with_verdict.json`,
  and rejection assertions in
  `packages/adeu_commitments_ir/tests/test_anm_models.py`.

### Edge 10: Ledger Authority Laundering

- Risk:
  the first ledger release could be overread as waiver/deferral/approval authority
  rather than operational state projection.
- Response:
  keep the ledger bounded to current-state tracking over instantiated obligations and
  require external authority for waiver/deferral semantics.
- Closeout Evidence:
  bounded ledger model in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  accepted fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47a/reference_policy_obligation_ledger.json`,
  and lock boundary in `docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md`.

### Edge 11: Selector Surface Under-Specification

- Risk:
  selector handling could remain implicit in `D-IR`, leaving clause-to-selector
  linkage hidden in prose or implementation folklore.
- Response:
  give `D-IR` a first-class selector-ref surface and explicit clause-to-selector
  linkage in the starter contract.
- Closeout Evidence:
  `D1NormalizedIR` schema/model surfaces in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  schema export `packages/adeu_commitments_ir/schema/d1_normalized_ir.v1.json`,
  and accepted fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47a/reference_d1_normalized_ir.json`.

### Edge 12: Predicate Contract Over-Operationalization

- Risk:
  bootstrap predicate contracts could be pulled too close to run-state by carrying
  evaluation-scope fields that belong elsewhere.
- Response:
  keep predicate contracts semantic and scope-independent in `V47-A`; operational
  scope belongs in fact bundles and result sets instead.
- Closeout Evidence:
  contract bundle shape in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  authoritative schema
  `packages/adeu_commitments_ir/schema/predicate_contracts_bootstrap.v1.json`,
  and accepted fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47a/reference_predicate_contracts_bootstrap.json`.

### Edge 13: Coexistence Overreach

- Risk:
  the first ANM slice could be mistaken for a mandate to migrate or override existing
  lock/planning markdown authority.
- Response:
  freeze only the minimum coexistence boundary in `V47-A`: no override, no repo-wide
  migration, companion posture allowed.
- Closeout Evidence:
  frozen coexistence wording in `docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md`
  and planning boundary in `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`.

### Edge 14: Starter Vocabulary Drift

- Risk:
  released fact-kind and provenance-mode enums could widen silently between the lock
  doc and the first implementation, weakening the tiny reference chain boundary.
- Response:
  require exact starter-vocabulary match in `V47-A` and defer widening to `V47-B`.
- Closeout Evidence:
  starter vocabularies in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  accepted reference fixtures under
  `packages/adeu_commitments_ir/tests/fixtures/v47a/`,
  and lock boundary in `docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md`.

### Edge 15: Package-Boundary Drift

- Risk:
  ANM source parsing, normative IR, and operational ledger logic could be scattered
  across too many packages in the first slice, raising review and contract drift risk.
- Response:
  keep the first slice bounded to `adeu_semantic_source` plus `adeu_commitments_ir`.
- Closeout Evidence:
  shipped implementation footprint in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  and bounded package selection in `docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md`.

## Current Judgment

- `V47-A` was worth implementing because the ANM / `D@1` seed bundle had reached
  bounded arc-ready quality and already carried a coherent typed artifact family.
- `V47-A` on `main` now resolves the first authoritative normative markdown substrate
  gap by shipping a deterministic source-to-ledger chain with explicit `D@1`
  authority boundaries, explicit selector/predicate semantics, fact-only checker
  posture, run-specific result sets, and cross-run ledger projection.
- the shipped seam remains substrate-first and non-authorizing so later `V47-B+`
  vocabulary hardening, coexistence widening, or ownership-transition families can
  consume it without being silently authorized by checker facts or ledger state.
