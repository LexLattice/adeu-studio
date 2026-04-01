# Assessment vNext+106 Edges

Status: planning-edge assessment for `V47-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS106_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
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

### Edge 2: Source / IR / Facts / Results / Ledger Collapse

- Risk:
  the first release could flatten the pipeline into one mixed evaluator artifact,
  making later authority boundaries hard to inspect.
- Response:
  keep source, normalized semantics, checker facts, result sets, and ledger state as
  distinct first-class surfaces.

### Edge 3: Bootstrap Ownership Overreach

- Risk:
  bootstrap string selectors or bootstrap predicate contracts could silently harden into
  broader O-owned selector or E-owned predicate-registry doctrine.
- Response:
  keep selector and predicate ownership explicitly bootstrap-only in `V47-A` and defer
  the ownership transition lane.

### Edge 4: Result-To-Ledger Drift

- Risk:
  `applicability`, `observed_outcome`, `effective_verdict`, and `ledger_state` could
  drift apart or be only partially represented.
- Response:
  freeze explicit mapping and preserve `latest_applicability`,
  `latest_observed_outcome`, and `latest_effective_verdict` on ledger rows.

### Edge 5: Zero-Match / `GatedOff` Confusion

- Risk:
  selector zero-match and `gated_off` could be treated as the same operational posture,
  obscuring whether an obligation instance was ever formed.
- Response:
  keep zero-match as notice-only with no first row, while preserving `gated_off` as a
  non-active instantiated row when subject resolution succeeded.

### Edge 6: Clause-Scope Blocker Row Collapse

- Risk:
  result rows could be modeled as if every row were subject-scoped, making
  clause-scope blocker postures impossible to represent cleanly.
- Response:
  support both:
  - subject-scoped result rows with `subject_ref`;
  - clause-scope blocker rows without `subject_ref`.

### Edge 7: Clause-Scope `UnknownResolution` Fabrication

- Risk:
  clause-scope `unknown_resolution` could fabricate ledger rows even when no
  `subject_ref` was formed.
- Response:
  keep that posture as a blocking evaluator result only until a resolvable subject
  exists.

### Edge 8: Fact-Row Shape Flattening

- Risk:
  the starter fact vocabulary could be flattened into one universal fact-row shape,
  forcing fields like `path` or `values` onto fact kinds that do not naturally carry
  them.
- Response:
  keep checker facts as a tagged union by `fact_type` and make payload fields
  fact-kind-specific.

### Edge 9: Checker Authority Laundering

- Risk:
  fact bundles could quietly become pseudo-evaluators that decide compliance or carry
  policy verdicts.
- Response:
  keep the checker surface fact-only and forbid verdict ownership in typed fact rows.

### Edge 10: Ledger Authority Laundering

- Risk:
  the first ledger release could be overread as waiver/deferral/approval authority
  rather than operational state projection.
- Response:
  keep the ledger bounded to current-state tracking over instantiated obligations and
  require external authority for waiver/deferral semantics.

### Edge 11: Selector Surface Under-Specification

- Risk:
  selector handling could remain implicit in `D-IR`, leaving clause-to-selector
  linkage hidden in prose or implementation folklore.
- Response:
  give `D-IR` a first-class selector-ref surface and explicit clause-to-selector
  linkage in the starter contract.

### Edge 12: Predicate Contract Over-Operationalization

- Risk:
  bootstrap predicate contracts could be pulled too close to run-state by carrying
  evaluation-scope fields that belong elsewhere.
- Response:
  keep predicate contracts semantic and scope-independent in `V47-A`; operational
  scope belongs in fact bundles and result sets instead.

### Edge 13: Coexistence Overreach

- Risk:
  the first ANM slice could be mistaken for a mandate to migrate or override existing
  lock/planning markdown authority.
- Response:
  freeze only the minimum coexistence boundary in `V47-A`: no override, no repo-wide
  migration, companion posture allowed.

### Edge 14: Starter Vocabulary Drift

- Risk:
  released fact-kind and provenance-mode enums could widen silently between the lock
  doc and the first implementation, weakening the tiny reference chain boundary.
- Response:
  require exact starter-vocabulary match in `V47-A` and defer widening to `V47-B`.

### Edge 15: Package-Boundary Drift

- Risk:
  ANM source parsing, normative IR, and operational ledger logic could be scattered
  across too many packages in the first slice, raising review and contract drift risk.
- Response:
  keep the first slice bounded to `adeu_semantic_source` plus `adeu_commitments_ir`.

## Current Judgment

- `V47-A` is worth implementing now because the ANM / `D@1` bundle has reached
  arc-ready seed quality and already carries a coherent bounded artifact family.
- the right first move is substrate-first:
  emit the typed chain cleanly before widening into migration, ownership transition, or
  downstream policy-bearing consumers.
