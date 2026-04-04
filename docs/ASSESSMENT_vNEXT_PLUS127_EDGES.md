# Assessment vNext+127 Edges

Status: start-bundle edge assessment for `V52-A` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS127_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Parallel Substrate Drift

- Risk:
  paper-domain contracts could quietly mint a second semantic substrate instead of
  behaving as the first bounded domain consumer of released `V49`.
- Response:
  freeze explicit `V49` reuse or explicit narrow delta declaration, plus the
  identity-vs-projection split and canonical hash posture.
- Start-Bundle Evidence:
  `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS127.md`.

### Edge 2: Scope Inflation Beyond Abstract Scale

- Risk:
  the first slice could claim full-paper semantics or admit `paper.abstract_digest`
  and broader artifact classes before the family earns that breadth.
- Response:
  freeze the first slice to `paper.abstract` and `pasted.paragraph` only.
- Start-Bundle Evidence:
  bounded source-artifact strategy and selected vocabularies in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS127.md`.

### Edge 3: Source Authority Becomes Soft

- Risk:
  inferred content, bridge heuristics, or diagnostics could outrank anchored source
  spans and collapse the intended source-authority posture.
- Response:
  keep source text plus explicit span anchors authoritative and keep interpretation
  advisory only.
- Start-Bundle Evidence:
  objective and authority-posture strategy in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS127.md`.

### Edge 4: Diagnostics Become Second Semantic Owner

- Risk:
  diagnostics and projections could become effective semantic identity instead of
  advisory/support surfaces.
- Response:
  exclude diagnostics and projections from semantic hash and keep them advisory-only.
- Start-Bundle Evidence:
  `diagnostic_and_projection_fields_excluded_from_semantic_hash = true` and
  acceptance criteria in `docs/LOCKED_CONTINUATION_vNEXT_PLUS127.md`.

### Edge 5: Overlay Laundering Into Live Authority

- Risk:
  the imported `adeu_core_ir` schema and `urm_domain_adeu` workflow additions could be
  copied into live repo paths and treated as accepted authority.
- Response:
  keep the overlay support-only and re-author live ownership in
  `packages/adeu_paper_semantics` only.
- Start-Bundle Evidence:
  `examples/external_prototypes/adeu-paper-semantic-workbench-poc/ALIGNMENT.md`,
  `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md`, and the lock package-ownership strategy.

### Edge 6: Consumer Surfaces Arrive Too Early

- Risk:
  the first contract slice could drift into `/papers/semantic-workbench`, live worker
  bridge, or advanced visualization work.
- Response:
  keep `V52-A` strictly package-first and pre-consumer.
- Start-Bundle Evidence:
  widening strategy in `docs/LOCKED_CONTINUATION_vNEXT_PLUS127.md`.

### Edge 7: Contract Shape Stays Too Coarse

- Risk:
  the first slice could hide key paper semantics inside one broad workbench payload
  and undercut later bounded consumers.
- Response:
  freeze first-class models for source artifacts, spans, claims, lane fragments,
  inference bridges, diagnostics, projections, top-level artifacts, and worker
  requests.
- Start-Bundle Evidence:
  artifact-family strategy and selected schema anchors in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS127.md`.

## Current Judgment

- `V52-A` is the right first D-track slice because it internalizes the imported
  workbench concept at the narrowest seam that can actually carry domain authority.
- the slice is properly bounded if implemented as written: one package, one abstract-
  scale contract family, one explicit source-authority posture, one advisory-only
  interpretation posture, one typed worker-request contract, and no web/worker/visual
  widening.
- the main implementation risk is silent parallel-substrate drift; the lock addresses
  that by requiring explicit `V49` reuse or explicit narrow delta declaration.
