# Assessment vNext+127 Edges

Status: post-closeout edge assessment for `V52-A` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS127_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Parallel `V49`-Adjacent Substrate Drift

- Risk:
  paper-domain contracts could quietly mint a second semantic substrate instead of
  behaving as the first bounded domain consumer of released `V49`.
- Response:
  keep direct `V49` hash-law reuse explicit and keep any paper-domain delta narrow,
  visible, and non-silent.
- Closeout Evidence:
  `sha256_canonical_json` reuse from `adeu_semantic_forms`, `SEMANTIC_IDENTITY_MODE`,
  and the committed `v52a` fixtures under
  `packages/adeu_paper_semantics/tests/fixtures/v52a/`.

### Edge 2: Source-Authority Drift

- Risk:
  inferred fragments or diagnostics could outrank anchored source text and collapse
  the intended source-authority posture.
- Response:
  keep source text plus explicit span anchors authoritative and keep interpretation
  advisory only.
- Closeout Evidence:
  `SOURCE_AUTHORITY_POSTURE`, `INTERPRETATION_AUTHORITY_POSTURE`, anchored quote-slice
  validation in `models.py`, and the malformed-span reject fixture.

### Edge 3: Projection/Diagnostic Identity Laundering

- Risk:
  diagnostics, projections, or explanatory warrant text could become effective
  semantic identity instead of advisory/support surfaces.
- Response:
  keep identity-vs-projection split explicit and exclude projection/support fields
  from semantic hash.
- Closeout Evidence:
  `IDENTITY_FIELD_NAMES`, `PROJECTION_FIELD_NAMES`, and the paired mutation tests for
  projection-only vs identity-bearing change in
  `test_paper_semantics_models.py`.

### Edge 4: Contradictory Claim/Fragment Ownership

- Risk:
  multi-claim artifacts could validate even when one claim lists a fragment owned by a
  different claim, leaving downstream grouping ambiguous.
- Response:
  require exact bidirectional equality between `claim.lane_fragment_ids` and the
  fragments whose `claim_id` points back to that claim.
- Closeout Evidence:
  `claim lane_fragment_ids must exactly match owned fragment claim_id bindings`
  validation in `models.py` and
  `test_claim_fragment_ownership_must_be_bidirectionally_consistent`.

### Edge 5: Scale Inflation Beyond Abstract/Paragraph

- Risk:
  the first slice could over-claim broader paper semantics and silently admit
  `paper.abstract_digest` or full-paper semantics.
- Response:
  freeze `V52-A` to `paper.abstract` and `pasted.paragraph` only.
- Closeout Evidence:
  `SourceArtifactKind` in `models.py`, committed reference fixtures, and absence of
  broader paper-artifact kinds from the shipped package.

### Edge 6: Overlay Laundering Into Live Authority

- Risk:
  the imported workbench overlay could be treated as accepted schema/route/domain
  authority rather than shaping evidence only.
- Response:
  keep the imported bundle support-only and re-author live ownership in
  `packages/adeu_paper_semantics` only.
- Closeout Evidence:
  shipped code exists only under `packages/adeu_paper_semantics`, while the imported
  bundle remains under
  `examples/external_prototypes/adeu-paper-semantic-workbench-poc`.

### Edge 7: Consumer Prematurity

- Risk:
  the first paper-domain slice could drift into live workbench route, worker bridge,
  or advanced visualization seams before the contract family is accepted.
- Response:
  keep `V52-A` strictly package-first and pre-consumer.
- Closeout Evidence:
  merged scope limited to package source, fixtures, tests, and bootstrap wiring, with
  no `apps/web` or `urm_domain_*` implementation changes in the shipped slice.

### Edge 8: CI Import-Path Drift

- Risk:
  the bounded package could pass only under local `PYTHONPATH` overrides while failing
  full repo collection on CI.
- Response:
  wire the package into the repo bootstrap/editable-install path.
- Closeout Evidence:
  `Makefile` editable-install entry for `packages/adeu_paper_semantics[dev]` and green
  merged `python` CI on PR `#349`.

## Current Judgment

- `V52-A` was the right first D-track move because it internalized the paper semantic
  authority seam at the narrowest package-first boundary that could actually carry
  domain contracts.
- the shipped result is properly bounded: one repo-owned `adeu_paper_semantics`
  package, two bounded source-artifact kinds, explicit source-authority and
  advisory-only interpretation posture, first-class typed semantic substructures,
  direct `V49` identity/hash-law reuse, deterministic accepted/reject fixtures, and
  no live workbench, worker bridge, or advanced visualization widening.
- review hardening materially improved the release by closing the bidirectional
  claim/fragment ownership gap and aligning the lock wording with the shipped
  diagnostic contract.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` should now be read with `V52-A` closed on
  `main` and the branch-local default next path advanced to `V52-B` / `vNext+128`.
