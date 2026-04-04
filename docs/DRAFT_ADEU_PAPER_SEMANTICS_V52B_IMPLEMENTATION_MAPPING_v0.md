# Draft ADEU Paper Semantics V52B Implementation Mapping v0

Status: support note for the `V52-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the imported GPT
Pro `adeu-paper-semantic-workbench-poc` prototype should be used as shaping evidence
while the live repo-owned `V52-B` implementation is re-authored in
`apps/web/src/app/papers/semantic-workbench/`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS128.md`
- `docs/DRAFT_ADEU_PAPER_SEMANTICS_V52A_IMPLEMENTATION_MAPPING_v0.md`
- `examples/external_prototypes/adeu-paper-semantic-workbench-poc/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the bounded route concept:
  - `/papers/semantic-workbench`
- the read-only workbench posture over committed/sample artifacts
- the bounded two-surface viewing posture:
  - `artifact`
  - `local`
- the rendering emphasis on:
  - source metadata
  - anchored spans
  - claims
  - lane fragments
  - diagnostics
  - projections
- the local claim/lane navigation concept, provided it remains subordinate to released
  `V52-A` artifacts

## Re-Author With Repo Alignment

- create the repo-owned route under:
  - `apps/web/src/app/papers/semantic-workbench/`
- consume released `packages/adeu_paper_semantics` artifacts directly instead of
  importing the prototype `schema.ts` as authority
- use the committed released `v52a` artifact fixtures as the initial sample registry
- validate each committed sample JSON against the released `PaperSemanticArtifact`
  model before route-local rendering
- build one bounded view-model layer that preserves released artifact payloads,
  including `semantic_hash`, `identity_field_names`, and `projection_field_names`,
  and adds only deterministic local ordering/focus helpers
- keep the two refs distinct:
  - `selected_sample_artifact_ref` as committed fixture-path identity
  - `artifact_ref` as released artifact-id identity
- use released `projection.claim_order` when present and only fall back to
  deterministic claim-id order when absent
- add repo-native route smoke and bounded interaction/contract tests under
  `apps/web/tests/`

## Defer To Later Slice

- any live worker request/response bridge to `V52-C`
- any `urm_domain_paper` or `urm_domain_adeu` registration work to `V52-C`
- any API-backed or harness-backed refresh loop to `V52-C`
- spatial lane scene or richer morphic visualization to `V52-D`
- broader `/papers` product integration beyond the single bounded route to later work

## Do Not Import

- `live-worker.ts` into `V52-B`
- `spatial-lane-scene.tsx` into `V52-B`
- the prototype `schema.ts` as live route authority
- any prototype mock-processing that fabricates new semantic outputs instead of
  consuming released `V52-A` artifacts
- direct overlay files copied wholesale into live repo paths
- freeform text-entry or upload-driven processing surfaces in this slice
