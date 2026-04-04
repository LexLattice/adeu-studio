# Draft ADEU Paper Semantics V52D Implementation Mapping v0

Status: support note for the `V52-D` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the imported GPT
Pro `adeu-paper-semantic-workbench-poc` prototype should be used as shaping evidence
while the live repo-owned `V52-D` visualization seam is re-authored in
`apps/web/src/app/papers/semantic-workbench/`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS130.md`
- `docs/DRAFT_ADEU_PAPER_SEMANTICS_V52A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PAPER_SEMANTICS_V52B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PAPER_SEMANTICS_V52C_IMPLEMENTATION_MAPPING_v0.md`
- `examples/external_prototypes/adeu-paper-semantic-workbench-poc/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the same-object morphic workbench concept across:
  - `artifact`
  - `local`
  - `spatial`
- the idea that 3D is used only where it clarifies structure:
  - the spatial lane recomposition view
- the route-local spatial projection concept over O/E/D/U structure
- the emphasis that source-anchored artifact facts remain authoritative while the
  visualization stays advisory/presentational

## Re-Author With Repo Alignment

- keep semantic authority in released `packages/adeu_paper_semantics`
- extend the already released `/papers/semantic-workbench` route instead of creating a
  second paper-semantics route
- derive the live scene only from released `V52-A` artifacts already admitted by the
  released `V52-B` sample registry and route-local view state
- keep route-local visualization config minimal and user-driven, matching the shipped
  `V52-B` config posture rather than moving derived artifact/view state into config
- treat `spatial` as a route-local derived surface only:
  - do not require a released `projection.surface = spatial`
  - preserve released `artifact` / `local` projections as ordering anchors
- preserve `semantic_hash`, identity/projection field visibility, and released
  authority posture in the route-local model
- add one repo-owned route-local scene component and projection helper under:
  - `apps/web/src/app/papers/semantic-workbench/`
- keep the scene deterministic:
  - no physics layout
  - no randomness
  - lane columns plus claim-order rows only
- validate it with bounded route smoke / contract / build coverage

## Defer To Later Slice

- browser-triggered live worker execution over the accepted `V52-C` bridge
- upload or pasted-source execution flows
- full-paper, bibliography, or citation-graph visualization
- deeper spatial interaction systems, scene editing, or persistent browser state
- broader `/papers` navigation/product redesign

## Do Not Import

- `examples/external_prototypes/adeu-paper-semantic-workbench-poc/source_overlay/apps/web/src/app/papers/semantic-workbench/spatial-lane-scene.tsx`
  as live authority
- the prototype `page.tsx` or `schema.ts` wholesale into live route paths
- the prototype live-worker scaffold into this visualization slice
- prototype route-local state as semantic authority
- any prototype overlay file copied wholesale into live repo paths
