# Draft ADEU Paper Semantics V52A Implementation Mapping v0

Status: support note for the `V52-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the imported GPT
Pro `adeu-paper-semantic-workbench-poc` prototype should be used as shaping evidence
while the live repo-owned `V52-A` implementation is re-authored in
`packages/adeu_paper_semantics`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS127.md`
- `examples/external_prototypes/adeu-paper-semantic-workbench-poc/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the bounded source-artifact kinds:
  - `paper.abstract`
  - `pasted.paragraph`
- the worker-request posture:
  - `analysis_mode = evidence_first`
  - `authority_mode = advisory_only`
  - `preserve_source_anchor = true`
- the starter O/E/D/U lane vocabulary
- the starter diagnostic-kind vocabulary:
  - `contradiction`
  - `underdetermination`
  - `missing_bridge`
  - `overloaded_term`
  - `implicit_assumption`
  - `u_overreach`
- the span-anchor concept of explicit start/end offsets plus sentence/paragraph index
- the claim / lane-fragment / inference-bridge decomposition concept
- the bounded requested-depth vocabulary:
  - `1`
  - `2`

## Re-Author With Repo Alignment

- create the repo-owned package scaffold under:
  - `packages/adeu_paper_semantics/src/adeu_paper_semantics/`
  - `packages/adeu_paper_semantics/tests/`
- re-author the overlay schema ideas as repo-owned Pydantic models rather than
  importing `adeu_core_ir` schema files wholesale
- make the first paper semantic ontology explicit in `models.py`:
  - source artifact
  - source span
  - semantic claim
  - lane fragment
  - inference bridge
  - diagnostic
  - projection
  - semantic artifact
  - worker request
- reuse the released `V49` canonical hash / identity-vs-projection posture where
  selected, or declare the paper-domain delta explicitly in live contract code
- keep diagnostics and projections excluded from semantic identity and semantic hash
- re-author deterministic reference and reject fixtures in repo-native tests
- add repo-native package exports and bootstrap integration

## Defer To Later Slice

- the read-only mock workbench route to `V52-B`
- any live worker request/response bridge to `V52-C`
- any `urm_domain_paper` or `urm_domain_adeu` registration work to `V52-C`
- spatial lane scene or richer morphic visualization to `V52-D`
- `paper.abstract_digest` and broader full-paper artifact classes to later family work
- any direct modification of the existing `/papers` route to `V52-B` or later

## Do Not Import

- the prototype overlay tree wholesale into live package or app paths
- the prototype `/papers/semantic-workbench` route into `V52-A`
- the prototype `adeu_core_ir` schema files as if they were already accepted live
  repo authority
- the prototype `urm_domain_adeu` workflow additions as if they were already accepted
  live repo authority
- the prototype spatial scene or advanced visualization surfaces into `V52-A`
- any silent full-paper or `paper.abstract_digest` widening in the first slice
