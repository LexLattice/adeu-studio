# ADEU Semantic Forms v0 Bundle Alignment

Authority layer: support / maintainer intake note only.

Source lane:

- imported external prototype bundle
- class: `X2`
- precedent status: `non_precedent`

## Artifact Relationship

- narrative ingress note:
  [CLAIMED_SCOPE.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/CLAIMED_SCOPE.md)
- unpacked source payload:
  [source_tree](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree)
- in-pack prototype readme:
  [source_tree/adeu_semantic_forms_v0/README.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/README.md)

## Claimed Scope

The combined narrative and bundle claim:

- a bounded semantic-intent package above the released `V45` / `V47` / `V48-A` seam
- profile-relative natural-language recovery into canonical semantic normal form
- deterministic lowering from semantic normal form into a `V48`-adjacent taskpack
  binding seed
- bundled sample parse/transform artifacts for the starter domain `repo_policy_work`

## Observed Reachable Surfaces

The unpacked source tree contains:

- package source under
  [source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0)
- package-style models and parser candidates at
  [models.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/models.py),
  [parse_profile.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/parse_profile.py),
  [parser.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/parser.py),
  and
  [transform_v48_seed.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/transform_v48_seed.py)
- sample artifacts under
  [source_tree/adeu_semantic_forms_v0/samples](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/samples)

## Accepted Shipped Scope

Current accepted shipped scope is intentionally narrow:

- intake pack only
- unpacked source tree and sample artifacts only
- no accepted package addition
- no accepted schema contract
- no accepted bridge into live `V48` builders

## Maintainer Alignment Notes

- This is the strongest fit so far for repo philosophy because it is read-only,
  typed, and explicitly positioned as a bounded layer over already released surfaces.
- It is still not internal ADEU work yet because it proposes a new family surface and
  a new transform contract without prior repo-native planning.
- The bundle did not include runnable tests in the `tests/` directory, so the
  verification story remains sample-oriented rather than repo-gated.

## Required Before Internal Integration

- decide whether this belongs in an existing planning family or needs a new one
- freeze the authority boundary between:
  - fallible `NL -> ADEU` recovery
  - deterministic `ADEU -> ADEU` transform
- decide where the canonical artifact schemas should live if internalized
- re-author one bounded internal slice from repo-owned package/tests/docs rather than
  importing the bundle wholesale
