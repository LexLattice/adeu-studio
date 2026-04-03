# ADEU Paper Semantic Workbench POC Alignment

Authority layer: support / maintainer intake note only.

Source lane:

- imported external prototype bundle
- class: `X2`
- precedent status: `non_precedent`

## Artifact Relationship

- narrative ingress note:
  [CLAIMED_SCOPE.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc/CLAIMED_SCOPE.md)
- unpacked source payload:
  [source_overlay](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc/source_overlay)

This pack is an overlay-oriented import. Its payload preserves repo-relative paths as
claimed by the prototype rather than being installed into the live repo surfaces.

## Claimed Scope

The imported narrative claims:

- a new web route at `/papers/semantic-workbench`
- new `adeu_core_ir` schema surfaces for paper semantic workbench artifacts and worker
  requests
- a new `urm_domain_adeu` workflow template
- smoke/API test updates implying live integration

## Observed Reachable Surfaces

The unpacked overlay contains the following candidate surfaces:

- web route additions under
  [source_overlay/apps/web/src/app/papers/semantic-workbench](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc/source_overlay/apps/web/src/app/papers/semantic-workbench)
- papers index modification at
  [source_overlay/apps/web/src/app/papers/page.tsx](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc/source_overlay/apps/web/src/app/papers/page.tsx)
- new schema candidates at
  [source_overlay/packages/adeu_core_ir/schema/paper_semantic_workbench.v1.json](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc/source_overlay/packages/adeu_core_ir/schema/paper_semantic_workbench.v1.json)
  and
  [source_overlay/packages/adeu_core_ir/schema/paper_semantic_worker_request.v1.json](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc/source_overlay/packages/adeu_core_ir/schema/paper_semantic_worker_request.v1.json)
- workflow template registration candidate at
  [source_overlay/packages/urm_domain_adeu/src/urm_domain_adeu/adapters.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc/source_overlay/packages/urm_domain_adeu/src/urm_domain_adeu/adapters.py)
- smoke/API test modifications under
  [source_overlay/apps/web/tests/routes.smoke.test.mjs](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc/source_overlay/apps/web/tests/routes.smoke.test.mjs)
  and
  [source_overlay/apps/api/tests/test_urm_domain_tools.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc/source_overlay/apps/api/tests/test_urm_domain_tools.py)

## Accepted Shipped Scope

Current accepted shipped scope is intentionally narrow:

- intake pack only
- unpacked overlay only
- no live repo integration
- no accepted new schema contract
- no accepted product-surface reachability
- no accepted workflow-template expansion

## Maintainer Alignment Notes

- The concept is promising, but the import mixes product surface, worker contract,
  schema, and domain-template changes in one payload.
- That makes it unsuitable for direct merge into the internal ADEU lane without
  planning and slice decomposition.
- The imported test files are not treated as evidence that the route or schema is now
  repo-accepted; they only show the claimed prototype reach.

## Required Before Internal Integration

- choose an internal family and slice order rather than importing the whole overlay at
  once
- decide whether the first slice is:
  - schema-first
  - harness-first
  - web demo-first
- bind the worker/request contract to an explicit authority posture rather than only a
  frontend narrative
- normalize the overlay into repo-native package ownership and verification gates
