# Draft ADEU Paper Semantics V52C Implementation Mapping v0

Status: support note for the `V52-C` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the imported GPT
Pro `adeu-paper-semantic-workbench-poc` prototype should be used as shaping evidence
while the live repo-owned `V52-C` worker bridge is re-authored in
`packages/urm_domain_paper/`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS129.md`
- `docs/DRAFT_ADEU_PAPER_SEMANTICS_V52A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PAPER_SEMANTICS_V52B_IMPLEMENTATION_MAPPING_v0.md`
- `examples/external_prototypes/adeu-paper-semantic-workbench-poc/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the bounded live semantic-decomposition workflow concept
- the fixed read-only worker posture for paper semantic decomposition
- the idea of one dedicated semantic-decomposition template id
- the evidence-bearing worker-result posture:
  - `artifact_ref`
  - `worker_id`
  - `evidence_id`
  - `warrant_tag`
  - worker status / replay metadata

## Re-Author With Repo Alignment

- keep paper semantic authority in released `packages/adeu_paper_semantics`
- consume released `PaperSemanticWorkerRequest` directly instead of importing the
  prototype `adeu_core_ir` worker-request schema overlay
- extend the existing `packages/urm_domain_paper` domain pack instead of creating a
  new owner surface, and do not move ownership into `packages/urm_domain_adeu`
- expose exactly one bounded live tool:
  - `paper.run_semantic_decomposition`
- use one repo-owned template id under `urm_domain_paper`
- keep that tool additive with respect to the released:
  - `paper.ingest_text`
  - `paper.extract_abstract_candidate`
  - `paper.check_constraints`
  - `paper.emit_artifact`
- preserve the existing default template:
  - `paper.abstract.pipeline.v0`
- route live execution through the existing URM tool-call surface rather than adding a
  dedicated new API route
- emit one typed bridge result that carries request lineage plus `artifact_ref`,
  `warrant_tag`, and worker/evidence refs only
- add explicit capability-lattice / policy mapping for the new tool instead of relying
  on neighboring paper-tool authorization
- add repo-native bridge verification through `apps/api/tests/test_urm_domain_tools.py`
  and/or bounded `urm_domain_paper` tests, including regression on the existing
  paper-domain closed-world flow

## Defer To Later Slice

- any `apps/web` fetch or trigger wiring from `/papers/semantic-workbench`
- any route-side evidence readback or live semantic artifact rendering
- any broader workflow-template menu or multi-template orchestration
- any advanced visualization or richer motion/scene work to `V52-D`
- any ownership widening into broader `urm_domain_adeu` workflow surfaces

## Do Not Import

- `examples/external_prototypes/adeu-paper-semantic-workbench-poc/source_overlay/packages/urm_domain_adeu/src/urm_domain_adeu/adapters.py`
  as live authority
- imported `adeu_core_ir` schema additions as live bridge contracts
- imported `apps/api` or `apps/web` overlay files copied wholesale into live repo
  paths
- browser-local state as bridge authority
- live artifact rendering/readback inside the bridge result
