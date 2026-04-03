I inspected the repo first and built this on the seams that are already there rather than inventing a parallel stack.

The key modules I grounded the design in were:

* `apps/web/src/app/papers/page.tsx` for the existing paper/document flow and repo-native web styling posture.
* `apps/web/src/app/artifact-inspector/page.tsx` and `reference-surface.ts` for the evidence-first, bounded, authority-sensitive workbench discipline.
* `apps/web/src/app/explain/page.tsx` for semantic-depth / diagnostics presentation cues.
* `apps/web/src/app/copilot/page.tsx` plus `apps/api/src/adeu_api/urm_routes.py` for the existing `/urm/tools/call` harness seam.
* `packages/urm_domain_adeu/src/urm_domain_adeu/adapters.py` for template registration and resident-worker workflow execution.
* `packages/adeu_core_ir/schema/ux_morph_ir.v1.json` and `ux_morph_diagnostics.v1.json` for explicit morphic UX and diagnostics posture.
* `apps/api/src/adeu_api/paper_pipeline.py` and `packages/urm_domain_paper/src/urm_domain_paper/models.py` to keep scope bounded to abstract-size paper artifacts.

## 1. Design rationale

* This module is a **bounded semantic inspection workbench** for abstract-size artifacts, not a generic visualization layer.
* The **source text remains authoritative** at every stage; all semantic structure stays visibly advisory.
* The core object is a typed **paper semantic artifact** that can be rendered in three representations: source-anchored artifact view, local O/E/D/U decomposition, and spatial lane recomposition.
* The UX stays **same-object morphic**: the operator feels one artifact changing representation, not separate disconnected pages.
* The schema is **span-anchored and recursive**, so depth 1 and depth 2 decompositions use the same model.
* Diagnostics are not decorative; contradiction, underdetermination, missing bridge, implicit assumption, overloaded term, and U-overreach are first-class typed outputs.
* The live path is routed through the repo’s existing **ADEU harness surfaces** using `adeu.list_templates`, `adeu.run_workflow`, and `adeu.read_evidence`.
* 3D is used only where it clarifies structure: the **spatial lane recomposition** view. The reference artifact and local analysis remain primarily 2D and operator-legible.
* Mock outputs are demo-complete now, while the live pipeline is honestly scaffolded and visibly distinct.

## 2. Repo-grounded file plan

### Added

* `apps/web/src/app/papers/semantic-workbench/page.tsx`
  New user-facing route at `/papers/semantic-workbench`. This is the main ADEU paper semantic workbench surface.

* `apps/web/src/app/papers/semantic-workbench/schema.ts`
  Repo-native TS schema family for source spans, ODEU decomposition, bridges, diagnostics, projections, and worker request/response contracts.

* `apps/web/src/app/papers/semantic-workbench/mock-processing.ts`
  Demo pipeline with:

  * 5 canonical AI paper samples,
  * curated mock semantic artifacts for sample papers,
  * reusable heuristic decomposition for pasted text.

* `apps/web/src/app/papers/semantic-workbench/live-worker.ts`
  Scaffolded resident Codex path using the existing ADEU harness surface:

  * request builder,
  * worker prompt contract,
  * template discovery,
  * workflow launch,
  * evidence loading,
  * structured artifact extraction.

* `apps/web/src/app/papers/semantic-workbench/spatial-lane-scene.tsx`
  R3F spatial lane recomposition surface for O/E/D/U node distribution and bridge rendering.

* `packages/adeu_core_ir/schema/paper_semantic_workbench.v1.json`
  JSON Schema for the semantic artifact returned to the frontend.

* `packages/adeu_core_ir/schema/paper_semantic_worker_request.v1.json`
  JSON Schema for the future resident-worker request.

### Modified

* `packages/urm_domain_adeu/src/urm_domain_adeu/adapters.py`
  Registered a new ADEU-native workflow template:
  `adeu.paper.semantic_decomposition.v0`

* `apps/web/src/app/papers/page.tsx`
  Added a native entry link to the new semantic workbench route.

* `apps/web/tests/routes.smoke.test.mjs`
  Added the new route to the smoke route matrix.

* `apps/api/tests/test_urm_domain_tools.py`
  Updated template assertions so the new live template is explicitly expected.

### Intentionally not modified

* `apps/api/src/adeu_api/paper_pipeline.py`
  I left this alone on purpose. The future live path should go through the existing ADEU URM harness rather than forking a second ad hoc paper-analysis backend.

## 3. Schema family

Implemented in TS at [schema.ts](sandbox:/mnt/data/adeu_repo/adeu-studio-main/apps/web/src/app/papers/semantic-workbench/schema.ts) and mirrored in JSON Schema at [paper_semantic_workbench.v1.json](sandbox:/mnt/data/adeu_repo/adeu-studio-main/packages/adeu_core_ir/schema/paper_semantic_workbench.v1.json) and [paper_semantic_worker_request.v1.json](sandbox:/mnt/data/adeu_repo/adeu-studio-main/packages/adeu_core_ir/schema/paper_semantic_worker_request.v1.json).

Core family:

* `paper_claim_source@1`
  The authoritative source artifact. Holds title, authors, year, artifact kind, and source text.

* `paper_claim_span@1`
  Character-offset anchoring back into the source text.

* `odeu_lane_fragment@1`
  A lane-local semantic fragment with:

  * `lane: O | E | D | U`
  * `source_kind: explicit | inferred`
  * `status: explicit | inferred | contested | underdetermined | missing`
  * `confidence`
  * `warrant`
  * links to spans, bridges, diagnostics

* `odeu_claim_decomposition@1`
  A claim node with:

  * span anchors,
  * recursive parent/subclaim structure,
  * lane fragment ids,
  * confidence, explicitness, and claim-level status.

* `odeu_inference_bridge@1`
  Cross-lane or intra-claim bridges such as:

  * canonical bridge,
  * supporting bridge,
  * projection bridge,
  * missing bridge,
  * contradiction bridge.

* `odeu_semantic_diagnostics@1`
  Diagnostics typed as:

  * contradiction,
  * underdetermination,
  * missing_bridge,
  * overloaded_term,
  * implicit_assumption,
  * u_overreach.

* `odeu_visual_projection@1`
  UI-facing projection metadata:

  * default view,
  * lane order,
  * inline claim order,
  * recommended focus claim,
  * lane node order.

* `paper_semantic_workbench@1`
  The complete typed semantic artifact sent to the workbench.

* `paper_semantic_worker_request@1`
  The live worker request contract with evidence-first / advisory-only posture and bounded decomposition constraints.

Response contract:

* worker returns exactly one `paper_semantic_workbench@1` object.

## 4. Resident Codex processing contract

Implemented in [live-worker.ts](sandbox:/mnt/data/adeu_repo/adeu-studio-main/apps/web/src/app/papers/semantic-workbench/live-worker.ts).

### Tool path

The scaffolded live route uses the existing harness seam:

```json
POST /urm/tools/call
{
  "provider": "codex",
  "role": "copilot",
  "tool_name": "adeu.run_workflow",
  "arguments": {
    "template_id": "adeu.paper.semantic_decomposition.v0",
    "mode": "read_only",
    "inputs": {
      "prompt": "<resident codex contract>"
    }
  }
}
```

### Worker request shape

```json
{
  "schema": "paper_semantic_worker_request@1",
  "request_id": "<uuid>",
  "title": "optional title",
  "source_text": "<abstract or paragraph>",
  "source_kind": "paper.abstract",
  "requested_depth": 1,
  "return_schema": "paper_semantic_workbench@1",
  "operator_posture": {
    "analysis_mode": "evidence-first",
    "authority_mode": "advisory-only",
    "preserve_source_anchor": true
  },
  "constraints": {
    "anchor_explicit_claims_to_source_spans": true,
    "infer_missing_odeu_lanes": true,
    "mark_inferred_and_contested_content": true,
    "include_diagnostics": true,
    "max_top_level_claims": 6,
    "max_subclaims_per_claim": 4
  }
}
```

### Prompt contract

The resident worker is instructed to:

1. preserve the original source text as the authoritative anchor artifact
2. identify top-level claims and anchor every explicit claim to source spans
3. decompose each claim into O / E / D / U lane fragments
4. mark each fragment as explicit or inferred, with confidence and warrant
5. infer missing D or U content when needed, but mark it advisory, inferred, and lower confidence
6. emit diagnostics for contradiction, underdetermination, missing bridge, overloaded term, implicit assumption, and U-overreach
7. recurse one level deeper when `requested_depth = 2`
8. stay bounded to abstract-size semantics and not invent outside evidence
9. return exactly one JSON object matching `paper_semantic_workbench@1`

The page also supports `adeu.list_templates` and `adeu.read_evidence` so the operator can inspect template availability and evidence capture without pretending the live path is already complete.

## 5. Implementation

### Bundle

[Implementation bundle (.zip)](sandbox:/mnt/data/adeu-paper-semantic-workbench-poc.zip)

### Key files

* [Main route: `/papers/semantic-workbench`](sandbox:/mnt/data/adeu_repo/adeu-studio-main/apps/web/src/app/papers/semantic-workbench/page.tsx)
* [Schema family (TS)](sandbox:/mnt/data/adeu_repo/adeu-studio-main/apps/web/src/app/papers/semantic-workbench/schema.ts)
* [Mock/demo processing layer](sandbox:/mnt/data/adeu_repo/adeu-studio-main/apps/web/src/app/papers/semantic-workbench/mock-processing.ts)
* [Live resident-worker scaffold](sandbox:/mnt/data/adeu_repo/adeu-studio-main/apps/web/src/app/papers/semantic-workbench/live-worker.ts)
* [Spatial lane recomposition scene](sandbox:/mnt/data/adeu_repo/adeu-studio-main/apps/web/src/app/papers/semantic-workbench/spatial-lane-scene.tsx)
* [Artifact schema (JSON Schema)](sandbox:/mnt/data/adeu_repo/adeu-studio-main/packages/adeu_core_ir/schema/paper_semantic_workbench.v1.json)
* [Worker request schema (JSON Schema)](sandbox:/mnt/data/adeu_repo/adeu-studio-main/packages/adeu_core_ir/schema/paper_semantic_worker_request.v1.json)
* [Harness template registration](sandbox:/mnt/data/adeu_repo/adeu-studio-main/packages/urm_domain_adeu/src/urm_domain_adeu/adapters.py)

### What the route does now

* lets the operator select from 5 canonical AI papers:

  * Attention Is All You Need
  * BERT
  * GPT-3
  * CLIP
  * AlphaGo
* or paste a new abstract/paragraph into the bottom input panel
* supports depth 1 and depth 2 decomposition
* supports:

  * Artifact view
  * Local decomposition view
  * Spatial lane recomposition view
* keeps source text as anchor with inline claim highlighting
* shows local diagnostics and bridge metadata
* shows a right-side live scaffold inspector with:

  * template metadata
  * harness reachability
  * request preview
  * prompt preview
  * evidence preview
* uses 3D only in the lane recomposition surface

### Visual / morphic behavior

* source-anchored inline spans are persistent
* claim focus morphs across views using shared motion ids
* O/E/D/U lanes are toggleable and structurally encoded
* diagnostics use distinct visual language:

  * red = contradiction / U-overreach
  * hazy / attenuated = underdetermination
  * dashed bridge = missing bridge
  * dotted/inferred styling = advisory inference
* authority posture is always explicit:

  * source anchor = authoritative
  * semantic projection = advisory

### Validation I was able to run

Passed:

* targeted ADEU backend template/discovery test
* targeted ADEU workflow test
* syntax-level TS compile of the new workbench files using stubbed external declarations

Not runnable in this container:

* full web lint / Next smoke run, because `apps/web/node_modules` is not installed here and `eslint` is unavailable in the container for the web app

## 6. What is mocked vs what is live-ready

### Mocked now

* the 5 bundled paper examples use **real canonical papers** but ship as **concise abstract digests / paraphrase artifacts**, not verbatim full abstracts
* curated semantic decompositions for the sample papers are hard-coded as demo outputs
* arbitrary pasted text uses a reusable heuristic mock processor, not a real Codex decomposition

### Live-ready now

* typed request/response contract
* ADEU-native template id:

  * `adeu.paper.semantic_decomposition.v0`
* harness discovery path through:

  * `adeu.list_templates`
  * `adeu.run_workflow`
  * `adeu.read_evidence`
* frontend live scaffold that:

  * builds the request,
  * builds the worker contract,
  * starts a workflow,
  * reads evidence,
  * tries to extract a returned `paper_semantic_workbench@1` artifact

### Not yet live-complete

* the resident worker is not yet guaranteed to emit `paper_semantic_workbench@1` end-to-end
* there is no backend-side validator/coercer yet that normalizes arbitrary worker output into the schema
* there is no persistence layer yet for storing returned semantic artifacts as first-class records

## 7. Next-step integration notes

* Make the resident Codex workflow actually return `paper_semantic_workbench@1` objects in evidence, not just free-form output.
* Add a backend-side schema validation / coercion step so malformed worker output fails visibly instead of silently.
* Decide whether returned semantic artifacts should become durable ADEU artifacts in storage, with ids and provenance.
* Add a small bridge from `paper_pipeline.py` or a neighboring paper-domain surface only if needed for persistence or indexing; keep execution routed through URM.
* Replace the bundled digests with locally pasted source-authored abstracts when reviewing exact wording.
* Add evidence-side provenance for each inferred D/U fragment so the operator can inspect why a projection was made.
* Add selection syncing between artifact spans and spatial nodes at subclaim depth, plus keyboard fast paths for expert inspection.

The result is a real first module: demo-complete, morphic, source-anchored, typed, visually serious, and scaffolded against the repo’s existing ADEU harness rather than a fake side channel.
