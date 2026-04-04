# Draft Stop-Gate Decision vNext+129

Status: proposed gate for `V52-C`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS129.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the live bridge extends the existing `packages/urm_domain_paper` domain pack rather
  than instantiating a new owner surface or laundering ownership into
  `packages/urm_domain_adeu`;
- the slice consumes only released `adeu_paper_semantic_worker_request@1` inputs;
- the live bridge is exposed only as:
  - `paper.run_semantic_decomposition`
  - over the existing URM tool-call surface;
- the new tool is additive and does not replace or reinterpret the existing
  `paper.ingest_text` / `paper.extract_abstract_candidate` / `paper.check_constraints`
  / `paper.emit_artifact` flow or the existing default template
  `paper.abstract.pipeline.v0`;
- capability-lattice / policy action mapping for `paper.run_semantic_decomposition`
  is added explicitly rather than assumed ambiently;
- provider, role, and return schema remain frozen to:
  - `codex`
  - `pipeline_worker`
  - `adeu_paper_semantic_artifact@1`
- emitted bridge results carry bounded bridge status plus `warrant_tag`, `artifact_ref`,
  worker/evidence refs, and request lineage only, and do not embed rendered semantic
  artifact payloads;
- invalid request/template/bridge mismatches fail closed instead of being silently
  repaired;
- bounded regression proves the existing paper-domain tool flow remains unchanged;
- no new `apps/web` fetch wiring, dedicated API route, or prototype workflow overlay
  import ships in this slice;
- targeted bridge/domain tests pass deterministically.

## Do Not Accept If

- `V52-B` browser-local view config becomes authoritative bridge input;
- `paper.semantic_decomposition.v0` silently becomes the new implicit default template
  for the whole paper domain pack;
- bridge ownership is silently laundered into `urm_domain_adeu`;
- the new tool is added without explicit capability/policy mapping coverage;
- the bridge parses or re-renders live semantic artifact payloads in this slice;
- the bridge widens into upload/text-entry/browser trigger work;
- imported overlay workflow/template code is copied into live bridge paths;
- advanced visualization or richer workbench sprawl appears in the same slice.

## Local Gate

- docs-only starter validation:
  - `make arc-start-check ARC=129`
- once implementation starts:
  - run the relevant `urm_domain_paper` and `apps/api` lint/tests for the bounded
    `V52-C` bridge surface.
