# Locked Continuation vNext+83

Status: `V41-A` implementation contract.

## V83 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v41a_practical_analysis_request_contract@1",
  "target_arc": "vNext+83",
  "target_path": "V41-A",
  "target_scope": "practical_analysis_request_and_deterministic_source_set_capture_baseline",
  "analysis_request_schema": "adeu_architecture_analysis_request@1",
  "implementation_package": "adeu_architecture_ir",
  "deferred_artifact": "adeu_architecture_analysis_settlement_frame@1",
  "snapshot_identity_required": true,
  "source_set_ordering_rule": "normalized_repo_relative_path_order",
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "decomposition_doc": "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v23.md"
}
```

## Slice

- Arc label: `vNext+83`
- Family label: `V41-A`
- Scope label: practical analysis request and deterministic `source_set` capture
  baseline

## Objective

Introduce the first concrete practical repo-analysis slice by activating the request
and `source_set` boundary only and freezing the exact repo world that later settlement,
observation, intended compile, alignment, and runner lanes will consume.

This slice establishes the first repo-native practical-analysis substrate for:

- canonical `adeu_architecture_analysis_request@1`;
- deterministic repo-root-relative scope selection;
- explicit inclusion, exclusion, and artifact-kind policy;
- exact `source_set` capture over one bounded repo scope;
- per-item source hashing plus one aggregate `source_set` hash;
- exact maintainer-brief refs, accepted-doc refs, and authority-boundary policy
  pinning.

This slice remains deliberately prior to:

- `adeu_architecture_analysis_settlement_frame@1`;
- `adeu_architecture_observation_frame@1`;
- repo-grounded intended `adeu_architecture_semantic_ir@1` compile;
- `adeu_architecture_alignment_report@1`;
- CLI runner release;
- API or web inspection surfaces.

Its job is to make the request boundary and repo-source universe explicit before any
later slice tries to settle interpretation or compile claims about that world.

## Frozen Implementation Decisions

1. First active package strategy:
   - activate `packages/adeu_architecture_ir` in `vNext+83`;
   - `packages/adeu_architecture_compiler` remains a downstream consumer and may not
     become active for settlement, observation, alignment, or runner behavior in this
     arc.
2. Request artifact strategy:
   - `adeu_architecture_analysis_request@1` is the only newly released artifact family
     in this slice;
   - authoritative JSON schema must live under
     `packages/adeu_architecture_ir/schema/`;
   - mirrored export must live under `spec/`;
   - mirrored export must match the authoritative schema byte-for-byte after
     canonical export.
3. Repo-scope strategy:
   - one request scope must be defined by:
     - one repo-root-relative subtree anchor;
     - optional explicit file additions outside that subtree;
     - explicit exclusion rules;
     - allowed artifact kinds for:
       - `documentation`
       - `source_code`
       - `configuration`
       - `test`
   - free-form scope prose alone is not sufficient in this slice.
4. Snapshot strategy:
   - the first baseline allows exactly:
     - `committed_tree`
     - `materialized_snapshot`
   - ambient live working-tree state may not be treated as deterministic source input
     by itself in this arc;
   - a `committed_tree` request must bind an exact immutable snapshot identity, at
     least:
     - `commit_sha`
     - or `tree_sha`;
   - a `materialized_snapshot` request must bind an explicit snapshot-manifest anchor,
     at least:
     - `snapshot_manifest_ref`
     - or `snapshot_manifest_hash`;
   - a `materialized_snapshot` must be captured explicitly as part of the request
     boundary rather than implied.
5. Source-set hashing strategy:
   - every captured source item must carry a stable repo-root-relative path, artifact
     kind, and content hash;
   - `vNext+83` uses per-item `sha256` plus one aggregate `source_set_hash`;
   - canonical `source_set` ordering is normalized repo-root-relative path order after
     path normalization;
   - duplicate normalized paths are illegal, so no secondary tie-breaker is needed in
     this slice;
   - aggregate hash replay must be deterministic over the same ordered canonical
     source-set payload.
6. Governance-input strategy:
   - the request must bind exact maintainer-brief refs and accepted-doc refs rather
     than relying on free-floating prose alone;
   - each `maintainer_brief_ref` and `accepted_doc_ref` must resolve either:
     - to content inside the frozen `source_set`; or
     - to a separately materialized and hashed brief/document artifact captured by the
       request itself;
   - the request must bind either an exact `authority_boundary_policy` object or an
     exact released policy ref;
   - declared non-goals must be explicit if present.
7. Settlement deferral strategy:
   - the request may reserve a typed hook for a later settlement companion artifact;
   - `vNext+83` may not materialize semantic settlement, entitlement posture, drift
     claims, or impossibility claims as if request capture alone were sufficient.
8. Path decomposition strategy:
   - `vNext+83` is the first concrete `V41-A` arc;
   - settlement, observation, intended compile, alignment, and runner release remain
     available for later concrete `V41` arcs only.

## Required Deliverables

1. New typed practical-analysis request surface:
   - extend `packages/adeu_architecture_ir` with deterministic helpers that
     materialize canonical `adeu_architecture_analysis_request@1`;
   - export schema helpers needed for authoritative and mirrored JSON-schema output;
   - keep settlement, observation, compile, and alignment helpers out of scope.
2. Canonical practical-analysis request artifact:
   - `adeu_architecture_analysis_request@1`
3. Deterministic request entrypoints that:
   - consume one bounded repo scope definition, exact maintainer-brief refs,
     accepted-doc refs, and authority-boundary policy input;
   - capture the exact `source_set` over accepted artifact kinds;
   - materialize `adeu_architecture_analysis_request@1`;
   - fail closed when scope resolution, snapshot mode, per-item hashing, or aggregate
     replay drift is invalid.
4. Top-level schema anchors for `adeu_architecture_analysis_request@1`:
   - `schema`
   - `analysis_request_id`
   - `repo_root_ref`
   - `request_scope`
   - `snapshot_mode`
   - `snapshot_identity`
   - `source_set`
   - `source_set_hash`
   - `maintainer_brief_refs`
   - `accepted_doc_refs`
   - `declared_non_goals`
   - `authority_boundary_policy`
   - `settlement_frame_ref`
   - `notes`
5. Deterministic request / source-set laws that fail closed on at least:
   - any `request_scope` that is expressed only as free prose with no subtree anchor;
   - any source item path that is absolute, escapes repo root, or violates the
     declared scope without an explicit file-addition rule;
   - any duplicate repo-root-relative path in `source_set`;
   - any artifact kind outside the frozen allowed set in this slice;
   - any request using a snapshot mode outside `committed_tree` or
     `materialized_snapshot`;
   - any request missing immutable snapshot identity for the chosen snapshot mode;
   - any source item missing a content hash;
   - any request whose canonical `source_set` ordering is not normalized
     repo-root-relative path order;
   - any aggregate `source_set_hash` replay drift over the same canonical payload;
   - any `maintainer_brief_ref` or `accepted_doc_ref` that resolves neither to the
     frozen `source_set` nor to a separately materialized and hashed captured
     artifact;
   - any request that relies on unbound maintainer prose without exact brief refs;
   - any request that omits policy pinning;
   - any request that claims settlement, drift, or impossibility authority from
     request capture alone.
6. Committed reference fixtures:
   - one accepted request/source-set fixture ladder under
     `apps/api/fixtures/architecture/vnext_plus83/` covering:
     - canonical analysis request
     - canonical source-set capture over one bounded internal repo scope
   - the accepted fixture ladder must prove:
     - deterministic scope replay
     - per-item hash replay
     - aggregate `source_set_hash` replay
     - authority-policy pinning
     - explicit settlement deferral.
7. Python tests covering:
   - schema/model validation for `adeu_architecture_analysis_request@1`;
   - authoritative/mirrored schema export parity;
   - deterministic request and `source_set` replay from the accepted fixture ladder;
   - rejection of unsupported snapshot modes;
   - rejection of path escape, duplicate path, and out-of-scope inclusion drift;
   - rejection of unsupported artifact kinds;
   - rejection of unbound brief input or missing policy pinning;
   - rejection of settlement / drift / impossibility claims inside the request lane.

## Hard Constraints

- `vNext+83` may not activate settlement, observation, alignment, or runner entrypoints
  in `packages/adeu_architecture_compiler`.
- `vNext+83` may not ship:
  - `adeu_architecture_analysis_settlement_frame@1`,
  - `adeu_architecture_observation_frame@1`,
  - repo-grounded intended `adeu_architecture_semantic_ir@1` compile,
  - `adeu_architecture_alignment_report@1`,
  - CLI orchestration of the full loop,
  - API or web inspection routes,
  - automatic repo mutation,
  - direct prompt-to-code generation.
- `vNext+83` may not treat ambient live working-tree state as deterministic request
  input unless that state is first captured as an explicit `materialized_snapshot`.
- `vNext+83` may not mint semantic settlement, drift, or impossibility authority from
  request capture alone.
- `vNext+83` may not weaken the released `V40` root/sibling artifact boundaries.

## PR Shape

- Single integrated PR.

Rationale:

- the request schema, scope resolution, deterministic source-set capture, hashing,
  policy pinning, reference fixtures, and guard tests are tightly coupled and should
  land together so the first practical-analysis boundary freezes as one coherent
  baseline.
