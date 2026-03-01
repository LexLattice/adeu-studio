# Locked Continuation vNext+29 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS28.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS28.md`
- `docs/CONSOLIDATED_TERRITORY_PLAN_v4.md`
- `docs/CONSOLIDATED_TERRITORY_PLAN_v4_FACT_CHECKS.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+28` (`B1`-`B4`) is merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS28.md`.
- Consolidated territory planning sequence remains:
  - `vNext+29 = W3 / Path B` (read-only evidence explorer product surface).
- `vNext+29` is constrained to deterministic read-only evidence UX only:
  - deterministic catalog/list endpoints first
  - explorer UI shell second
  - packet/projection rendering + trust/non-enforcement labeling third
  - parity/regression guard rails and continuity proof fourth

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for default runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS28.md` remain authoritative for baseline semantics.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remains frozen and unchanged.
- Stop-gate schema-family remains unchanged:
  - `stop_gate_metrics@1` only; no schema fork in this arc.
- Stop-gate metric-key policy for this arc is frozen:
  - no new metric keys are introduced in v29.
- Stop-gate metric-cardinality continuity lock is frozen:
  - total stop-gate metric-key count remains `54` in this arc.
- Existing continuity thresholds from prior arcs remain required and unchanged.
- Provider surface continuity remains frozen:
  - no provider expansion or proposer-surface expansion in this arc.
- Non-enforcement/no-mutation continuity remains frozen for v29 evidence-explorer surfaces.
- Bounded behavior-change lock is frozen:
  - `C1` introduces deterministic fail-closed behavior for unsupported evidence family requests on listing endpoints.
  - this is a lock-alignment correction for deterministic catalog authority, not an enforcement release.
- L2 boundaries remain deferred in this arc:
  - no default-on `/urm/worker/run` governance release,
  - no persistent proposer idempotency storage release.
- Closeout observability continuity lock is frozen:
  - v29 closeout must include runtime-observability comparison row against v28 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with four implementation slices (one PR each):

1. `C1` deterministic evidence-explorer catalog/list endpoints
2. `C2` read-only evidence explorer UI shell (existing web stack only)
3. `C3` packet/projection renderers + trust-lane/non-enforcement labeling
4. `C4` parity/regression guard suite for `C1`-`C3` continuity proof

Out-of-scope note:

- formal ODEU implementation lane expansion (planned for v30)
- any L2 boundary releases
- new provider matrix entries or proposer endpoint expansion
- mutation/acknowledgement workflows (dismiss/resolve/approve) for explorer surfaces
- new stop-gate metric keys or stop-gate schema-family forks
- schema-family consolidation across evidence packet families

## C1) Deterministic Evidence-Explorer Catalog/List Endpoints

### Goal

Expose deterministic, read-only catalog/list API surfaces over existing persisted evidence families.

### Scope

- Add fixture-backed list endpoints under `/urm` for evidence-explorer catalog access.
- Keep catalog/list payloads deterministic and sorted for identical persisted inputs.
- Reuse existing evidence family pair/detail endpoints for payload retrieval; list endpoints do not introduce mutation semantics.
- Emit frozen catalog payload schemas for both family index and family detail responses.

### Locks

- Endpoint-set lock is frozen:
  - `GET /urm/evidence-explorer/catalog`
  - `GET /urm/evidence-explorer/catalog/{family}`
- Catalog payload schema lock is frozen:
  - `/catalog` response schema:
    - `schema = "evidence_explorer.catalog@0.1"`
    - required top-level keys:
      - `schema`
      - `families`
    - `families[]` required keys:
      - `family`
      - `identity_mode`
      - `entry_count`
      - `list_ref`
    - `families[].list_ref` required keys:
      - `kind = "endpoint"`
      - `path = "/urm/evidence-explorer/catalog/{family}"`
  - `/catalog/{family}` response schema:
    - `schema = "evidence_explorer.catalog_family@0.1"`
    - required top-level keys:
      - `schema`
      - `family`
      - `identity_mode`
      - `total_entries`
      - `truncated`
      - `entries`
    - optional top-level keys (present only when `truncated = true`):
      - `max_entries_per_family`
      - `returned_entries`
      - `remaining_entries`
    - `entries[]` required keys:
      - `family`
      - `entry_id`
      - `source_text_hash`
      - `core_ir_artifact_id`
      - `concept_artifact_id`
      - `ref`
    - `entries[]` optional key:
      - `artifact_id`
    - `entries[].ref` required keys:
      - `kind = "endpoint"`
      - `path`
- Primary-ref lock is frozen:
  - `entries[].ref.path` points to the primary detail endpoint for that entry identity.
  - for `read_surface`, primary `ref.path` is frozen to:
    - `/urm/core-ir/artifacts/{artifact_id}`
  - lane-projection, lane-report, and integrity endpoints are related links only for `read_surface` and are not emitted as primary `ref.path`.
  - optional related links in explorer renderers must be derived deterministically from frozen entry identity fields.
- Family-set lock is frozen to exactly:
  - `read_surface`
  - `normative_advice`
  - `proof_trust`
  - `semantics_v4_candidate`
  - `extraction_fidelity`
- Cross-family index lock is frozen:
  - `/urm/evidence-explorer/catalog` is the sole v29 cross-family index surface spanning the five frozen families.
  - no additional cross-family aggregator endpoint is introduced in this arc.
- Identity-mode lock is frozen:
  - `read_surface` uses `identity_mode = "artifact_level"`.
  - `normative_advice` uses `identity_mode = "pair_level"`.
  - `proof_trust` uses `identity_mode = "pair_level"`.
  - `semantics_v4_candidate` uses `identity_mode = "pair_level"`.
  - `extraction_fidelity` uses `identity_mode = "pair_level"`.
- Entry identity lock is frozen:
  - `entry_id` is deterministic and family-scoped.
  - artifact-level (`read_surface`) `entry_id` format:
    - `artifact:{artifact_id}`
  - pair-level family `entry_id` format:
    - `pair:{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}`
  - for artifact-level entries where pair fields are not applicable:
    - `concept_artifact_id` is emitted as empty string `""`.
  - for artifact-level entries:
    - `artifact_id` is required.
- Existing-family continuity lock is frozen:
  - `read_surface` maps to existing `/urm/core-ir/artifacts/...` read surfaces from v19.
  - `normative_advice` maps to existing `/urm/normative-advice/...` surfaces from v21.
  - `proof_trust` maps to existing `/urm/proof-trust/...` surfaces from v22.
  - `semantics_v4_candidate` maps to existing `/urm/semantics-v4/...` surfaces from v23.
  - `extraction_fidelity` maps to existing `/urm/extraction-fidelity/...` surfaces from v24.
- Extraction-fidelity boundary lock is frozen:
  - `extraction_fidelity` explorer surfaces are evidence-only diagnostics views.
  - explorer renderers/endpoints may not imply remediation, proposal, or auto-repair semantics for extraction-fidelity entries.
- Catalog source authority lock is frozen:
  - list endpoints in this arc are fixture-backed over persisted catalogs/artifacts already in repository.
  - filesystem globs, DB discovery scans, and undeclared directories are out-of-scope.
- Catalog completeness-scope lock is frozen:
  - `/catalog` completeness is defined as the five frozen families as represented by v29 fixture-backed catalog sources.
  - `/catalog` is not a repository-wide discovery endpoint and may not scan arbitrary directories/artifacts.
- Deterministic pre-cap filter lock is frozen:
  - `/catalog/{family}` supports optional deterministic filter query params:
    - `source_text_hash_prefix`
    - `core_ir_artifact_id_prefix`
    - `concept_artifact_id_prefix`
  - filter behavior is case-sensitive prefix match on corresponding entry fields.
  - dual-identity filter behavior is frozen:
    - for `identity_mode = "artifact_level"`, `concept_artifact_id` is always `""`.
    - non-empty `concept_artifact_id_prefix` deterministically excludes artifact-level entries.
  - filter application order is frozen:
    - apply filters first,
    - then apply deterministic ordering,
    - then apply volume cap/truncation.
- Deterministic ordering lock is frozen:
  - `/catalog` family entries are emitted in lexicographic order of `family`.
  - `/catalog/{family}` entries are emitted in lexicographic order by deterministic identity tuple:
    - `source_text_hash`, `core_ir_artifact_id`, `concept_artifact_id`, `artifact_id_or_empty`.
- Ordering normalization lock is frozen:
  - `artifact_id_or_empty = artifact_id` when `artifact_id` is present.
  - `artifact_id_or_empty = ""` when `artifact_id` is absent.
- Artifact-level identity invariant lock is frozen:
  - for `identity_mode = "artifact_level"` entries:
    - `artifact_id` must be present.
    - `core_ir_artifact_id` must equal `artifact_id`.
- Unsupported-family fail-closed lock is frozen:
  - unsupported `{family}` values fail deterministically before payload emission.
  - unsupported `{family}` is request-invalid, not artifact-not-found:
    - HTTP status `400`
    - reused code: `URM_ADEU_READ_SURFACE_REQUEST_INVALID`
  - reason token is frozen:
    - `reason = "UNSUPPORTED_FAMILY"`.
- Known-family empty-result lock is frozen:
  - when `{family}` is valid, family backing sources are present/valid, and no entries are available, response is deterministic success:
    - HTTP status `200`
    - `entries = []`
    - `total_entries = 0`
    - `truncated = false`
- Error-code reuse lock is frozen:
  - no new `URM_ADEU_EVIDENCE_EXPLORER_*` error-code family is introduced in this arc.
  - catalog/detail flows reuse existing family-domain codes only:
    - `URM_ADEU_READ_SURFACE_*`
    - `URM_ADEU_NORMATIVE_ADVICE_*`
    - `URM_ADEU_TRUST_INVARIANT_*`
    - `URM_ADEU_SEMANTICS_V4_*`
    - `URM_ADEU_EXTRACTION_FIDELITY_*`
- Family-domain error-dispatch lock is frozen:
  - known-family error envelopes must use that family's domain code namespace only.
  - cross-family fallback to unrelated domain namespaces is forbidden.
  - mapping is frozen:
    - `read_surface -> URM_ADEU_READ_SURFACE_*`
    - `normative_advice -> URM_ADEU_NORMATIVE_ADVICE_*`
    - `proof_trust -> URM_ADEU_TRUST_INVARIANT_*`
    - `semantics_v4_candidate -> URM_ADEU_SEMANTICS_V4_*`
    - `extraction_fidelity -> URM_ADEU_EXTRACTION_FIDELITY_*`
- HTTP status semantics lock is frozen:
  - unknown `{family}`:
    - HTTP `400` + reused `*_REQUEST_INVALID`.
  - known `{family}` with zero available entries:
    - HTTP `200` + deterministic empty `entries`.
  - known `{family}` with missing required backing artifacts/catalog inputs:
    - HTTP `404` + reused `*_ARTIFACT_NOT_FOUND`.
  - known `{family}` with schema/shape/linkage-invalid backing payloads:
    - HTTP `400` + reused `*_PAYLOAD_INVALID`.
- Catalog volume lock is frozen:
  - `max_entries_per_family = 1000`
  - when filtered raw entries exceed cap:
    - apply deterministic ordering over the filtered set first,
    - emit the first `1000`,
    - set `truncated = true`,
    - keep `total_entries` as pre-truncation count.
- Truncation-signaling lock is frozen:
  - when `truncated = true`, response must include deterministic truncation metadata:
    - `max_entries_per_family`
    - `returned_entries`
    - `remaining_entries`
  - truncation metadata fields are omitted when `truncated = false`.
- Mutation boundary lock is frozen:
  - `C1` handlers are read-only and may not write canonical artifacts, stop-gate artifacts, or report artifacts.

### Acceptance

- Deterministic reruns produce byte-identical list payloads for identical persisted inputs.
- Unsupported family requests fail closed deterministically.
- Existing pair/detail endpoints remain behavior-compatible and unchanged for identical inputs.
- Catalog payloads validate against frozen `evidence_explorer.catalog@0.1` and `evidence_explorer.catalog_family@0.1` schemas.
- Deterministic pre-cap filters are applied consistently and reproducibly across reruns.
- Family-domain error dispatch behavior is deterministic and consistent with frozen family->code mapping.
- Primary `ref.path` values are deterministic and map to frozen primary-detail endpoint semantics.

## C2) Read-Only Evidence Explorer UI Shell

### Goal

Ship a deterministic, read-only evidence explorer shell over existing evidence families without changing backend enforcement behavior.

### Scope

- Add an explorer route in the existing `apps/web` stack consuming `C1` list endpoints.
- Provide deterministic family navigation, filtering, and stable empty/error states.
- Keep UI delivery additive and compatible with current app structure.

### Locks

- UI stack continuity lock is frozen:
  - implementation must use existing web toolchain and dependency set; no new frontend build-system dependency is introduced.
- Read-only interaction lock is frozen:
  - explorer shell may issue `GET` requests only.
  - no `POST`, `PUT`, `PATCH`, or `DELETE` actions are introduced by this surface.
- No-provider-call continuity lock is frozen:
  - explorer flows may not trigger provider/proposer dispatch.
  - explorer flows may not call `/urm/core-ir/propose`.
- Deterministic state lock is frozen:
  - default family selection and rendered list ordering must be deterministic from `C1` payload ordering.
  - deterministic empty/error states are required for unsupported family and missing-data cases.
- Deep-link lock is frozen:
  - selected family and selected entry state must be represented in URL state deterministically.
  - opening a deep-link in a fresh browser session must restore the same family/entry selection state for identical payload inputs.
- Deep-link truncation/fallback lock is frozen:
  - when a deep-linked entry is outside the current list window because of filters/truncation:
    - UI must still attempt primary-detail fetch via deterministic `ref.path` derivation from selected `family` + decoded `entry_id`.
    - if detail fetch succeeds, render entry and show deterministic `outside_current_list_window` state.
    - if detail fetch returns artifact-not-found, show deterministic `entry_unavailable` state.
- Route-id encoding lock is frozen:
  - UI routes may not embed raw `entry_id` directly in path segments.
  - when `entry_id` is represented in URL path or hash, use base64url encoding over UTF-8 bytes, no padding.
  - decode/encode roundtrip must be lossless for all frozen family entry-id formats.
- UI determinism-definition lock is frozen:
  - determinism in this arc is defined over data ordering and view-state decisions only:
    - default route/family selection
    - grouping/sorting
    - empty/error state selection
    - rendered item ordering
  - visual layout timing and screenshot-pixel identity are out-of-scope.
- No-mutation continuity lock is frozen:
  - client interactions in this arc cannot mutate persisted evidence or policy state.

### Acceptance

- Explorer shell renders deterministically from fixture-backed API responses.
- No write/mutation network calls are emitted by explorer interactions.
- Existing non-explorer product surfaces continue to behave unchanged.
- Deep-link reload reproduces identical family/entry selection state for identical payload inputs.
- Deep-link behavior under filtering/truncation follows frozen deterministic fallback rules.

## C3) Packet/Projection Renderers + Trust/Non-Enforcement Labels

### Goal

Provide deterministic packet/projection rendering for existing evidence families with explicit trust-lane and non-enforcement messaging.

### Scope

- Add renderer components/views for the five frozen explorer families.
- Render existing packet/projection payloads only; do not redefine evidence-family contracts.
- Display explicit trust-lane and non-enforcement labels for each rendered family.

### Locks

- Renderer family coverage lock is frozen:
  - renderers must exist for all frozen `C1` families:
    - `read_surface`
    - `normative_advice`
    - `proof_trust`
    - `semantics_v4_candidate`
    - `extraction_fidelity`
- Trust-lane labeling lock is frozen:
  - renderer surfaces must display explicit trust-lane labels:
    - `read_surface -> mapping_trust`
    - `normative_advice -> mapping_trust`
    - `proof_trust -> proof_trust`
    - `semantics_v4_candidate -> solver_trust`
    - `extraction_fidelity -> mapping_trust`
- Trust-label provenance lock is frozen:
  - displayed trust label is derived only from frozen family-name mapping.
  - labels may not be inferred from payload issue counts, severity mixes, or other runtime heuristics.
- Trust-label surface-attribute lock is frozen:
  - trust label is a surface-family attribute, not an inferred artifact property.
  - renderers may not upgrade/downgrade trust labels based on payload content.
- Non-enforcement label lock is frozen:
  - each rendered family surface must display deterministic non-enforcement text:
    - `Evidence-only surface; no automatic policy enforcement or mutation is performed.`
- Payload contract continuity lock is frozen:
  - `C3` renderers consume existing family payload contracts and may not fork/add schema-family variants.
- Identity-mode renderer lock is frozen:
  - renderer behavior is deterministic for both frozen identity modes:
    - `artifact_level` entries render without requiring non-empty `concept_artifact_id`.
    - `pair_level` entries require and render full pair identity fields.
  - renderer branching may not reinterpret `entry_id` formats beyond frozen `C1` definitions.
- Deterministic render ordering lock is frozen:
  - list blocks and issue/item groups rendered from family payloads must preserve deterministic ordering from upstream payload contracts.

### Acceptance

- All frozen families render with deterministic ordering and stable labels.
- Trust-lane labels and non-enforcement label are present on every family surface.
- Rendering differs only when underlying persisted evidence payloads differ.
- Artifact-level and pair-level entry renderers both pass deterministic identity rendering checks.

## C4) Parity and Regression Guard Suite

### Goal

Prove `C1`-`C3` explorer activation is behavior-preserving, deterministic, and non-enforcing.

### Scope

- Add regression/parity coverage for:
  - catalog/list endpoint deterministic ordering
  - explorer read-only behavior (no provider/no mutation)
  - renderer coverage and labeling continuity

### Locks

- No-new-metric-keys lock is frozen:
  - v29 test additions may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v28 continuity metrics remain at frozen required values.
- Fail-closed regression lock is frozen:
  - detected canonical-hash drift in locked baseline comparisons fails CI and blocks merge.
- Provider/mutation guard lock is frozen:
  - tests fail closed if explorer routes trigger provider dispatch or write side effects.
- No-write-verb guard lock is frozen:
  - explorer surface tests fail closed if UI/API flows issue `POST`, `PUT`, `PATCH`, or `DELETE` requests.
- Static coverage lock is frozen:
  - tests fail closed when any frozen `C1` family is missing renderer or required labels.
- Deterministic ordering guard lock is frozen:
  - tests fail closed when endpoint or renderer ordering diverges from frozen deterministic ordering rules.
- Family-availability guard lock is frozen:
  - CI must probe all frozen family detail/projection surfaces and fail closed when any mapped family surface is unavailable.
- Explorer fixture-snapshot guard lock is frozen:
  - guard suite includes deterministic pre/post snapshot checks over explorer fixture-backed catalogs/artifacts and fails closed on mutation.

### Acceptance

- Guard suites pass deterministically across reruns.
- Locked continuity metrics and parity evidence remain unchanged.
- No-provider and no-mutation guard tests pass for explorer flows.

## Stop-Gate Impact (v29)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity metrics remain required.
- Listing/explorer surfaces are convenience read surfaces in this arc and do not introduce new stop-gate metric families.
- v29 closeout must include runtime-observability comparison row against v28 baseline.
- Runtime-observability closeout placement lock is frozen:
  - v29 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md` inside a machine-checkable JSON block.

## Error/Exit Policy (v29)

- No new URM error-code family is planned in this arc.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `api: add deterministic evidence-explorer catalog/list endpoints over frozen families`
2. `web: add read-only evidence explorer shell with deterministic navigation`
3. `web/api: add packet/projection renderers with trust-lane and non-enforcement labels`
4. `tests: add vnext+29 deterministic ordering and no-provider/no-mutation guard suite`

## Intermediate Preconditions (for v29 start)

1. v28 lock/closeout artifacts remain authoritative and unchanged.
2. v28 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS28.md`
3. Existing frozen evidence family surfaces remain available:
   - v19 read-surface endpoints
   - v21 normative-advice endpoints
   - v22 proof-trust endpoints
   - v23 semantics-v4 endpoints
   - v24 extraction-fidelity endpoints
   - all five family surfaces above must be callable in CI at v29 start.
4. No L2 release is introduced in this arc.

## Exit Criteria (Draft)

- `C1` through `C4` merged with green CI.
- No new stop-gate metric keys introduced.
- Existing evidence-family payload contracts remain unchanged.
- Explorer catalog/list and renderer outputs are deterministic for identical persisted inputs.
- Existing continuity thresholds remain at required values.
- v29 closeout evidence includes runtime-observability comparison row against v28 baseline.
- No solver semantics contract delta and no trust-lane regression introduced.
