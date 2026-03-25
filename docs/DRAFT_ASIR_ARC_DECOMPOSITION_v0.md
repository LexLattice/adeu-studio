# Draft ASIR Arc Decomposition v0

Status: working decomposition draft after `vNext+77` closeout, `vNext+78`
closeout, `vNext+79` closeout, `vNext+80` closeout, `vNext+81` closeout, and
`docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`.

This document is an intermediate planning artifact between:

- the ASIR architecture constitution; and
- the next-family selection / first-lock docs.

It exists to prevent a direct jump from "module architecture is defined" to "one large
implementation arc tries to land too much at once."

This is not a lock doc. It does not authorize runtime behavior, schema release, or
implementation by itself.

## Purpose

- compile the ASIR architecture document into repo-sized implementation slices;
- keep each ASIR slice closer in scale to prior ADEU arc families rather than to a
  one-shot subsystem rollout;
- make the family order explicit before the first ASIR lock is drafted;
- separate baseline-required slices from compatible-later slices;
- keep the Lean formal lane visible as a bounded proof-mirror sidecar rather than a
  hidden dependency for the full compiler.

## Inputs

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v17.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v18.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v19.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v20.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v21.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v22.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS77.md`
- `docs/ASSESSMENT_vNEXT_PLUS77_EDGES.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS78.md`
- `docs/ASSESSMENT_vNEXT_PLUS78_EDGES.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS79.md`
- `docs/ASSESSMENT_vNEXT_PLUS79_EDGES.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS80.md`
- `docs/ASSESSMENT_vNEXT_PLUS80_EDGES.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS81.md`
- `docs/ASSESSMENT_vNEXT_PLUS81_EDGES.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/formal/asir/ASIR_FORMAL_KERNEL.md`
- `docs/formal/asir/ASIRKernelHybrid.md`
- `docs/formal/asir/ASIRKernelGating.md`
- `docs/formal/asir/ASIRKernelConnector.md`

## Decomposition Thesis

ASIR already has an architecture-level ladder in the main spec:

- semantic root and fixtures;
- deterministic compiler baseline;
- bounded hybrid lane;
- core IR lowering;
- first UX lowering;
- evidence and stop-gate integration.

That ladder is conceptually right, but it is still architecture-shaped. This document
recompiles it into implementation slices shaped more like prior ADEU path families:

- one narrow contract seam per slice;
- one explicit set of artifacts per slice;
- one bounded validator/evidence surface per slice;
- no mixing of semantic root, hybrid law, projection lowering, and UX workbench concerns
  inside the same first lock.

## Baseline Agreement

- `vNext+76` (`V39-E`) is closed on `main`.
- The bounded `V39` family is complete at its intended baseline.
- `vNext+77` (`V40-A`) is closed on `main` at its bounded baseline.
- `vNext+78` (`V40-B`) is now closed on `main` at its bounded baseline.
- `vNext+79` (`V40-C`) is now closed on `main` at its bounded baseline.
- `vNext+80` (`V40-D`) is now closed on `main` at its bounded baseline.
- `vNext+81` (`V40-E`) is now closed on `main` at its bounded baseline.
- The ASIR root-family substrate is released under `packages/adeu_architecture_ir`.
- The deterministic ASIR conformance substrate is released under
  `packages/adeu_architecture_compiler`.
- The bounded hybrid checkpoint substrate is released under
  `packages/adeu_architecture_compiler`.
- The narrow `adeu_core_ir` lowering substrate is now released under
  `packages/adeu_architecture_compiler`.
- The next safe step is family-complete evidence and release integration rather than
  reopening the released semantic-root, deterministic-compiler, hybrid,
  `adeu_core_ir`, or `ux_domain_packet@1` boundary.
- The Lean formal lane is useful but should remain sidecar-only unless a later lock
  explicitly promotes it into a required release surface.

## Machine-Checkable Decomposition Baseline

```json
{
  "schema": "asir_arc_decomposition@1",
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "baseline_arc": "vNext+81",
  "closed_path_family": "V39",
  "closed_paths": [
    "V39-A",
    "V39-B",
    "V39-C",
    "V39-D",
    "V39-E"
  ],
  "next_path_family": "V40",
  "closed_current_family_paths": [
    "V40-A",
    "V40-B",
    "V40-C",
    "V40-D",
    "V40-E"
  ],
  "default_next_arc_candidate": "V40-F",
  "default_next_concrete_arc_candidate": "vNext+82",
  "v40_path_count": 6,
  "v40_default_arc_span": {
    "from": "vNext+82",
    "to": "vNext+86"
  },
  "v40_paths_may_span_multiple_arcs": true,
  "planned_family_packages": [
    "packages/adeu_architecture_ir",
    "packages/adeu_architecture_compiler"
  ],
  "v40a_active_packages": [
    "packages/adeu_architecture_ir"
  ],
  "deferred_package_activation": {
    "packages/adeu_architecture_compiler": "V40-B_or_later"
  },
  "sidecar_formal_surfaces": [
    "docs/formal/asir/ASIR_FORMAL_KERNEL.md",
    "docs/formal/asir/ASIRKernelHybrid.md",
    "docs/formal/asir/ASIRKernelGating.md",
    "docs/formal/asir/ASIRKernelConnector.md",
    "RequestProject/"
  ],
  "formal_kernel_mode": "proof_mirror_sidecar_only",
  "first_family_projection_minimal_contract": [
    "adeu_core_ir"
  ],
  "compatible_later_projection_targets": [
    "ux_domain_packet",
    "ux_morph_ir"
  ],
  "forbidden_first_lock_widenings": [
    "api_or_web_workbench_release",
    "direct_prompt_to_code_generation",
    "unbounded_oracle_or_multi_round_hybrid",
    "packages_adeu_lean_in_place_upgrade",
    "formal_kernel_required_for_full_family_validity"
  ]
}
```

## Family Scale Rules

To stay aligned with prior ADEU implementation families, `V40` should obey these
decomposition rules:

- each path introduces one primary seam, not several unrelated ones;
- each path may span one or more concrete `vNext+` arcs, and PR granularity sits below
  that arc boundary;
- each path should usually fit into one narrow lock plus one bounded PR split;
- no path should mix semantic-root introduction, hybrid checkpoint release, and UX
  lowering in one slice;
- no path should require API or web integration merely to prove a lower-level contract;
- closeout evidence should remain additive to the current stop-gate schema family.

## Package Activation Timing

- `packages/adeu_architecture_ir` is the first active package and belongs to `V40-A`.
- `packages/adeu_architecture_compiler` is planned at the family level but should remain
  reserved until `V40-B` or later.
- `V40-A` may define package-boundary seams that the compiler package will consume
  later, but it should not activate deterministic compiler entrypoints in the first
  concrete arc.

## Concrete Arc Granularity

`V40` path labels are not assumed to map one-to-one onto concrete `vNext+` arcs.

The current recommended concrete split is:

- `vNext+77`
  - closed first concrete `V40-A` arc:
    root schemas, models, exports, canonicalization/hashing, reference fixtures,
    validator tests, and boundary exclusions
- `vNext+78`
  - closed first concrete `V40-B` arc:
    compiler package activation, conformance-report schema/export baseline,
    deterministic assembly/integrity passes, blocked/ready gating, reference fixtures,
    and validator tests
- `vNext+79`
  - closed first concrete `V40-C` arc:
    hybrid schema/model/export baseline, deterministic checkpoint classifier,
    typed oracle request/resolution/checkpoint-trace surfaces, replay identity,
    one-round oracle law, bounded `ir_delta` proposal law, committed fixtures, and
    validator tests
- `vNext+80`
  - closed first concrete `V40-D` arc:
    projection bundle/manifest schema/model/export baseline, deterministic
    `adeu_core_ir` lowering, manifest/source-lineage honesty, blocked-vs-ready
    projection checks, committed fixtures, and validator tests
- `vNext+81`
  - closed first concrete `V40-E` arc:
    ASIR-to-`ux_domain_packet@1` lowering, reuse of the existing UX governance
    target-family schema under `packages/adeu_core_ir`, frozen approved-profile /
    authority-boundary compatibility, committed fixtures, and validator tests
- `vNext+82`
  - default first concrete `V40-F` arc:
    family-complete `V40-A` through `V40-E` evidence integration, canonical family
    release evidence, explicit released-vs-deferred surface posture, stop-gate
    continuity assertions, and bounded release-note wiring without stop-gate schema
    drift
- `vNext+83`
  - optional follow-on `V40-F` hardening only if deeper release-summary diagnostics,
    stricter family evidence guards, or broader release-note packaging remain
    intentionally deferred from `vNext+82`

Later `V40` paths may also take one or more concrete arcs when that keeps each lock
comparable to earlier ADEU slices.

## Recommended `V40` Slice Ladder

| Path | Theme | Primary output | Baseline role |
|---|---|---|---|
| `V40-A` | semantic root baseline | ASIR root artifacts and schemas | required |
| `V40-B` | deterministic compiler baseline | assembly + integrity + conformance | required |
| `V40-C` | bounded hybrid ambiguity lane | checkpoint/oracle/trace artifacts | required |
| `V40-D` | core IR lowering baseline | `adeu_core_ir` projection | required |
| `V40-E` | first UX lowering baseline | `ux_domain_packet` / `ux_morph_ir` compatibility | compatible-later |
| `V40-F` | evidence and release integration | closeout evidence and stop-gate continuity | required |

## Path V40-A: Semantic Root and Schema Baseline

Lock class: `L1`

Goal:

- release the ASIR semantic root as a canonical typed artifact family before compiler,
  hybrid, or projection widening.

Scope:

- canonical `adeu_architecture_intent_packet@1`;
- canonical `adeu_architecture_ontology_frame@1`;
- canonical `adeu_architecture_boundary_graph@1`;
- canonical `adeu_architecture_world_hypothesis@1`;
- canonical `adeu_architecture_semantic_ir@1`;
- activate `packages/adeu_architecture_ir` only;
- canonicalization and hashing rules for the root family;
- authoritative and mirrored schema exports;
- one committed reference fixture set;
- fail-closed root-boundary enforcement:
  - no projection state in the root,
  - no checkpoint-trace state in the root,
  - no conformance summary in the root.

Locks:

- `packages/adeu_architecture_compiler` remains reserved and inactive in this path;
- no deterministic compiler pass release yet;
- no hybrid checkpoint/oracle lane yet;
- no `adeu_core_ir` lowering yet;
- no UX lowering yet;
- no API or web integration yet;
- Lean proof mirrors may accompany frozen finite vocabularies but are not required for
  slice validity.

Acceptance:

- the semantic root validates as a clean meaning artifact;
- reference fixtures prove root/sibling separation explicitly;
- schema exports are authoritative and mirrored;
- canonical payload hashing is deterministic.

Expected PR shape:

- default first concrete arc: single integrated PR

Rationale:

- the `vNext+77` package surface, root-family schemas, canonicalization/hashing,
  reference fixture ladder, and validator tests are tightly coupled;
- a later concrete `V40-A` hardening slice may still exist if richer coverage is
  intentionally deferred, but the first concrete lock does not assume a mandatory
  two-PR split.

## Path V40-B: Deterministic Assembly and Integrity Baseline

Lock class: `L1`

Goal:

- release deterministic ASIR assembly and integrity checking without yet widening into
  hybrid execution or projection families.

Scope:

- compile entrypoint for source normalization and ASIR assembly;
- section-local validation passes for ontology, epistemics, deontics, and utility;
- whole-ASIR integrity pass;
- validator check-id families;
- canonical `adeu_architecture_conformance_report@1` baseline;
- consumed-root replay lineage in the conformance report;
- explicit required-vs-advisory check-result posture;
- static deterministic human-escalation lineage only;
- deterministic pre-projection conformance plus blocked/ready gating.

Locks:

- `V40-B` is the first lawful point where `packages/adeu_architecture_compiler` may
  become active;
- no oracle request/resolution artifacts yet;
- no checkpoint trace yet;
- no projection bundle or projection manifest yet;
- no lowerings beyond internal draft validation;
- no API or web inspection surface yet.

Acceptance:

- deterministic compiler can assemble canonical ASIR from bounded inputs;
- whole-ASIR integrity pass enforces cross-section laws;
- conformance report remains downstream of the root and does not collapse back into it;
- `ASIR-P-xxx` in this path means pre-projection readiness honesty only rather than
  manifest-integrity checking.

Expected PR shape:

- PR1: compiler pass skeleton + validators
- PR2: conformance-report fixtures and deterministic tests

## Path V40-C: Bounded Hybrid Ambiguity Baseline

Lock class: `L1`

Goal:

- release the ASIR hybrid ambiguity lane using the already-proven `v76` bounded hybrid law.

Scope:

- consume released `V40-A` semantic-root artifacts and released `V40-B` conformance
  outputs rather than free-floating checkpoint fixtures;
- canonical `adeu_architecture_oracle_request@1`;
- canonical `adeu_architecture_oracle_resolution@1`;
- canonical `adeu_architecture_checkpoint_trace@1`;
- canonical `adeu_architecture_ir_delta@1`;
- deterministic checkpoint classifier;
- frozen `resolution_route -> checkpoint_class` law;
- frozen `resolution_state -> final_adjudication` law;
- exact replay identity and one-round oracle rule;
- advisory-only oracle boundary and fail-closed escalation behavior;
- explicit preservation of deterministic required-check authority from `V40-B`.

Locks:

- no checkpoint fixtures may bypass the released root and deterministic assembly
  surfaces once those surfaces exist;
- no failed required deterministic check may be reinterpreted as an oracle-repair
  checkpoint in the first baseline;
- no direct repo mutation;
- no patch payload emission;
- no multi-round oracle loop;
- no API or web human-review workbench release in the first baseline.

Acceptance:

- hybrid checkpoints bind back to released semantic-root and conformance surfaces;
- deterministic/oracle/human checkpoint branches replay cleanly;
- final adjudication remains deterministic;
- oracle output cannot mint authority, scope, or capability.

Expected PR shape:

- single integrated PR

## Path V40-D: Core IR Lowering Baseline

Lock class: `L1`

Goal:

- prove one narrow downstream lowering from ASIR into repo-native shared integrity space.

Scope:

- canonical `adeu_architecture_projection_bundle@1`;
- canonical `adeu_architecture_projection_manifest@1`;
- consume released `V40-B` conformance outputs and `V40-C` checkpoint/adjudication
  state before lowering;
- lowering from ASIR into `adeu_core_ir@0.1` only;
- projection honesty checks;
- blocked-by-ambiguity and source-lineage manifest checks.

Locks:

- no lowering directly from an undervalidated semantic root;
- `adeu_core_ir` is the only required target family in this slice;
- no UX lowering yet;
- no API/workflow/event/test-contract families yet.

Acceptance:

- one canonical ASIR fixture lowers deterministically into `adeu_core_ir@0.1`;
- manifest lineage is inspectable and honest;
- released readiness/blocking state governs whether lowering is allowed;
- unresolved blocking ambiguity cannot be misreported as ready projection;
- blocked projection units carry empty emitted-output refs in the first baseline.

Expected PR shape:

- single integrated PR

## Path V40-E: First UX Lowering Baseline

Lock class: `L0`

Goal:

- prove ASIR compatibility with the existing UX IR/compiler family without widening into
  generic application generation.

Scope:

- lowering from released ASIR / `V40-D` projection lineage into `ux_domain_packet@1`
  only in the first concrete `V40-E` arc;
- optional follow-on lowering into `ux_morph_ir@1` only after the first concrete
  `V40-E` baseline is stable;
- explicit compatibility checks against the released UX governance family under
  `packages/adeu_core_ir`, including the frozen approved-profile and authority-boundary
  posture;
- exact one-to-one binding from each emitted UX packet to one released ready
  `projection_id` in the first concrete `V40-E` arc;
- continued preservation of no direct brief-to-UI-code without IR.

Locks:

- this slice is compatible-later rather than first-family blocking;
- `V40-E` is non-blocking for first-family validity;
- the first concrete `V40-E` arc may not emit `ux_morph_ir@1`;
- no direct React tree generation;
- no broad UI compiler export or workbench release by default.

Acceptance:

- ASIR can serve as a lawful upstream semantic and projection source for emitted
  `ux_domain_packet@1`;
- emitted `ux_domain_packet@1` remains typed, approved-profile-bound, and intermediate
  rather than prompt-to-surface;
- blocked projection units emit zero UX packets and ready units emit at most one UX
  packet in the first baseline;
- `V40-D` projection honesty remains preserved while the target family widens from
  `adeu_core_ir@0.1` to one existing UX IR surface only.

Expected PR shape:

- single integrated PR

## Path V40-F: Evidence and Release Integration

Lock class: `L1`

Goal:

- integrate the ASIR family into repo-native closeout, evidence, and stop-gate continuity
  without widening the stop-gate schema family.

Scope:

- ASIR family evidence inputs and closeout artifacts;
- one canonical family-level evidence artifact that binds the released `V40-A` through
  `V40-E` surfaces and their closeout evidence together;
- authoritative and mirrored schema exports for that family evidence artifact;
- stop-gate continuity assertions with no schema-family or metric-key drift;
- closeout evidence for schema export parity, deterministic compilation, hybrid replay,
  projection honesty, and first UX lowering where applicable;
- family-complete release note posture for the first ASIR ladder, including explicit
  released-vs-deferred surface marking.

Locks:

- no stop-gate schema-family fork;
- no implicit metric-key expansion;
- no broader runtime observability claims than the implementation actually proves;
- runtime-observability deltas remain informational only and may not by themselves
  change shipped/deferred surface status or block family evidence materialization;
- no deferred `ux_morph_ir@1`, rendered-surface export, workbench/API route, or formal
  sidecar surface may be misreported as a released `V40` family surface.

Acceptance:

- closeout artifacts truthfully represent the landed ASIR slice set;
- stop-gate continuity is preserved;
- remaining deferred surfaces are explicit;
- one canonical family evidence artifact binds the shipped `V40-A` through `V40-E`
  lane without overclaiming any unreleased surface;
- per-path evidence closure is exact for `V40-A` through `V40-E` rather than only
  list-shaped.

Expected PR shape:

- single integrated PR

## Formal Proof-Mirror Sidecar

The Lean kernels should not become an unspoken prerequisite for all `V40` slices.

The correct decomposition is:

- `docs/formal/asir/ASIR_FORMAL_KERNEL.md` aligns most naturally with `V40-A`;
- `docs/formal/asir/ASIRKernelHybrid.md` aligns most naturally with `V40-C`;
- `docs/formal/asir/ASIRKernelGating.md` aligns most naturally with `V40-B` and `V40-D`;
- `docs/formal/asir/ASIRKernelConnector.md` aligns most naturally with the
  `V40-C` / `V40-D` boundary.

An initial pipeline-composition kernel now exists in the Aristotle sidecar lane, but
current review shows that it still sits below the full released `V40-C` artifact
contract.

The next proof-sidecar addition should therefore be a bounded artifact-law catch-up
module covering:

- targeted checkpoint application rather than blanket list-wide adjudication;
- `resolution_state -> final_adjudication` law;
- oracle-ref nullability by checkpoint class;
- delta provenance via `source_resolution_id`;
- preservation of `V40-B` deterministic-failure boundaries.

Sidecar rules:

- formal kernels may prove already-frozen finite laws;
- they must not silently redefine the architecture contract;
- they do not certify downstream Python or JSON mirrors unless the mirroring path is
  exact and trusted;
- they should remain optional until a later lock explicitly promotes them.

## Default Order

1. `V40-A`
2. `V40-B`
3. `V40-C`
4. `V40-D`
5. `V40-E`
6. `V40-F`

## Non-Goals for This Decomposition

- selecting implementation details inside a future lock;
- authorizing API or web workbench release by implication;
- collapsing the formal Lean sidecar into the mainline compiler authority;
- turning the ASIR family into one oversized umbrella arc.
