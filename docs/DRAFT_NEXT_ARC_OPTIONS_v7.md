# Draft Next Arc Options v7 (Post vNext+43, Agent Harness Baseline)

This document defines the post-`vNext+43` planning baseline for an ADEU-governed agentic development harness.

Status: active planning draft (`V32-A` through `V32-F` closed; next family selection in progress).

Goal:

- move from prompt-first agent guidance to a typed, deterministic, ADEU-vetted harness where prompts are rendered outputs of authoritative contracts;
- prioritize Codex SDK path integration in ADEU first;
- keep the harness portable as a standalone ADEU-kernel-based module, independent of domain modules (`legal`, `articles`, etc.).

This is a planning document only. It is not a lock doc and does not authorize runtime behavior changes.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS43.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS43.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

## Baseline Agreement (Current Ground Truth)

- Baseline implementation is `vNext+43` (`V32-F`) on `main`.
- `V32-A` through `V32-F` are closed.
- `stop_gate_metrics@1` remains the active stop-gate schema family.
- Determinism/replayability, canonical JSON hashing, and fail-closed posture remain mandatory.
- No implicit carryover of key-expansion authority is allowed post-v43.

## Planning Boundary (For This Family)

- IDE-specific UX realization (for example VSCode extension mechanics) is explicitly out of immediate scope.
- Primary runtime path is Codex SDK integration within ADEU.
- Standalone portability is required at architecture level (package/runtime boundary), not tied to ADEU domain modules.
- Portability boundary clarification:
  - harness kernel logic is domain-agnostic and consumes only compiled semantic artifacts via typed interfaces,
  - domain-specific meaning remains upstream in ASC outputs, not embedded in harness kernel policy logic.

## Naming Convention (New Family)

- `V33-*` identifiers are reserved for single-path families in this planning cycle.
- `B33-*` identifiers are reserved for explicit multi-path bundles.
- `V32-*` remains historical/closed and is not reused.

## Vision Contract (Planning-Level)

- Authoritative sources:
  - lock/decision docs + compiled semantic artifacts + explicit pipeline profile contract.
- Non-authoritative sources:
  - free-form prompt prose as behavioral authority.
- Operational rule:
  - agent-facing prompts are rendered views of typed task contracts, not source-of-truth policy.
- Single-source constraint:
  - taskpack compilation consumes compiled ASC artifacts plus explicit profile contracts and must not re-parse raw markdown prose as semantic authority.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "agent_harness_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v6.md",
  "taskpack_compiler_authority_inputs": [
    "artifacts/semantic_compiler/*/evidence_manifest.json",
    "artifacts/semantic_compiler/*/surface_diff.json",
    "compiled_commitments_ir_artifacts",
    "pipeline_profile_contract"
  ],
  "profile_resolution_key": "profile_id",
  "profile_resolution_authority": "registry_only",
  "profile_resolution_purity": "deterministic_pure_resolution",
  "pipeline_profile_input_mode": "authoritative_surface_only",
  "ad_hoc_profile_path_input": "forbidden",
  "raw_docs_as_semantic_input_for_taskpack_compiler": false,
  "closed_path_family": "V32",
  "closed_paths": [
    "V32-A",
    "V32-B",
    "V32-C",
    "V32-D",
    "V32-E",
    "V32-F"
  ],
  "next_path_family": "V33",
  "default_next_arc_candidate": "V33-A",
  "sdk_priority": "codex_sdk_first",
  "standalone_portability_required": true
}
```

## Harness Diagnostic Namespace (Planning)

- Harness diagnostics use a dedicated namespace family (planning placeholder): `AHK[0-9]{4}`.
- Existing URM runtime error-code families remain unchanged by this planning draft.

## Path Family V33 (Agent Harness)

### Path V33-A: Pipeline Profile + TaskPack Contracts + Deterministic Compiler

Lock class: `L1`

Goal:

- introduce typed contracts for harness behavior knobs and agent task execution packets;
- compile authoritative planning/semantic evidence into deterministic taskpacks.

Scope:

- add a typed Pipeline Profile contract (human knob surface, machine validated);
- add deterministic profile resolution for compiler input:
  - profile selection by stable authoritative `profile_id`,
  - `profile_id` resolves through a single authoritative registry surface,
  - no arbitrary local ad-hoc profile file path ingestion;
- add a portable harness kernel package boundary (for example `packages/adeu_agent_harness`) that owns:
  - pipeline profile schema,
  - taskpack schema,
  - deterministic taskpack compiler interface,
  - deterministic serialization/hashing utilities;
- add a typed TaskPack contract with deterministic rendering:
  - `TASKPACK.md` (agent-facing projection),
  - `ACCEPTANCE.json`,
  - `ALLOWLIST.json`,
  - `FORBIDDEN.json`,
  - `COMMANDS.json`,
  - `EVIDENCE_SLOTS.json`,
  - `taskpack_manifest.json` (authoritative ABI manifest with component schema IDs + component hashes),
  - bundle hash derived from canonical JSON of `taskpack_manifest.json` only;
- add deterministic compiler entrypoint from compiled ASC artifacts + explicit profile contracts to taskpack bundle;
- add fixture corpus + golden tests for deterministic taskpack emission.

Locks:

- prompt text is projection-only; policy authority remains typed contracts;
- taskpack compiler semantic authority is compiled ASC artifacts plus profile contract only; markdown prose interpretation is forbidden;
- profile authoring lock is frozen:
  - profile schema is strict (`extra=forbid` equivalent posture),
  - invalid fields/types fail closed with deterministic field-path diagnostics;
- taskpack ABI integrity lock is frozen:
  - `taskpack_manifest.json` is authoritative component catalog for schema IDs and hashes,
  - each taskpack component uses a contract ID format `taskpack/<component>@<version>`,
  - component schema IDs are authoritative only via `taskpack_manifest.json`,
  - each listed component hash must verify against produced component bytes,
  - bundle hash authority is canonical JSON hash of `taskpack_manifest.json` only;
- markdown projection lock is frozen:
  - `TASKPACK.md` is generated under a canonical markdown profile (fixed section order, UTF-8, LF, deterministic whitespace policy),
  - markdown projection is byte-identical across reruns for identical inputs;
- projection traceability lock is frozen:
  - each rendered semantic section in `TASKPACK.md` carries deterministic machine-readable source attribution (`source_schema_id`, `source_component_hash`) derived from `taskpack_manifest.json`,
  - attribution syntax is frozen to machine-extractable markers (`<!-- adeu:... -->`) with deterministic parser/verifier coverage.
- canonical JSON/hash profile remains frozen;
- deterministic env contract is frozen (`TZ=UTC`, `LC_ALL=C`, `PYTHONHASHSEED=0`);
- no runtime/provider/proposer boundary expansion;
- no stop-gate schema-family fork in this path.

Acceptance:

- repeated compile runs over identical inputs produce byte-identical taskpack JSON artifacts and byte-identical markdown projection;
- malformed/incomplete profile or taskpack contract fails closed with deterministic diagnostics;
- taskpack allowlist/forbidden/command surfaces are machine-checkable.
- ad-hoc profile path attempts fail closed with deterministic diagnostics.

### Path V33-B: Codex SDK Harness Runner (Constrained Execution)

Lock class: `L1`

Goal:

- execute taskpacks through Codex SDK with fail-closed enforcement of task constraints.

Scope:

- add harness runner that consumes compiled taskpacks and invokes Codex SDK;
- define execution interface in harness kernel and adapter boundary for concrete SDK/runtime providers;
- ensure API-layer Codex integrations are adapter implementations and not harness-kernel hard dependencies;
- enforce allowlisted edit surfaces and forbidden effect surfaces;
- enforce required command execution and deterministic env subset;
- add deterministic pre-apply policy validation pass:
  - model output is normalized into a canonical candidate-change-plan artifact (file operations + diff payload),
  - policy validation evaluates the canonical candidate-change-plan against `ALLOWLIST.json` and `FORBIDDEN.json` before any workspace write/commit step;
- add deterministic dry-run mode (`--dry-run`):
  - resolves taskpack + profile, renders final execution payload, emits canonical payload artifact and provenance preview, performs no network execution and no workspace mutation;
- emit deterministic run provenance artifact (inputs, model role, outputs, hashes, exit status).

Locks:

- runner behavior is taskpack-driven only;
- harness kernel must not import `apps/api` application-layer modules directly;
- out-of-allowlist edits fail closed;
- wrapper/indirect execution paths for required commands are non-authoritative unless explicitly allowed by contract.
- anti-injection authority lock is frozen:
  - repository text is non-authoritative by default for runtime instruction authority,
  - only taskpack-declared context blocks are authoritative for agent instructions.
- post-generation boundary enforcement lock is frozen:
  - model output is untrusted until deterministic policy validation succeeds,
  - freeform natural-language claims are non-authoritative for policy validation,
  - policy validation failure blocks apply/commit and fails closed.

Acceptance:

- constrained runner rejects non-authorized edits/commands deterministically;
- identical taskpack + inputs + env produce replayable provenance artifacts.
- deterministic dry-run emits byte-identical payload/provenance preview artifacts for identical inputs.

### Path V33-C: Auditor/Verifier Lane + Evidence Writer

Lock class: `L0`

Goal:

- make verification and closeout evidence emission first-class harness outputs.

Scope:

- add deterministic verification pipeline over taskpack outputs;
- add evidence slot writer producing machine-checkable closeout blocks;
- integrate with existing closeout lint posture without schema-family churn.

Locks:

- required violations are error-only and fail closed;
- warning channel cannot satisfy required-violation reporting;
- no implicit threshold widening.
- evidence writer compatibility lock is frozen:
  - emits closeout blocks compatible with existing `stop_gate_metrics@1` posture,
  - introduces no new stop-gate metric keys in this path.
  - derived metric-key cardinality continuity remains frozen at current baseline (`80`) in this path.

Acceptance:

- verification lane reproduces identical results on reruns with fixed inputs;
- closeout evidence slots are fully populated or fail closed.

### Path V33-D: UX Surface Packaging (Integrated + Standalone)

Lock class: `L1`

Goal:

- expose the same harness kernel in two deployment modes:
  - ADEU-integrated UX,
  - standalone module UX.

Scope:

- define shared kernel package boundary and mode-specific adapters;
- enforce no coupling to domain-module semantics/contracts.

Locks:

- kernel contracts are identical across deployment modes;
- adapter layer cannot redefine policy semantics.

Acceptance:

- same taskpack/profile inputs yield byte-identical deterministic artifacts (`taskpack_manifest`, taskpack JSON components, verification/evidence payloads) across both modes.
- mode-variant execution outputs must remain policy-equivalent with identical pass/fail decisions and issue-code sets.
- policy-equivalence basis is frozen to:
  - `issue_code_set`,
  - `required_evidence_slots_filled`,
  - `allowlist_violations`,
  - `forbidden_effects_detected`.

## Decision Matrix (Post-v43)

Interpretation note:

- matrix risk values refer to governance-boundary risk (execution-threshold risk begins at `V33-B`).

| Option ID | Includes | Max lock class | Benefit | Risk |
|---|---|---:|---|---|
| `V33-A` | contracts + taskpack compiler | `L1` | establishes authoritative harness contract surface | medium |
| `B33-AB` | `V33-A + V33-B` | `L1` | adds executable Codex SDK constrained loop | high |
| `B33-ABC` | `V33-A + V33-B + V33-C` | `L1` | end-to-end contract -> execute -> verify loop | very high |
| `B33-ABCD` | `V33-A + V33-B + V33-C + V33-D` | `L1` | complete integrated + standalone UX family | very high |

Execution-threshold interpretation:

- `B33-AB` is the first end-to-end execution threshold and inherits governance criticality from `V33-B`.
- `B33-ABC` is the first full-loop threshold (compile -> execute -> verify) and requires stricter stop-gate evidence posture than `V33-A` alone.

## Recommended Sequencing (Default)

1. `vNext+44`: `V33-A` (contracts + deterministic taskpack compiler, no runner yet).
2. `vNext+45`: `V33-B` (Codex SDK constrained runner).
3. `vNext+46`: `V33-C` (auditor/verifier + evidence writer).
4. `vNext+47`: `V33-D` (integrated + standalone UX packaging).

## Proposed First Arc Candidate (`vNext+44`)

Candidate: `V33-A` only (`L1`, thin-slice).

Intermediate-state note:

- `V33-A` without `V33-B` is an accepted transitional state: contract compilation and verification hardening proceed before introducing execution surface authority.

Suggested PR split:

1. `contracts: add V33-A pipeline profile and taskpack schemas + compiler MVP`
2. `tests: add V33-A determinism and fail-closed guard suite`

## Continuity and Non-Regression Requirements

- Existing v36-v43 continuity guards remain mandatory and unreverted.
- No `L2` boundary release is authorized by this options draft.
- Stop-gate metric-key expansion is not assumed for `V33-A`; any new metrics require explicit lock text.

## Disposition of Deferred V32 Follow-ons

- `V32-F` optional metric extension is closed in `v43`.
- Remaining deferred V32 candidates from prior locks remain deferred (not abandoned) and are not implicitly subsumed by `V33`:
  - compiler developer ergonomics (`--stop-after`, IR dumps),
  - resolver namespace aliasing/workspace-scoped bindings,
  - deterministic bootstrap overflow controls + PR split chunking,
  - semantic-equivalency delta evaluation lane,
  - deep-path keyset extraction semantics,
  - optional matrix-lane coverage-signature validation.
- Any activation of these deferred items still requires explicit lock selection and scope text.

## Proposed Next Step

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS44.md` for `V33-A` only.
2. Draft companion assessment scaffold for `V33-A` edge review.
3. Implement `V33-A` in small green PRs under frozen determinism constraints.
