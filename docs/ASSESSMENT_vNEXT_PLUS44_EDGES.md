# Assessment vNext+44 Edges (V33-A Planning)

This document records pre-implementation edge analysis for `vNext+44` (`V33-A` Pipeline Profile + TaskPack contracts + deterministic compiler), aligned to `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`.

Status: active planning assessment (pre-implementation, March 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS44_EDGES.md",
  "phase": "planning_assessment",
  "authoritative": false,
  "authoritative_scope": "pre_implementation_edge_analysis_only",
  "required_in_closeout": true,
  "notes": "Planning assessment placeholder state. Post-implementation closeout must refresh findings/status against v44 execution evidence."
}
```

## Scope

- In scope: typed Pipeline Profile contract, TaskPack contract ABI, deterministic taskpack compiler, deterministic markdown projection with source attribution, and fail-closed guard posture.
- Out of scope: Codex SDK constrained execution runner (`V33-B`), auditor/evidence writer lane (`V33-C`), integrated/standalone UX packaging (`V33-D`), stop-gate metric-key expansion, and runtime/provider/proposer boundary changes.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS43.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS43.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`
- `apps/api/scripts/lint_closeout_consistency.py`
- `artifacts/stop_gate/metrics_v43_closeout.json`
- post-v43 feedback set (Gemini + GPT + Opus, March 4, 2026 UTC)

## Repository Baseline Anchors

1. v43 (`V32-F`) is closed on `main` with additive stop-gate migration complete.
2. Stop-gate schema family remains `stop_gate_metrics@1`; derived metric-key cardinality baseline is `80`.
3. v36-v43 continuity posture is frozen and required for v44.
4. Harness-specific compiler/contract package does not yet exist; `V33-A` is greenfield at implementation level.
5. Existing Codex SDK integrations live in app-layer surfaces and remain out-of-scope for v44 (`V33-B` deferred).

## V33-A Edge Set

1. Raw-doc semantic authority bleed:
   - taskpack compiler can accidentally re-interpret markdown prose directly.
2. Profile injection backdoor:
   - ad-hoc local profile path ingestion can bypass authoritative profile selection.
3. Profile resolution nondeterminism:
   - implicit env/default fallbacks can produce non-replayable profile selection.
4. Profile registry mutability drift:
   - registry can map stable `profile_id` to silently changed payload bytes without ID change.
5. Profile registry representation ambiguity:
   - registry storage format/schema/entry uniqueness can drift without explicit contract.
6. Profile schema drift:
   - loose validation can accept unknown or malformed knob fields.
7. Authority-input drift:
   - compiler can consume wrong/missing ASC artifacts without deterministic failure.
8. Semantic-compiler input arc-selection ambiguity:
   - wildcard artifact-family references can resolve multiple/no source arcs without explicit selection policy.
9. TaskPack component set drift:
   - missing or extra components can bypass ABI expectations.
10. Contract ID drift:
   - component schema IDs can diverge without a frozen naming policy.
11. Manifest integrity drift:
   - component hashes can mismatch produced artifacts if manifest checks are weak.
12. Bundle-hash subject ambiguity:
   - hashing all files vs manifest-only can fork integrity semantics.
13. Markdown projection nondeterminism:
   - whitespace/order/line-ending variance can break replayability.
14. Markdown section-order ambiguity:
   - frozen section-order claims can drift if section IDs/order are not explicitly enumerated.
15. Attribution traceability loss:
   - rendered markdown can omit machine-verifiable source attribution.
16. Attribution non-verifiability:
   - attribution can exist as free text but not be parser/verifier enforceable.
17. Attribution marker ownership ambiguity:
   - renderer-owned positions can be under-specified without explicit root-scope EOF marker rules.
18. Attribution marker collision/spoof risk:
   - marker-like strings in payload content can collide with attribution syntax unless verifier scope is frozen.
19. Severity-channel downgrade risk:
   - required structural violations can be downgraded to warnings.
20. False-green planning evidence risk:
   - planning-gate docs can overclaim implementation closeout readiness.
21. Stop-gate continuity regression risk:
   - v44 planning/compiler work can accidentally alter metric keyset posture.
22. Transitional-state misread risk:
   - `V33-A`-only delivery can be misread as full harness execution readiness.
23. Kernel boundary ambiguity:
   - portability goals can drift without a strict package boundary in v44 scope.
24. Deferred-item lineage drift:
   - unresolved V32 deferred candidates can be implicitly treated as superseded.
25. Deterministic-env drift:
   - compiler/guards can execute outside frozen env settings.
26. Arc authorization drift:
   - v44 lock can accidentally absorb `V33-B`/`V33-C`/`V33-D` behavior.

## Feedback Disposition Into v44 Guardrails

1. GPT: freeze profile resolution semantics.
   - captured as `profile_id` + `registry_only` + deterministic pure resolution + no ad-hoc path input.
2. GPT: freeze TaskPack schema-id policy.
   - captured as `taskpack/<component>@<version>` with manifest-only schema-id authority.
3. GPT: make markdown attribution verifiable.
   - captured as frozen `<!-- adeu:... -->` marker syntax with required attribution verifier.
4. Opus: avoid kernel naming collision and portability ambiguity.
   - captured as package-boundary lock (portable harness package boundary, domain-agnostic kernel logic).
5. Opus/Gemini: secure authority boundary against prompt injection vectors.
   - v44 captures authority constraints at compile stage; runtime anti-injection enforcement is explicitly deferred to `V33-B`.
6. Gemini: avoid profile-contract backdoor.
   - captured by explicit ban on ad-hoc local profile path ingestion and registry-only profile resolution.
7. Gemini: prevent profile mutability under stable ID.
   - captured by registry hash-binding requirement (`profile_id` plus declared canonical profile hash and strict resolved-hash verification).
8. Gemini: prevent attribution marker hijacking/collision.
   - captured by frozen verifier scope (renderer-owned semantic markers only) and fail-closed spoof/collision policy.
9. Opus: specify registry storage format for hash-binding determinism.
   - captured by frozen `taskpack_profile_registry@1` contract with canonical JSON object representation and strict entry/uniqueness validation.
10. Opus: make renderer-owned attribution marker positions concrete.
   - captured by frozen root-scope EOF marker position rules and parser-scope exclusions (code fences/blockquote content non-authoritative).
11. Opus: remove wildcard arc-selection ambiguity from authority-input resolution.
   - captured by explicit single `source_semantic_arc` policy with fail-closed zero/multi-match handling.
12. Opus: freeze markdown section order with explicit section-order IDs.
   - captured by frozen `required_section_order_ids` under markdown projection policy.

## Required Guardrails

- Compiler-authority lock:
  - taskpack compilation consumes compiled ASC artifacts plus explicit profile contracts only.
- Raw-doc prohibition lock:
  - raw markdown prose is non-authoritative for taskpack semantic input.
- Profile-resolution lock:
  - `profile_id` + `registry_only` + deterministic pure resolution.
- Profile-registry hash-binding lock:
  - registry entry declares canonical profile hash and compiler enforces exact resolved-hash match.
- Profile-registry contract lock:
  - registry schema, required fields, and `profile_id` uniqueness are strict and fail closed on drift.
- Profile-schema strictness lock:
  - unknown fields/types fail closed with deterministic diagnostics.
- Authority-input version-selection lock:
  - compiler resolves authority inputs from exactly one explicit semantic arc and fails closed on ambiguous wildcard matches.
- TaskPack ABI lock:
  - required component set is fixed and manifest is authoritative for component schema IDs/hashes.
- Contract-ID lock:
  - component schema ID format `taskpack/<component>@<version>` is frozen.
- Bundle-hash lock:
  - bundle hash subject is canonical JSON hash of `taskpack_manifest.json` only.
- Markdown-canonicalization lock:
  - generated markdown uses frozen encoding/order/line-ending/whitespace policy.
- Markdown section-order lock:
  - generated markdown enforces frozen section-order IDs and fails closed on drift.
- Attribution-verifier lock:
  - every rendered semantic section carries machine-verifiable source attribution.
- Attribution-marker position lock:
  - verifier accepts only root-scope semantic-section EOF attribution markers emitted by renderer.
- Attribution-collision lock:
  - marker-like payload text is non-authoritative; spoof/collision detection is fail-closed under frozen verifier scope.
- Severity lock:
  - required violations are error-only and fail closed.
- Continuity lock:
  - v36-v43 continuity guarantees remain merge-blocking and unreverted.
- Stop-gate continuity lock:
  - no new metric keys; cardinality remains `80` in v44 scope.
- Scope fence:
  - no `V33-B`, `V33-C`, or `V33-D` behavior release in v44.

## Acceptance Evidence Targets (v44)

- Deterministic reruns over identical inputs produce byte-identical taskpack JSON components.
- `TASKPACK.md` projection is byte-identical and attribution-verifier clean across reruns.
- Manifest component-hash verification fails closed on any component drift.
- Profile resolution rejects ad-hoc path ingestion and non-registry resolution paths.
- Profile registry hash-binding checks fail closed when resolved bytes drift from declared registry hash.
- Profile-registry schema/entry-uniqueness checks fail closed on malformed registry contract payload.
- Semantic-compiler authority-input resolution fails closed when `source_semantic_arc` resolution is zero-match or multi-match.
- `TASKPACK.md` frozen section-order IDs pass deterministically and fail closed on ordering drift.
- Attribution verifier ignores non-authoritative marker-like payload text and fails closed on marker spoof/collision.
- v36-v43 continuity posture remains green with no stop-gate keyset/cardinality drift.

## Implementation Readiness Notes

1. `V33-A` is implementation-ready as an `L1` thin slice and valid transitional state before runner release.
2. Highest risk concentration is authority-boundary enforcement (input surfaces, profile resolution, ABI/hash semantics).
3. Recommended implementation order:
   - profile contract + registry-only resolution,
   - taskpack component schemas + manifest ABI,
   - deterministic compiler/projection path,
   - deterministic guard suite and failure fixture coverage.

## Deferred Expansions (Non-v44)

- Runtime anti-injection enforcement over model outputs (candidate-change-plan policy validation) is deferred to `V33-B`.
- Codex SDK adapter boundary and deterministic dry-run execution are deferred to `V33-B`.
- Delta-aware taskpack recompilation/caching optimizations are deferred beyond v44.
- Cryptographic signing of taskpack bundle hash for runner trust-chain verification is deferred beyond v44.
- Auditor/evidence writer lane and closeout-slot automation are deferred to `V33-C`.
- Integrated/standalone UX mode parity enforcement is deferred to `V33-D`.
- Deferred V32 follow-ons remain deferred and require explicit future lock text.
