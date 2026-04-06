# Draft ADEU History Semantics Implementation Mapping v0

Status: bounded implementation/support note for the first repo-owned
`adeu_history_semantics` proto-module.

Authority layer: package implementation plus support explanation only.

This note explains the package home, frozen artifact family, verification posture,
and deliberate deferrals for the first bounded history/abstract semantics slice.
It does **not** authorize a broad repo architecture rewrite.

Read together with:

- `README.md`
- `REPO_ATLAS.md`
- `AGENTS.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`
- `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`
- `packages/adeu_semantic_forms`
- `packages/adeu_semantic_source`
- `packages/adeu_paper_semantics`
- `packages/urm_domain_digest`

## Scope

This slice adds a package-first, tests-first, bounded proto-module for turning
conversation-history-like text and abstract-like text into explicit ADEU/ODEU-governed
semantic artifacts.

The implementation is intentionally narrow:

- raw history remains the authoritative substrate
- deterministic preclassification happens before reconstruction
- user messages anchor theme selection when available
- assistant text may explicate the inferential lanes once attached to a
  user-anchored theme frame
- chronology and inferential maturity are represented separately
- lane absence and underdetermination are explicit rather than silently filled in

## Selected Repo Home

Chosen home:

- `packages/adeu_history_semantics`

Why this home was selected:

1. `packages/` is the repo-native location for typed, reusable, deterministic
   artifact families. The requested work is a semantic artifact family, not an
   API route, web feature, or runtime orchestration surface.
2. `packages/adeu_paper_semantics` is the closest local precedent for a
   domain-specific semantic module that owns closed-world Pydantic models,
   canonical hashing, fixtures, and validation tests.
3. `packages/adeu_semantic_source` is the wrong boundary for this slice because
   that package is about docs/module parsing for the semantic compiler lane,
   while history semantics needs its own source/preclassification/slice/
   reconstruction/workspace artifact family.
4. `packages/adeu_semantic_forms` is lower-level substrate. It is a dependency
   source for canonical hashing posture, not the correct place to put a
   conversation/history domain module.
5. `packages/urm_domain_digest` shows a useful bounded-domain pattern, but the
   current request is not a worker/runtime adapter. Runtime widening was
   therefore deferred.

## Frozen Artifact Family

The package freezes the following first bounded artifact family.

### 1. Raw source artifact

`HistorySourceArtifact`

Purpose:

- preserve the authoritative raw text
- carry input kind (`conversation_history` or `abstract_like`)
- preserve source label/notes as overlay metadata
- expose `corpus_wave_posture` so Wave 0 bootstrap work is not structurally blocked

Identity basis:

- input kind
- canonical source text hash

### 2. Deterministic history ledger

`HistoryPreclassification`
`HistoryLedgerEntry`
`HistoryLedger`

Purpose:

- stratify the raw source into bounded entries before semantic reconstruction
- preserve source line spans and order indices
- record deterministic preclassification signals such as:
  - role
  - origin type
  - source declaration hints
  - structural markers
  - text-shape signals
  - local grouping ids
  - suggested slice boundaries

Important posture:

- these are preclassification signals, not truth claims
- they are fail-closed, explicit, and provenance-linked

### 3. Bounded slice artifact

`HistorySlice`

Purpose:

- collect a bounded local unit for later reconstruction
- preserve chronology start/end indices
- preserve a separate inferential maturity score/band
- distinguish primary entry ids from support entry ids

Primary-entry rule:

- if user entries exist in the local group, those become the primary entries
- assistant/system material becomes support for the slice
- if no user entries exist, the slice falls back to source-primary behavior

### 4. Theme anchor artifact

`HistoryThemeAnchor`

Purpose:

- freeze a bounded theme anchor with explicit selection posture
- keep user messages first-order for theme selection whenever available
- record the primary/support entry ids and slice ids that justify the anchor

### 5. Explicit ODEU reconstruction packet

`HistoryODEULaneReconstruction`
`HistoryODEUReconstructionPacket`

Purpose:

- reconstruct the slice/theme pair through four explicit lanes: `O`, `E`, `D`, `U`
- record lane presence status:
  - `present`
  - `weakly_present`
  - `underdetermined`
  - `not_salient`
- record explicitation status:
  - `locally_explicit`
  - `dialogically_explicitated`
  - `contextually_reconstructed`
  - `underdetermined`
- keep evidence refs attached to concrete ledger entries/excerpts

Important posture:

- this is not a one-paragraph summary plus labels
- each lane is reconstructed separately
- absent or weak lanes remain explicit as absent or underdetermined

### 6. Inferential workspace substrate

`HistoryWorkspaceQuestion`
`HistoryWorkspaceThemeFrame`
`HistoryWorkspaceSnapshot`

Purpose:

- provide the first bounded inferential workspace artifact
- preserve both chronology order and inferential order
- surface underdeveloped lanes and open questions
- keep provenance entry ids attached at the frame level

### 7. End-to-end semantic bundle

`HistorySemanticBundle`

Purpose:

- freeze a deterministic end-to-end artifact from raw source through workspace
- provide a single validation surface for tests, fixtures, and later ingestion

## Deterministic Pipeline

The frozen pipeline is:

1. `build_history_source_artifact`
2. `build_history_ledger`
3. `build_bounded_slices`
4. `build_theme_anchors`
5. `build_odeu_reconstruction_packets`
6. `build_workspace_snapshot`
7. `compile_history_semantic_bundle`

This order is intentional.

The package does **not** jump directly from raw text to high-level semantics.
It first records deterministic preclassification and bounded grouping signals, then
constructs provenance-linked overlays.

## Design-Invariant Mapping

### Raw history remains authoritative

The canonical source text is preserved in `HistorySourceArtifact`. Every later
artifact references the source id and retains ledger provenance.

### Deterministic preclassification comes first

The ledger layer is created before any ODEU reconstruction. Role/origin/marker/
shape/grouping information is frozen as explicit preclassification rather than
buried in later inference.

### User messages anchor themes

`HistorySlice` and `HistoryThemeAnchor` treat user entries as primary entries when
present. This keeps the subject/theme layer aligned with the requesting or
originating perspective rather than with later assistant exposition.

### Assistant output is second-order for theme selection but often first-order for explication

Packets can mark assistant-derived lane material as
`dialogically_explicitated` once it is attached to a user-anchored slice/theme.
The assistant can therefore make the inferential structure explicit without
becoming the theme-selection authority.

### ODEU reconstruction is explicit 4-lane rebuild

Every packet carries a complete ordered lane set `O/E/D/U`. The lanes are
validated individually, and absent lanes remain explicit as absent.

### Chronology is separated from inferential development

`HistorySlice` stores chronology indices and inferential maturity. The workspace
snapshot then freezes both `chronology_slice_order` and
`inferential_slice_order`.

### Lane weakness/absence is explicit

Lanes can be `weakly_present`, `underdetermined`, or `not_salient`. The package
never forces full symmetric lane presence.

### Reconstructive honesty is explicit

Lane models distinguish:

- locally explicit material
- dialogically explicitated material
- contextually reconstructed material
- underdetermined material

This is the bounded v0 mechanism for preventing later explicitness from being
silently projected backward.

### Bootstrap corpus principle remains open

`corpus_wave_posture` on the source artifact leaves room for a later ingestion
curriculum where conversation-history-like Wave 0 material has special status in
framework emergence and stabilization.

## Verification Surfaces Added

The slice adds:

- package scaffolding under `packages/adeu_history_semantics`
- deterministic reference fixtures for:
  - a bounded conversation-history-like demo source
  - a bounded abstract-like demo source
  - compiled reference bundles for both
- unit tests covering:
  - preclassification determinism and grouping
  - external-paste-like signal detection
  - model validation
  - projection-only vs identity-changing mutations
  - absent-lane fail-closed behavior
  - provenance grounding
  - end-to-end bundle replay from input text to workspace snapshot

## Important Bounded Choices

### Conservative conversation header parsing

The parser intentionally recognizes full role headers (`User`, `Assistant`,
`System`) rather than one-letter `U:` role aliases.

Reason:

- in this module, `U:` is also the explicit utility-lane marker
- interpreting `U:` as a role header would silently split assistant ODEU lane
  material into false user messages
- the fail-closed choice is to avoid that ambiguity in v0

### Exact theme-key merge only

Theme anchors merge only on exact deterministic theme keys in v0.
No fuzzy or embedding-based theme merge is introduced here.

### Advisory-only semantic posture

The semantic layers are overlays, not replacements for the source. The package
keeps interpretation authority explicitly advisory-only.

## Intentional Deferrals

This slice deliberately does **not** add:

- database storage
- vector stores or RAG infrastructure
- graph database integration
- live API or web UI productization
- runtime worker/domain adapters
- automatic ingestion of private chat history
- learned or probabilistic lane reconstruction
- broad repo-wide doctrine rewrites
- multi-wave ingestion orchestration beyond the `corpus_wave_posture` hook
- fuzzy theme clustering across distant slices/documents

## Next Bounded Growth Path

Reasonable next steps after this slice would be:

1. a Wave 0 corpus loader that still emits `HistorySourceArtifact` and `HistorySemanticBundle`
2. stronger deterministic lineage/source-declaration surfaces for imported chat logs
3. bounded cross-slice theme consolidation rules beyond exact-key merge
4. explicit workspace-delta artifacts for longitudinal inferential development
5. only after the package contract is accepted, optional API/runtime consumers

## Implementation Summary

The implemented package is therefore a bounded backbone module:

- package-first
- tests-first
- examples/fixtures-first
- provenance-linked
- fail-closed
- explicitly ODEU-structured
- suitable for later real bootstrap corpus ingestion without pretending that
  corpus is already present in the repo
