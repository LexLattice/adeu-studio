# Assessment: v4 Draft Comparison (`_codex`, `_gpt`, `_opus`, `_gemini`)

This note compares:

- `docs/archives/next_arc_options_v4/DRAFT_NEXT_ARC_OPTIONS_v4_codex.md`
- `docs/archives/next_arc_options_v4/DRAFT_NEXT_ARC_OPTIONS_v4_gpt.md`
- `docs/archives/next_arc_options_v4/DRAFT_NEXT_ARC_OPTIONS_v4_opus.md`
- `docs/archives/next_arc_options_v4/DRAFT_NEXT_ARC_OPTIONS_v4_gemini.md`

Date context: comparison prepared after `vNext+16` closeout (`February 2026`).

## Executive Summary

High-level convergence is strong on baseline state and process discipline:

- all drafts treat `vNext+16` as stable and deterministic
- all drafts preserve additive/deterministic guardrails
- all drafts avoid immediate uncontrolled semantic mutation

Primary divergence is on **what to optimize first**:

- `codex` and `gemini` lean toward integrity follow-on closure
- `gpt` and `opus` lean toward product-consumption or broader system-level pivot
- `opus` and `codex` explicitly emphasize maintenance/CI sustainability pressure

## Convergence Map

Shared themes with broad overlap:

1. Deterministic closeout discipline must continue (`manifest`, replay, hash, stop-gate).
2. Provider parity maintenance is a fallback, not default expansion.
3. Next work should be thin-slice scoped with explicit locks.
4. Existing v16 diagnostics are a foundation, not an endpoint.

Partial convergence themes:

1. Integrity follow-on:
   - strong in `codex` and `gemini`
   - present indirectly in `opus`
   - lower emphasis in `gpt`
2. Product surfacing:
   - strong in `gpt` and `opus`
   - weak/secondary in `codex` and `gemini`
3. Consolidation/operational debt:
   - strong in `opus` and `codex`
   - limited in `gpt`
   - implicit in `gemini`

## Divergence Map

Main points of disagreement:

1. First-arc recommendation:
   - `codex`: integrity diagnostics expansion first
   - `gpt`: core-ir proposer/product surface first
   - `opus`: consolidation/CI sustainability first
   - `gemini`: normative integrity completion first
2. Risk appetite:
   - `gemini` introduces solver semantics v4 path earlier than others
   - `gpt` introduces product and advisory/proof options earlier
   - `codex` is moderate and sequencing-focused
   - `opus` is conservative on maintainability before broader exposure
3. Scope framing:
   - `gpt` is option-centric and product-oriented
   - `opus` is architecture-program oriented (2–3 arc horizon)
   - `gemini` is deferred-item closure oriented
   - `codex` is middle-ground with explicit fallback and operational guardrails

## Depth and Rigor Variation

Observed variation in technical depth and lock precision:

## `v4_opus`

- Highest repo-grounded detail and path decomposition depth.
- Strong explicit articulation of system tensions (two IR families, schema growth, CI budget).
- Strong for strategic sequencing and large-program planning.

## `v4_codex`

- High lock/process coherence and clean transition from v16 closeout.
- Balanced across feature expansion and maintainability.
- Strong on deterministic governance continuity and practical next-step freeze candidate.

## `v4_gemini`

- Good deferred-item continuity (especially v15/v16 carryovers).
- Strong technical specificity on normative deontic follow-on.
- More aggressive in introducing semantics-v4 path, which raises risk if taken too early.

## `v4_gpt`

- Strong product-orientation and articulation of “ship visible value now”.
- Useful set of alternative directions (proposer, report, advice, proof).
- Lightest formal lock detail relative to the other three drafts.

## Unique Ideas Worth Keeping

From `v4_gpt`:

- explicit core-ir proposer surface as a product unlock
- optional advisory layer and proof-lane starter paths

From `v4_opus`:

- cross-IR coherence bridge as a first-class path
- explicit recognition that schema/metric growth can become a blocker

From `v4_gemini`:

- direct closure of deferred extraction/deontic edges before broad expansion
- clear sequencing that keeps normative correctness ahead of semantic uplift

From `v4_codex`:

- balanced “expand + consolidate + fallback” planning shape
- concrete continuity with current locks and closeout artifacts

## Comparative Matrix

| Draft | Primary Bias | v17 First Recommendation | Determinism Discipline | Product Focus | Maintainability Focus | Semantic Expansion Urgency |
|---|---|---|---|---|---|---|
| `_codex` | balanced integrity + operations | integrity follow-on (`9b`) | high | medium | high | low/medium |
| `_gpt` | product activation | core-ir proposer surface | medium | high | low/medium | medium |
| `_opus` | systems consolidation | consolidation/CI sustainability (`12a`) | high | medium/high | high | low |
| `_gemini` | deferred diagnostic closure | normative integrity follow-on (`11a`) | high | low/medium | medium | medium/high |

## What Converges Most Strongly for a Safe Next Lock

Most defensible shared-core starting point:

1. Keep `vNext+17` additive and deterministic.
2. Continue integrity expansion before solver-semantic mutation.
3. Preserve provider-parity fallback branch.
4. Make CI/runtime sustainability explicit in planning even if not chosen as v17 core scope.

## Synthesis Implication

The most stable synthesis is:

- choose integrity follow-on as primary v17 thin slice,
- plan consolidation as immediate next arc,
- stage product exposure after those two if parity remains stable.

This preserves the strongest overlap among drafts while still retaining high-value ideas from all four.
