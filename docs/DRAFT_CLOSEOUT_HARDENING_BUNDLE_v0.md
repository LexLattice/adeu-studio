# Draft Closeout Hardening Bundle v0

Status: working synthesis only (March 7, 2026 UTC).

This document records the proposed post-`v54` operational hardening bundle for the closeout
lane.

It is not a lock doc. It does not authorize runtime behavior changes, release-scope changes,
or boundary expansion. It does not supersede `V34-G` planning.

## Purpose

- capture the counterfactual structural review of the current closeout lane;
- name the safe optimization surface precisely;
- define a small future bundle that mechanizes deterministic closeout glue without
  weakening semantic adjudication or auditability.
- require explicit no-regression proof against the currently accepted closeout baseline
  before any hardening slice is treated as safe.

## Baseline Finding

The current closeout lane is already structurally correct.

- deterministic builders already exist for quality dashboard, stop-gate metrics, and
  closeout consistency lint;
- artifact-authoritative validators already exist for harness evidence, attestation, retry
  context, and standalone integrity;
- the main remaining inefficiency is the orchestration shell around those deterministic
  steps, especially long inline closeout command assembly;
- the accountable semantic layer still belongs in explicit reasoning:
  - lock-satisfaction judgment,
  - edge disposition,
  - cleanup retirement,
  - final gate statement,
  - overclaim audit.

Working rule:

- mechanize the glue, not the judgment layer.

## Safe Optimization Surface

### 1. Deterministic orchestration extraction

Current issue:

- recent closeout docs still carry long inline Python orchestration blocks for multi-artifact
  regeneration.

Safe change:

- extract that orchestration into a dedicated script under `apps/api/scripts/`;
- keep the script transparent by printing or recording its fully resolved execution plan,
  subcommands, inputs, and output targets before mutation;
- fail closed on missing inputs, unexpected outputs, unresolved arc parameters, or path
  inputs outside approved repo roots.

Preserved invariants:

- canonical artifact schemas remain unchanged;
- emitted artifact bytes remain deterministic;
- closeout still depends on explicit human/agent adjudication after deterministic generation.

### 2. Deterministic closeout artifact index

Current issue:

- closeout outputs are machine-readable individually, but the bundle does not emit one
  canonical index of all generated paths and hashes.

Safe change:

- emit a deterministic closeout artifact index JSON listing:
  - artifact path,
  - schema_id,
  - sha256,
  - `binding_ref` or `null`,
  - `provenance_ref` or `null`;
- forbid volatile or narrative fields unless they already come from authoritative
  deterministic artifacts.

Preserved invariants:

- individual artifacts remain authoritative;
- the index is only a witness surface over already-emitted artifacts.

### 3. Advisory closeout adjudication checklist

Current issue:

- the semantic closeout layer is repeated from memory across arcs even though its core
  reasoning checkpoints are stable.

Safe change:

- add a lightweight checklist or scaffold for the reasoning layer:
  - lock satisfied,
  - required evidence emitted,
  - assessment converted from pre-lock to post-closeout,
  - cleanup retirements justified,
  - no overclaim in decision language.
- any generated scaffold may pre-structure prompts, headings, and checkpoints only; it must
  not auto-assert closure, retirement, or final gate language.

Preserved invariants:

- the checklist is advisory only;
- it scaffolds thought, not replaces thought.

## Proposed Bundle Shape

This future hardening bundle should stay small and operational.

### Slice `O1`: Closeout orchestration extraction

Goal:

- move closeout artifact-generation glue out of inline decision-doc commands and into one
  deterministic script.

Scope:

- add a repo-owned closeout builder such as
  `apps/api/scripts/build_arc_closeout_bundle.py`;
- accept explicit arc inputs:
  - `--arc`,
  - `--baseline-arc`,
  - required evidence input paths,
  - output roots;
- require all path inputs to resolve inside approved repo roots without expanding authority
  beyond the current closeout lane;
- print or persist the fully resolved execution plan before mutation and fail closed on
  unresolved inputs or outputs.

Acceptance / no-regression proof:

- replay a previously closed arc such as `v53` through both the historical inline
  orchestration path and the extracted builder;
- byte-diff all emitted artifacts and fail on divergence;
- confirm that the builder does not change schema families, slot allowlists, or closeout
  adjudication responsibilities.

Out of scope:

- auto-writing decision/assessment prose;
- auto-retiring cleanup items;
- changing closeout artifact schemas.

### Slice `O2`: Closeout artifact index + lint

Goal:

- make the deterministic closeout output set easier to replay, diff, and lint.

Scope:

- emit one canonical closeout artifact index JSON per arc;
- add a lint script that verifies:
  - listed files exist,
  - listed hashes match file bytes,
  - required schemas/slots named in the index are present.

Acceptance / no-regression proof:

- recompute hashes from the listed files and fail if any index entry diverges from actual
  bytes;
- fail if any required artifact is omitted or any index record includes unauthorized
  volatile fields;
- confirm that the index remains a witness surface only and does not replace artifact-local
  validation.

Out of scope:

- changing stop-gate semantics;
- changing evidence slot allowlists;
- replacing existing artifact-local validation.

### Slice `O3`: Advisory adjudication scaffold

Goal:

- compress repeated closeout reasoning without hiding it.

Scope:

- add a short checklist doc or generated scaffold for closeout adjudication;
- keep it explicitly non-authoritative and non-substitutive.

Acceptance / no-regression proof:

- the scaffold must remain non-authoritative and contain no auto-filled closure claims;
- the scaffold may generate structure/prompts/checkpoints only, never adjudicated
  conclusions;
- compare one scaffold-assisted closeout against a prior high-quality closeout of the same
  class and verify equivalent coverage of lock satisfaction, edge disposition, cleanup
  retirement, and overclaim review.

Out of scope:

- auto-generating post-closeout edge dispositions;
- auto-updating `docs/FUTURE_CLEANUPS.md`;
- auto-approving closeout.

## Suggested Execution Order

1. `O1` first
   - best benefit/risk ratio;
   - removes repeated command re-derivation without touching semantic judgment.
2. `O2` second
   - strengthens machine-readable replay and validation once the builder exists.
3. `O3` third
   - useful, but intentionally lower authority than the first two slices.

## Non-Goals

This proposal does not recommend:

- automating lock-satisfaction judgment;
- automating edge-closure or residual-risk decisions;
- automating cleanup retirement decisions;
- automating the final gate statement;
- hiding closeout commands behind opaque wrappers with no visible execution plan.

## Adoption Rule

This bundle should only be formalized after `v54` closeout is complete on `main`.

Reason:

- `v54` should close under the currently accepted process so the operational hardening work
  has a stable baseline;
- changing the closeout lane before `v54` closes would blur whether a later quality delta
  came from the slice itself or from the process mutation.

## Recommendation

- carry this proposal forward for the next planning turn after `v54` closeout;
- treat it as an operational hardening bundle, not as a semantic/runtime expansion bundle;
- keep the safe optimization boundary explicit:
  deterministic orchestration glue can move into scripts and indexes, but semantic
  adjudication remains reasoning-driven.
