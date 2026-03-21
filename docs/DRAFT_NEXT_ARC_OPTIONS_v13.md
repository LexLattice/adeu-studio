# Draft Next Arc Options v13

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v12.md`.

This draft proposes the next family after the brokered-reflexive execution
baseline: make externally originated or imported single-PR contributions
legible, retrospectively alignable, and structurally checkable under the repo's
current ADEU discipline without pretending they were authored inside the full
native arc sequence.

## Baseline

- `V38-A` established a typed way to compile high-level ADEU/UDEO intent into a
  bounded brokered execution plan.
- The repo already has:
  - strong internal arc discipline through lock, assessment, and decision docs;
  - deterministic local gates through `make check`;
  - closeout and scaffold linting through `lint_arc_bundle.py`,
    `lint_closeout_consistency.py`, and `lint_semantic_compiler_closeout.py`;
  - live evidence that imported external PRs can arrive with partially
    acceptable code but large meta-sequence divergence from repo-native process.

## Gap

The missing layer is not more generic review commentary. The missing layer is a
bounded repo-native conformance lane for imported work that did not originate in
the ADEU harness.

Today the repo lacks a canonical way to:

- classify an imported contribution by lane and structural impact;
- separate code-alignment judgment from meta-sequence judgment;
- record:
  - `claimed_scope`,
  - `observed_reachable_surfaces`,
  - `accepted_shipped_scope`;
- bind maintainer-side follow-up requirements to an accepted imported diff;
- decide whether an imported contribution is precedent-bearing or merely
  accepted after normalization;
- retrospectively align one external PR to the repo's current structural law
  without rewriting history;
- pin the exact policy sources, policy hashes, and evaluator version used to
  derive a canonical conformance report.

## Recommended Family

- Family name: `V39`
- Family theme: external contribution alignment and module conformance
- First path: `V39-A`
- Default path selection:
  select `V39-A` as the next default candidate

## Recommended First Path (`V39-A`)

Implement a bounded, repo-native retrospective-alignment baseline that takes one
imported contribution and turns it into explicit ADEU structure.

The first reference target should be the poetry-utility contribution currently
carried by PR `#293`, treated as an imported single-PR lane rather than as a
native full-arc contribution.

`V39-A` should introduce:

- a canonical `external_contribution_alignment_packet@1`;
- a canonical `module_conformance_report@1`;
- a committed local subject bundle for the imported poetry contribution:
  - materialized diff,
  - materialized metadata,
  - materialized claimed-scope text,
  - any other admissible local evidence;
- a deterministic evaluation path that consumes explicit inputs and current
  repo policy surfaces rather than reviewer prose alone, with pinned policy
  provenance in the emitted evidence;
- one accepted reference packet/report/evidence bundle for the poetry utility
  contribution.

## Why This Path

- It converts a real repo pain point into typed substrate instead of leaving it
  as maintainer folklore.
- It preserves the distinction between internal ADEU-native work and imported
  external work rather than collapsing them into one fake history.
- It gives the repo a first-class way to say:
  - the code is partly or fully acceptable,
  - the process diverged,
  - these follow-ups are required,
  - this contribution is or is not precedent-bearing.
- It makes the normalization trail inspectable by separating:
  - what the contributor claimed,
  - what the repo actually observed,
  - what maintainers accepted as shipped scope.
- It creates the seed of a later generic module-conformance lane without
  prematurely claiming that structural conformance can replace architectural
  judgment.

## First-Slice Boundary

`V39-A` should stay bounded to:

- one imported reference contribution only;
- one localized subject bundle only rather than a live floating PR target;
- explicit structural classification and retrospective alignment artifacts;
- deterministic separation of:
  - code alignment,
  - meta-sequence alignment,
  - claimed scope,
  - observed reachable surfaces,
  - accepted shipped scope,
  - required maintainer follow-ups,
  - precedent status;
- default-negative precedent semantics unless a maintainer explicitly grants
  precedent-bearing status with a reason;
- docs, tests, and light tooling needed to make that first lane real.

It should not attempt:

- a generalized contribution marketplace;
- fully automatic semantic acceptance or rejection of arbitrary modules;
- live GitHub-network dependency in the canonical evaluation path;
- broad contributor-portal UX;
- a repo-wide scoring or ranking engine for all modules in one slice.
