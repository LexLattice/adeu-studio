# Draft Parallel Arc Meta-Loop Protocol v0

Status: working protocol draft only.

Authority layer: support only.

This document does not authorize runtime changes by itself. It captures one bounded
maintainer-side experiment for running two ADEU arc families in parallel under one
governance-first control plane.

This protocol is intentionally narrower than
`docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`. It is not a general multi-role execution
constitution. It is a concrete pilot for two concurrent family lanes.

## Purpose

- separate loop governance from implementation work;
- preserve ADEU docs-first slice discipline inside each family;
- allow parallel progress across two families without using `main` as an implementation
  trunk;
- test whether a self-distilled reviewer role can replicate the practical conceptual
  review posture currently obtained externally;
- preserve enough execution trace that the pilot can later be inspected as empirical
  loop evidence rather than only remembered narratively.

## Pilot Scope

Starter pilot families:

- `V53`
- `V54`

Starter pilot roles:

- one meta-orchestrator on `main`
- one persistent arc worker for `V53`
- one persistent conceptual reviewer for `V53`
- one persistent arc worker for `V54`
- one persistent conceptual reviewer for `V54`

Optional later shared helper:

- one PR/CI janitor role

This pilot does not authorize:

- direct implementation on `main`
- symmetric multi-writer mutation on the same branch
- reviewer self-integration of review findings
- skipping required slice phases because another family is progressing

## Core Governance Rule

`main` is governance-only for this experiment.

That means:

- only the meta-orchestrator touches `main`
- family planning docs, family closeout docs, and final family-to-`main` merge work
  happen under meta-orchestrator control
- implementation work happens in family arc branches and slice branches only

For the pilot, this also means:

- the meta-orchestrator owns the canonical loop log on `main`
- family branches own slice-local working state and intermediate draft artifacts

## Branch Topology

Per family:

- one long-lived arc branch:
  - `arc/v53`
  - `arc/v54`
- one short-lived slice branch per slice, based from the family arc branch
- slice PRs target the family arc branch, not `main`

Family integration:

- each family arc branch is merged to `main` only through a separate maintainer-side
  integration step after the family or chosen family segment is complete enough to
  reconcile drift and conflicts intentionally

This preserves:

- one governance trunk
- two implementation trunks
- explicit final conflict review against `main`

## Role Boundaries

### Meta-Orchestrator

Owns:

- family branch creation
- legal state transitions
- branch/PR/CI governance checks
- family-to-`main` integration
- closeout sufficiency
- canonical loop-log recording and transition ratification

Does not own in steady state:

- drafting starter locks
- code implementation
- conceptual review content

### Arc Worker

Owns one family sequentially.

Owns:

- starter bundle drafting for the assigned slice
- feedback integration
- code implementation
- PR preparation
- review-fix integration
- closeout drafting for the assigned family branch
- preserving the slice-local draft/review/integrated artifact sequence

Does not own:

- governance-state advancement by fiat
- family-to-`main` merge decisions
- conceptual-review authority

### Conceptual Reviewer

Owns one family review lane only.

Owns:

- conceptual review over the starter bundle or implementation diff
- doctrine-fit review
- authority-layer review
- fail-closed and boundary review

Does not own:

- implementation edits
- direct code mutation
- merge or closeout authority

## Per-Family State Machine

Each family moves through this bounded state machine:

1. `starter_draft_pending`
2. `starter_review_pending`
3. `starter_integration_pending`
4. `starter_committed_to_arc_branch`
5. `implementation_pending`
6. `pr_open_against_arc_branch`
7. `inline_review_pending`
8. `review_fixing_pending`
9. `ci_pending`
10. `merge_ready_to_arc_branch`
11. `merged_to_arc_branch`
12. `closeout_pending`
13. `closeout_committed_to_arc_branch`
14. `next_slice_ready`
15. `family_complete_pending_main_merge`
16. `merged_to_main`

Illegal shortcuts include:

- implementing before starter bundle commit
- merging before CI green
- closeout before slice merge
- advancing the family while the baton says the prior slice is still blocked

## Canonical Slice Loop

Per slice, the legal sequence is:

1. arc worker drafts starter bundle on the family arc branch
2. conceptual reviewer reviews that bundle
3. arc worker integrates worthwhile review findings
4. starter bundle is committed on the family arc branch
5. arc worker implements on a slice branch
6. slice PR opens against the family arc branch
7. GitHub inline bot comments and CI are harvested
8. arc worker applies worthwhile review fixes
9. slice PR merges into the family arc branch once green
10. arc worker drafts closeout on the family arc branch
11. meta-orchestrator verifies the baton and advances to next slice

## Evidence Preservation Rule

This pilot should preserve the sequence itself as inspectable evidence.

At minimum, each slice should retain distinct artifacts for:

- starter first draft
- conceptual review output
- integrated starter bundle

These may be preserved either as:

- committed docs on the family arc branch; or
- explicit support artifacts under a canonical meta-loop evidence path

The purpose is diagnostic:

- later analysis should be able to compare what changed between draft, review, and
  integration
- the pilot should not collapse those stages into one final lock artifact only

## Review Doctrine

The conceptual reviewer is intended to emulate the best current external conceptual
review posture, not generic code review.

The reviewer must prioritize:

- authority-layer fit
- doctrinal fit relative to ADEU planning/lock posture
- fail-closed semantics
- schema/contract sharpness
- under-specified mapping laws
- evidence/status mismatches
- starter-slice boundedness

The reviewer may not:

- widen the selected slice casually
- propose implementation details that contradict the controlling lock
- silently promote planning language into lock-level prohibition

## Baton Requirement

Every role handoff must emit one baton JSON document matching:

- `docs/PARALLEL_ARC_META_LOOP_BATON_v0.json`

The baton is the only accepted transition claim surface for this pilot.

Self-reported completion without baton state is non-authoritative.

For the pilot, baton semantics are split minimally into:

- transition claim:
  emitted by worker/reviewer/helper roles
- transition ratification:
  emitted by the meta-orchestrator after checking the claim

This is intentionally lighter than a full runtime constitution, but it prevents the
pilot from collapsing worker claims and governance acceptance into one artifact.

## Canonical Storage

The pilot should use one canonical evidence root:

- `artifacts/meta_loop/`

Recommended layout:

- `artifacts/meta_loop/orchestrator_log/`
- `artifacts/meta_loop/<family>/<slice>/batons/`
- `artifacts/meta_loop/<family>/<slice>/starter_bundle/`
- `artifacts/meta_loop/<family>/<slice>/review/`

The orchestrator log should be append-oriented and reconstructable, so later analysis
can inspect:

- what transition was claimed
- what transition was ratified
- what evidence was cited
- what branch/PR/CI state existed at that moment

## Governance Revision Rule

For the first pilot:

- protocol/prompt/baton docs should stay frozen within a slice once that slice enters
  `starter_review_pending`
- if an emergency correction is required mid-slice, the meta-orchestrator must log it
  explicitly as a governance override event
- normal protocol improvements should be queued to the next slice boundary

This intentionally leaves room for error while still making mid-run redesign visible
rather than ambient.

## Readiness Gates

The meta-orchestrator should verify, at minimum:

Before implementation:

- controlling starter bundle exists
- reviewer baton exists
- integration baton exists
- starter commit is present on the family arc branch
- distinct starter draft/review/integrated artifacts are preserved

Before PR merge:

- PR targets the family arc branch
- required local checks were run and recorded
- CI is green
- review-fix baton exists if inline comments were present

Before family merge to `main`:

- intended family segment is closed on the family branch
- family branch closeout docs are committed
- conflict review against `main` is performed explicitly

Cross-family preflight:

- if two live families touch the same authoritative package, schema family, or
  generated artifact space, the meta-orchestrator must log the declared collision
  posture before both proceed in parallel

## Validation Posture

This pilot is successful if it demonstrates:

- parallel family progress without losing docs-first discipline
- reviewer/worker separation without major loop drift
- baton-governed state transitions that are auditable after the fact
- manageable `main` integration from family branches

This pilot fails if it demonstrates:

- repeated illegal state shortcuts
- reviewer/worker role collapse
- uncontrolled drift between family branches and `main`
- baton output too weak to govern transitions reliably

## Deferred Pilot Hardening

The first experiment intentionally does not yet freeze a full constitutional execution
contract.

The following items are explicitly deferred to later pilot hardening after the first
empirical run produces analyzable loop evidence:

- full phase-conditional baton legality matrix
- full claim-versus-ratification constitution beyond the starter split used here
- strict governance-version pinning per slice and per family
- fully typed reviewer-output schema beyond the current structured prompt posture
- richer cross-family collision taxonomy beyond the preflight rule used here
- automated baton validation beyond JSON/schema shape and orchestrator-side review

So the first pilot should be read as:

- strong enough to preserve sequence and governance visibility
- intentionally loose enough to leave room for observable failure modes
- not yet the final multi-role execution constitution
