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

Model restriction for the pilot:

- all sub-workers and reviewers use `gpt-5.4`
- all sub-workers and reviewers use reasoning effort `xhigh`
- no other child model is used during the first experiment

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
7. wait 5 minutes, then inspect the explicit GitHub bot-review witnesses for Codex and
   Gemini
8. if either required bot has not picked up the PR, follow the manual-trigger rule
9. once both required bots reach a terminal witnessed state, harvest and classify any
   inline findings
10. arc worker applies worthwhile review fixes
11. push the review-fix update to the same PR branch
12. wait 5 minutes, then verify CI is green
13. slice PR merges into the family arc branch once green
14. arc worker drafts closeout on the family arc branch
15. meta-orchestrator verifies the baton and advances to next slice

## Pre-Review Integrity Gate

Before a starter bundle is handed to a conceptual reviewer, the meta-orchestrator
should verify at minimum:

- the expected starter-doc set exists:
  - lock
  - stop-gate
  - assessment
  - updated family planning doc
- required starter support docs for that slice exist if the family pattern calls for
  them:
  - for imported-prototype-derived slices, include the slice-level starter mapping doc
    if selected by that family pattern
- first-draft evidence copies are present for every required starter doc
- the worker baton and the starter stop-gate doc do not materially contradict each
  other on claimed local validation status

If that integrity gate fails:

- the family remains in `starter_integration_pending`
- the reviewer should not be treated as the primary repair surface for missing starter
  structure

The 5-minute waits are deliberate pilot rules, not suggestions:

- after PR open, wait 5 minutes before checking Codex/Gemini review witnesses
- after pushing review fixes, wait 5 minutes before deciding CI readiness

If the first check occurs before the signal is complete:

- continue polling at 30-second intervals until the relevant bot-review or CI state is
  complete enough to trust

## GitHub Bot Review Witness Model

For this pilot, the required GitHub inline review bots are:

- `codex`
- `gemini`

The bot-review step is not atemporal. It may not be discharged by a single empty query
against review threads or review comments.

The meta-orchestrator must inspect explicit witnesses for each required bot.

### Witness Surfaces

Primary witness surfaces on the PR:

- reactions on the main PR body/comment
- bot-authored parent review comments
- bot-authored inline review comments or review-thread descendants

### Per-Bot Pickup Witness

For both `codex` and `gemini`, pickup-in-progress is witnessed by:

- an `eyes` reaction on the main PR body/comment from that bot

This means the bot has picked up the review task and is still working.

### Terminal Witnesses

For `codex`, the accepted terminal witnessed states are:

- `completed_no_findings`
  - witnessed by replacement of the prior `eyes` reaction with a `thumbs_up` reaction
    on the main PR body/comment
- `completed_with_findings`
  - witnessed by:
    - one generic/header parent comment from Codex; and
    - one or more subordinate inline findings or review-thread comments

For `gemini`, the accepted terminal witnessed states are:

- `completed_no_findings`
  - witnessed by one Gemini-authored parent comment explicitly stating that no issues
    were found
- `completed_with_findings`
  - witnessed by:
    - one generic/header parent comment from Gemini; and
    - one or more subordinate inline findings or review-thread comments

### Non-Pickup Witness

A required bot is `not_picked_up` only when:

- the 5-minute post-PR-open wait has elapsed; and
- there is still no reaction or comment witness from that bot on the PR

Absence of review threads alone is not sufficient evidence of `not_picked_up`.

### Manual Trigger Rule

If `codex` is still `not_picked_up` after the initial 5-minute wait, the
meta-orchestrator should trigger it manually by commenting:

- `@codex review`

After that manual trigger:

- wait another 5 minutes
- then resume witness polling at 30-second intervals until Codex reaches a terminal
  witnessed state or the orchestrator explicitly logs an unresolved bot-outage posture

Gemini manual-trigger behavior is not frozen by this first pilot. If Gemini does not
pick up a PR, the orchestrator must log that explicitly rather than silently treating
Gemini as complete.

### Review-Step Discharge Law

The GitHub bot-review step is complete only when each required bot is in one of:

- `completed_no_findings`
- `completed_with_findings`
- explicitly logged unresolved outage posture accepted by the meta-orchestrator

So the orchestrator may not conclude:

- `no reviews were present`

unless the relevant terminal witness for each required bot has actually been observed.

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

Reviewer completion law for the pilot:

- the reviewer must always emit:
  - one review artifact
  - one reviewer baton
- bundle inconsistency or incompleteness should normally produce:
  - `not_yet_lock_ready`
  rather than silent reviewer halt
- operational/tooling quirks should be recorded as operational notes unless they are
  genuinely the main conceptual blocker in the reviewed slice

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

For PR-phase batons, the relevant bot-review witness fields should be populated when
applicable, especially during:

- `pr_open_against_arc_branch`
- `inline_review_pending`
- `review_fixing_pending`
- `ci_pending`

## Canonical Storage

The pilot should use one canonical evidence root:

- `artifacts/meta_loop/`

Recommended layout:

- `artifacts/meta_loop/orchestrator_log/`
- `artifacts/meta_loop/<family>/<slice>/batons/`
- `artifacts/meta_loop/<family>/<slice>/starter_bundle/`
- `artifacts/meta_loop/<family>/<slice>/review/`
- `artifacts/meta_loop/r<run_number>/` for preserved run snapshots when the same pilot
  family is relaunched on fresh branches

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

## Worktree Preflight Rule

Before a family slice begins on a fresh worktree, the meta-orchestrator should prepare:

- authoritative `.venv` availability in that worktree
- canonical meta-loop evidence directories for that family/slice
- one explicit note if known docs-only helper tooling is not yet worktree-clean

Known pilot quirk already observed:

- `apps/api/scripts/lint_arc_bundle.py` currently does not accept the worktree `.git`
  file layout as repository-root evidence

That quirk should be:

- logged explicitly
- treated as an operational note
- not rediscovered ad hoc by every worker/reviewer as if it were a family-specific
  blocker

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
- the 5-minute bot-review witness wait rule was honored
- Codex bot state is terminally witnessed or explicitly escalated
- Gemini bot state is terminally witnessed or explicitly escalated
- the 5-minute post-fix CI wait rule was honored or explicitly escalated in the log

Before family merge to `main`:

- intended family segment is closed on the family branch
- family branch closeout docs are committed
- conflict review against `main` is performed explicitly

Cross-family preflight:

- if two live families touch the same authoritative package, schema family, or
  generated artifact space, the meta-orchestrator must log the declared collision
  posture before both proceed in parallel

## Merge Governance Note

Review-rule bypass is not assumed by default in this pilot.

For slice PRs against family arc branches:

- merge without bypass if the branch policy allows it
- use review-rule bypass only if the repository policy actually requires it and the
  meta-orchestrator records the reason explicitly in the loop log

For family-to-`main` integration:

- any required bypass decision is always a meta-orchestrator governance action
- the orchestrator log must record:
  - whether bypass was needed
  - why it was needed
  - which checks were green at the time

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
