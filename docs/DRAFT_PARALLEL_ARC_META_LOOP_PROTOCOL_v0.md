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

Implementation-worker launch reference for the pilot:

- `docs/DRAFT_PARALLEL_ARC_IMPLEMENTATION_WORKER_PROMPT_v0.md`
- `docs/PARALLEL_ARC_IMPLEMENTATION_STAGE_REPORT_TEMPLATE_v0.json`

Starter-worker launch reference for the pilot:

- `docs/DRAFT_PARALLEL_ARC_STARTER_WORKER_PROMPT_v0.md`

Model restriction for the pilot:

- baseline sub-worker and reviewer posture is `gpt-5.4` with reasoning effort
  `xhigh`
- explicit model-comparison runs may instead use `gpt-5.3-codex` with reasoning
  effort `xhigh`, but only when the orchestrator logs that variance test explicitly
- do not mix worker models casually inside one run without logging the reason

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
- finishing the full implementation contract for the assigned slice rather than
  stopping at exploratory or partial package mutation

Does not own:

- governance-state advancement by fiat
- family-to-`main` merge decisions
- conceptual-review authority

The arc worker may not claim implementation completion while any required contract
surface for the slice is still missing, red, or only partially wired.

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
6. slice PR opens as a full PR against the family arc branch
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

## Implementation Three-Stage Law

For the pilot, the implementation phase should be split into three explicit stages:

1. semantic-IR bridge
2. code transposition
3. verification and attestation

The purpose of stage 1 is to materialize the code-facing reasoning bridge between the
starter lock/mapping contract and the intended code surfaces. The worker should not
leave that bridge implicit inside model reasoning alone.

For the pilot, this semantic-IR artifact should be treated as the authoritative
implementation-lowering artifact for the slice. Stage 2 and stage 3 should conform to
it unless an explicit mapping change is recorded in the stage-end artifacts with a
reason.

### Stage 1: Semantic-IR Bridge

The worker should produce one bounded semantic-IR artifact that names:

- the exact slice lock and slice mapping docs being implemented
- the exact contract names or schema ids being introduced
- the exact contract item -> planned package file/module ownership mapping
- the required authoritative schema exports and root `spec/` mirrors, if the lock
  selects released contracts
- the exact contract item -> planned deterministic fixture/test/check mapping
- the explicit non-goals and deferred seams that must remain out of scope

This stage may also include pseudocode, function/class skeletons, or a package/file
plan, but it should remain meta-code rather than live implementation.

### Stage 2: Code Transposition

The worker should transpose the semantic-IR bridge into live code by materializing:

- required package code surfaces
- required schema export surfaces
- required root `spec/` mirrors
- required deterministic fixtures/tests
- required package wiring

The stage-2 worker should judge its own completion first against the semantic-IR bridge
and only secondarily against the higher-level starter contract. If the worker changes
the semantic-IR mapping during transposition, it should record:

- which contract item changed
- what code/test/export surface changed
- why the original lowering was changed
- whether the change leaves any new deferred or extra surface

### Stage 3: Verification And Attestation

The worker should run the bounded targeted checks selected by the finish line and then
emit:

- one stage-end self-report for verification
- one final implementation baton

The implementation baton remains the authoritative completion claim for the phase.

The verification stage should compare the final code both to:

- the starter lock and slice mapping contract
- the stage-1 semantic-IR bridge

The worker should explicitly surface any:

- contract items that were promised in semantic-IR but not implemented
- implemented surfaces that were not declared in semantic-IR
- planned checks from semantic-IR that were not actually run

### Stage-End Reporting

At the end of each implementation stage, the worker should emit one machine-checkable
stage report using:

- `docs/PARALLEL_ARC_IMPLEMENTATION_STAGE_REPORT_TEMPLATE_v0.json`

The stage report should map contract items to concrete code/test/export surfaces so the
orchestrator can inspect compliance without reconstructing the worker's hidden
reasoning.

The stage report should also carry enough structure to answer:

- what code surfaces each contract item lowered into
- what checks each contract item was expected to receive
- which seams were explicitly deferred or declared as non-goals
- whether stage 2 changed the semantic-IR lowering and why
- whether stage 3 found any extra or unmapped surfaces

### Completion Law

Implementation completion is satisfied only when:

- the semantic-IR bridge exists
- the semantic-IR bridge is treated as the implementation-lowering reference unless a
  justified mapping change is recorded
- the required live package surfaces exist and are coherent
- the required schema exports exist under the package schema directory
- the required root `spec/` mirrors exist
- the required deterministic fixtures/tests for the slice exist
- the bounded targeted checks for the owned package lane pass
- the worker emits one final implementation baton with:
  - changed files
  - checks run
  - checks skipped
  - blockers
  - semantic-IR conformance statement
  - semantic-IR mapping changes, if any
  - readiness judgment

Implementation completion is not satisfied by:

- a partial package diff
- only adding models without schema export surfaces when the lock requires contract
  release
- only adding helpers without fixtures/tests
- red targeted checks
- silently diverging from the semantic-IR bridge during implementation
- passing targeted checks while leaving promised semantic-IR surfaces unimplemented
- a narrative status message without the stage-end artifacts
- a narrative status message without the baton

If a worker is handed a partial implementation state on a slice retry, the worker
must finish that state or fail loudly against the missing finish-line items; it may not
quietly restart the slice from scratch unless the orchestrator explicitly authorizes
that reset.

If targeted tests reveal released-surface drift inside the slice's owned package lane
for the bounded contract, the worker should repair that drift inside the slice rather
than reporting a partial completion.

### Interruption Rule

The meta-orchestrator should not interrupt a worker routinely inside an implementation
stage.

Normal deep work inside a coding stage is not itself drift.

Interruption during implementation should be reserved for significant drift such as:

- no material `O` artifact at the expected stage boundary
- writes outside the allowed scope
- explicit blocked state
- doctrinal widening against the controlling lock
- repeated refusal to cross from stage contract to required stage artifact

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

## Implementation Retry Recovery Rule

If a slice implementation worker stops mid-slice and leaves only partial code:

- preserve the partial diff as pilot evidence before relaunch
- do not overwrite the failed state in place without an evidence record
- relaunch from the committed family-trunk starter baseline on a fresh retry slice
  branch unless the orchestrator explicitly chooses a different recovery posture
- the retry prompt must name the concrete misses from the failed attempt

If the worker repeatedly fails to cross from semantic-IR to live code mutation, prefer
sharpening the implementation contract and stage-end self-reporting rather than
pre-materializing live code stubs too early.

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

Implementation PR policy for this pilot:

- implementation PRs are opened as full PRs, not drafts
- a draft PR is a process deviation, not a neutral equivalent state
- if a PR is accidentally opened as draft, the orchestrator should either:
  - convert it to ready-for-review immediately; or
  - explicitly log the manual bot-trigger fallback it had to use because of the draft
    posture

### Witness Surfaces

Primary witness surfaces on the PR:

- bot-authored parent review comments
- bot-authored inline review comments or review-thread descendants

Fallback witness surface on the PR:

- reactions on the main PR body/comment

### Terminal Witnesses

For `codex`, the accepted terminal witnessed states are:

- `completed_with_findings`
  - primary witness:
    - one parent review comment titled `Codex Review`; and
    - one or more subordinate inline findings or review-thread comments
- `completed_no_findings`
  - fallback witness when no parent review comment exists:
    - replacement of the prior `eyes` reaction with a `thumbs_up` reaction on the main
      PR body/comment

For `gemini`, the accepted terminal witnessed states are:

- `completed_with_findings`
  - primary witness:
    - one Gemini-authored parent review comment titled `Code Review`; and
    - one or more subordinate inline findings or review-thread comments
- `completed_no_findings`
  - primary witness:
    - one Gemini-authored parent review comment titled `Code Review` whose body
      explicitly states that no feedback is being provided

If the relevant parent review comment exists, it is the primary witness of pickup and
terminal completion. The orchestrator should then inspect inline findings beneath it
rather than re-deriving completion from reactions.

### Per-Bot Pickup Witness

Only when the relevant parent review comment is absent, inspect reactions.

For both `codex` and `gemini`, pickup-in-progress is then witnessed by:

- an `eyes` reaction on the main PR body/comment from that bot

This means the bot has picked up the review task and is still working.

### Non-Pickup Witness

A required bot is `not_picked_up` only when:

- the 5-minute post-PR-open wait has elapsed; and
- there is still no parent review comment witness from that bot; and
- there is still no reaction witness from that bot on the PR

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

For strict step-checkpoint runs, the baton should also carry:

- `execution_template_ref`
- `template_step_id`
- `template_step_order`
- `claimed_step_complete`
- `continuation_required_before_next_step`

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

## Machine-Checkable Execution Templates

For diagnostic runs where fidelity is more important than speed, the pilot may switch a
slice into strict step-checkpoint mode.

In that mode, the worker must follow one explicit machine-checkable template exactly.

Canonical template refs for the current pilot are:

- `docs/PARALLEL_ARC_STARTER_BUNDLE_EXECUTION_TEMPLATE_v0.json`
- `docs/PARALLEL_ARC_IMPLEMENTATION_EXECUTION_TEMPLATE_v0.json`
- `docs/PARALLEL_ARC_REVIEW_FIX_EXECUTION_TEMPLATE_v0.json`
- `docs/PARALLEL_ARC_CLOSEOUT_EXECUTION_TEMPLATE_v0.json`

Each template step must define:

- `step_id`
- `step_order`
- `required_inputs`
- `required_outputs`
- `success_predicate`
- `required_checks`
- `forbidden_shortcuts`
- `next_step_if_pass`
- `escalate_if_fail`

The template is not descriptive only. In strict step-checkpoint mode it becomes the
required execution order for the assigned role.

## Strict Step-Checkpoint Mode

When the orchestrator enables strict step-checkpoint mode for a slice:

- the worker may execute only the currently authorized template step
- each material template step should use a fresh worker instance by default,
  especially for drafting-heavy steps
- after completing that step, the worker must emit one baton naming the template ref
  and current step id/order
- the worker must then stop and wait for explicit orchestrator continuation before
  beginning the next template step
- the orchestrator must verify the claimed outputs before authorizing the next step
- the worker may not self-advance merely because the next step looks obvious

The purpose is diagnostic rather than throughput-oriented:

- isolate where procedural drift happens
- separate “did work” from “completed the correct step”
- make partial compliance visible at the step level

In this mode, the baton semantics become:

- worker baton:
  - exact step-complete claim only
- orchestrator baton:
  - exact step-ratification or step-rejection only

If a step fails:

- the worker should stay blocked on that step
- the baton should name the unsatisfied outputs or failed checks
- the orchestrator should either:
  - authorize repair on the same step; or
  - halt the slice and log the failure as evidence

The worker may not silently skip ahead to later cleanup or compensating edits.

## Drafting-Step Start Law

For strict-mode drafting steps:

- the prompt should name the exact files to create or update
- if the step is meant to create files, the first next write action should be
  `apply_patch`
- exploratory searches for local conventions or historical examples are not assumed
  lawful once the step has been authorized
- if the worker uses exploratory tools before the required files exist, the
  orchestrator should treat that as a step-compliance failure rather than harmless
  progress

The pilot evidence so far shows a recurring `read more before writing` loop. This rule
exists to make that loop visible and actionable rather than tolerating it as partial
progress.

## Contradiction Recording Law

If a worker encounters a real doc mismatch during a step that is not authorized to
repair that mismatch yet:

- record the mismatch in the required step artifact
- do not widen the step into extra repo research or self-directed reconciliation
- do not silently repair the mismatch unless the step explicitly owns that repair

This keeps contradiction-bearing steps from drifting into reviewer-like behavior when
the assigned task is only to checkpoint or boundedly draft.

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

- semantic-IR stage report exists
- code-transposition stage report exists
- final implementation baton exists

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
