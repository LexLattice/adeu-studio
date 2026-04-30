# Review GPTPro Dispatch Review V75 Planning v0

Status: support review captured from external GPTPro feedback on the initial
`V75` planning bundle.

Authority layer: support.

This support note records review conclusions and patch requirements for the
planned `V75` dispatch-review family. It is not a selector, lock, starter
bundle, implementation authority, runtime authority, product authority, release
authority, external contest authority, or recursive policy authority.

## Verdict

The review approves `V75` as the correct next family and approves the initial
bundle as a strong support-review bundle.

The approved family boundary is:

- make dispatch pressure, multi-worker orchestration posture, worker IO, tool
  applicability, exception visibility, and reconciliation reviewable;
- do not execute dispatch, assign workers, run commands, authorize runtime /
  product / release / external-contest actions, or treat worker output as
  truth.

The review also approves the `A` / `B` / `C` lane structure:

- `V75-A`: dispatch-review request, source index, non-execution guardrail;
- `V75-B`: worker role, assignment plan, IO, tool applicability, exception
  posture;
- `V75-C`: projected / observed output reconciliation plan, reconciliation
  contract, post-dispatch-review handoff, family closeout alignment.

The bundle should remain support / planning until the canonical `vNext+209`
starter trio exists. Only `V75-A` should be selected for the first active slice.

## Required Patch Set

The review requests these patches before `LOCKED_CONTINUATION_vNEXT_PLUS209.md`
is activated:

- distinguish source context from eligibility source: roadmap and support docs
  may contextualize `V75`, but `eligible_for_dispatch_review` must require
  concrete released `V74-C` substrate;
- make carried exceptions first-class in `V75-A` as upstream `V74-C` exception
  refs until the native `V75-B` exception register exists;
- define row-shaped `required_later_authority_rows`;
- add `assignment_execution_posture = no_execution_authorized` to `V75-B`
  assignment plans;
- separate tool applicability from tool-use permission with `tool_use_posture`;
- rename or constrain `external_review_worker` as external-branch review only;
- split projected output slots from observed worker outputs in `V75-C`;
- add `handoff_subject_horizon` so `future_outcome_review` cannot imply hidden
  dispatch execution;
- require blocking exceptions to prevent `ready_for_later_review`, except when
  the handoff is specifically a blocker-settlement / arbiter-review request;
- state that the `V75` bundle supersedes the roadmap placeholder names
  `repo_worker_output_reconciliation_record@1` and
  `repo_post_dispatch_outcome_review_handoff@1`.

## Non-Authority Boundary

The review explicitly preserves these non-selected surfaces:

- no `V75-B` or `V75-C` activation under the `V75-A` starter lock;
- no worker assignment;
- no command execution;
- no runtime permission;
- no product authorization;
- no external contest participation;
- no PR / commit / merge / release;
- no benchmark truth;
- no model selection;
- no living-memory authority;
- no recursive policy amendment.

## Recommended Starter Scope

The recommended `vNext+209` starter should select only:

- `packages/adeu_repo_description/src/adeu_repo_description/dispatch_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/schema/repo_dispatch_review_request.v1.json`
- `packages/adeu_repo_description/schema/repo_dispatch_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_dispatch_non_execution_guardrail.v1.json`
- `spec/repo_dispatch_review_request.schema.json`
- `spec/repo_dispatch_source_index.schema.json`
- `spec/repo_dispatch_non_execution_guardrail.schema.json`
- `packages/adeu_repo_description/tests/test_dispatch_review_v75a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`
- `apps/api/fixtures/repo_description/vnext_plus209/` reference and reject
  fixtures for `V75-A`.
