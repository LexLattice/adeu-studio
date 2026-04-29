# Review GPTPro Operator Projection V74 Planning v0

Status: support review capture for the planned `V74` family.

Authority layer: support.

This note captures operator-provided GPTPro review feedback for the initial
`V74` planning bundle. It is not lock authority by itself. It is an integrated
support source for the patched `V74` family planning docs and the future
`vNext+206` starter bundle.

## Verdict Captured

The review approved `V74` as the correct next family after `V73`, with the
central thesis that the repo now needs a governed operator projection and typed
case-view layer that makes decision state legible to a human without turning
visibility into authority.

The review approved the `A` / `B` / `C` split:

- `V74-A`: operator projection case view, projection source index, and
  non-authority guardrail;
- `V74-B`: typed adjudication case view, model-output comparison projection,
  and exception visibility register;
- `V74-C`: decision visibility contract, review/workbench projection,
  post-projection handoff, and family closeout alignment.

The review also confirmed that `packages/adeu_repo_description` remains the
correct starter home because these are repo/corpus projection records, not live
UI, product workbench, command surface, runtime evaluator, dispatch loop, or
release automation.

## Integrated Patches

The review requested these boundary patches before `vNext+206`:

- add minimal `visible_blocker_rows` / exception-summary rows to `V74-A`, so
  blocker visibility is machine-checkable before the `V74-B` exception register
  exists;
- add `projection_horizon` and `visible_authority_state` to keep
  `ready_for_human_review` separate from authority to act;
- require product-pressure cases to carry product-authority-missing or
  equivalent later-authority posture unless rejected or out of scope;
- add source roles for conceptual-diff, product-wedge, model-output, prompt,
  and adjudicator-schema provenance;
- make `comparison_axis_rows` structured in `V74-B`;
- require model-output comparison provenance rows;
- rename `repo_ratification_workbench_projection@1` to
  `repo_ratification_review_workbench_projection@1`;
- split visibility obligations from non-derivable authority kinds in `V74-C`;
- source-bind required later authority through authority requirement rows;
- make `V75` handoff validation strict: non-dispatch guardrail required,
  dispatch authority requirement required, and no ready posture with blocking
  carried exceptions.

## Non-Authority Doctrine Preserved

The review emphasized that `V74` must not authorize:

- `V75` dispatch or multi-worker orchestration;
- `V43` external-world contest participation;
- live product UI or operator command execution;
- product authorization or product-market validation;
- runtime permission;
- commit, PR update, merge, release, or released truth;
- recursive self-approval;
- model-output comparison as benchmark truth.

Those constraints were integrated into the patched support docs and should be
carried into the `vNext+206` starter lock.
