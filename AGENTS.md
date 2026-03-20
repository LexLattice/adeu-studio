# Repo Local Guidance

## Python Environment

- Treat `.venv` as the authoritative Python environment for this repo.
- Prefer `make bootstrap`, `make check`, `make test`, `make lint`, and `make format` over raw `python`, `pytest`, or `ruff` commands.
- If you need to run Python directly, use `.venv/bin/python` and `.venv/bin/pip`.
- Do not create alternate virtual environments unless `.venv` is missing or broken.

## Pre-PR Gate

- Before opening or updating a Python PR, run `make check`.
- `make check` is the default local gate for the Python lane and includes:
  - Ruff lint
  - pytest
  - closeout consistency lint
  - semantic compiler closeout lint
  - generated instruction policy doc check
- If you intentionally run a narrower subset instead of `make check`, state what was skipped.

## Docs-Only Arc Bundles

- For docs-only arc starting-bundle work, use `make arc-start-check ARC=<n>`.
- For docs/artifacts-only arc closeout bundle work, use `make arc-closeout-check ARC=<n>`.
- These shortcuts are only for diffs limited to arc planning/closeout docs and committed
  closeout artifacts; they are not a replacement for `make check` when Python source,
  tests, `Makefile`, CI, or lint scripts change.
- `make arc-start-check` runs the arc-bundle scaffold lint plus the generated instruction
  policy doc check.
- `make arc-closeout-check` runs the arc-bundle closeout lint, closeout consistency lint,
  semantic closeout lint, committed URM event-stream validation for that arc bundle, and
  the generated instruction policy doc check.
- If you intentionally use an arc-bundle shortcut instead of `make check`, say that the
  full Python lane was skipped because the change was docs/artifacts only.

## Contribution Taxonomy

- Keep two contribution lanes distinct:
  - `Internal ADEU lane`: repo-owned work, core architectural changes, schema changes,
    workflow changes, and orchestrated experiments. Default expectation is the
    repo-native ADEU flow: pre-docs or explicit intent capture, implementation,
    verification, and post-doc or closeout alignment where applicable.
  - `External single-PR lane`: outside contributions or imported Codex-produced diffs
    that did not originate inside the repo harness. These may arrive without the full
    ADEU arc bundle, but they do not replace the internal lane or set precedent by
    themselves.
- Review external PRs on two separate axes:
  - code alignment with in-repo ADEU engineering practice
  - meta-sequence alignment with repo workflow and documentation discipline
- A strong code diff does not erase meta-sequence divergence. Missing pre-docs,
  post-docs, tests, or evidence should be called out explicitly and handled through
  maintainer-side alignment post-processing.

## External Single-PR Lane

- External PRs are allowed to be structurally lighter than internal ADEU arc work.
- Minimum expectations for an external PR:
  - include a short intent note in the PR body or handoff message covering the problem,
    touched surfaces, and non-goals
  - keep the change bounded; avoid mixing feature work with unrelated workflow or
    governance edits
  - if a new runtime behavior is claimed, wire it to a reachable product surface or
    state clearly that the contribution is internal-only utility work
  - add or update tests for the changed behavior, or explain the gap and risk plainly
  - preserve fail-closed validation posture; do not silently repair malformed model,
    tool, or schema output into apparent success
  - state the checks actually run, especially when narrower than `make check`
- External PRs that introduce a new schema, a new externally reachable surface, or a
  cross-cutting workflow change should usually be treated as maintainership handoff
  candidates rather than merged as raw single-PR contributions.
- See `docs/DRAFT_EXTERNAL_CONTRIBUTION_ALIGNMENT_v0.md` for the maintainer-side
  normalization path.

## Reflexive Orchestration Experiments

- When a task is explicitly framed as a repo-internal orchestration experiment,
  prefer compiling the high-level intent into typed ADEU artifacts before
  widening implementation scope.
- If sub-agents are used for such an experiment, keep recommended child models
  within:
  - `gpt-5.4`
  - `gpt-5.3-codex`
  - `gpt-5.4-mini`
- Recommended child reasoning effort for that workflow should remain `xhigh`.
- Treat adversarial feedback and code review as explicit delegated phases, not
  optional commentary.

## Maintainer Alignment Post-Processing

- Accepted external PRs should be normalized into repo-native ADEU structure by a
  maintainer either before merge or in an immediate follow-up maintainer PR.
- The maintainer-side alignment step should:
  - classify the external contribution by scope and contract impact
  - record the meta-sequence gap separately from the code-quality judgment
  - add missing tests, evidence, or surface wiring where the external PR over-claims
    what it ships
  - decide whether the accepted work needs arc docs, a continuation lock, a decision
    note, an assessment, or only a narrow follow-up note
  - avoid treating imported external diffs as process precedent until the alignment
    step is complete
- Use `docs/DRAFT_EXTERNAL_CONTRIBUTION_ALIGNMENT_v0.md` as the working reference for
  that post-processing flow.
