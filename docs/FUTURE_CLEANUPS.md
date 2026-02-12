# Future Cleanups Tracker

This note tracks small follow-up cleanups that are intentionally out of scope for the
current milestone PR sequence.

## Pending

- `cleanup-policy-cli-strictness-defaults`:
  align `policy validate`, `policy eval`, and `policy diff` strictness defaults and
  preserve explicit compatibility flags. This is the separate cleanup PR noted during N2 planning.
- `cleanup-copilot-child-queue-method-extraction`:
  refactor large `URMCopilotManager` methods in
  `packages/urm_runtime/src/urm_runtime/copilot.py` into smaller helpers without behavior
  changes:
  - `_run_child_workflow_v2`
  - `_spawn_child_v2`
  - `_recover_stale_child_runs`
  This was deferred from PR3/PR4 as maintainability-only follow-up work.
