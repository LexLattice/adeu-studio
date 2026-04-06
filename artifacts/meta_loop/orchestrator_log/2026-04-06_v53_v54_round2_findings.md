## Round-2 Findings

This note preserves the main operational and sequencing findings from the second
parallel-pilot run over `V53-A` and `V54-A`.

### Preserved Evidence

- canonical run snapshot:
  - `artifacts/meta_loop/r2/`
- active family-trunk worktrees before run-3 reset:
  - `arc/v53`
  - `arc/v54`

### What Worked

- both family workers produced starter-bundle drafts on their family trunks
- `V54-A` completed a real conceptual review pass with:
  - review artifact
  - reviewer baton
- the baton/orchestrator-log surfaces were sufficient to reconstruct the loop
  without relying on hidden conversational recovery

### What Failed

- first-launch role drift:
  - a worker drifted into governance-summary behavior instead of bounded family
    starter-draft ownership
- `V53-A` reviewer completion failure:
  - reviewer lane did not emit the required review artifact + baton
- starter-bundle structural asymmetry:
  - `V53-A` lacked the preserved first-draft copy of the updated planning doc
- starter-bundle integrity mismatch:
  - `V53-A` stop-gate doc claimed local docs-only gate success
  - `V53-A` worker baton recorded failure caused by the worktree `.git` repo-root
    discovery quirk in `lint_arc_bundle.py`
- imported-prototype starter structure remained too soft:
  - neither family included the slice-specific starter mapping doc that the
    prototype-derived pattern calls for

### Run-3 Hardening Derived From Round 2

- add a pre-review integrity gate before reviewer handoff
- require complete first-draft evidence for every required starter doc
- require reviewer output even on inconsistent starter bundles:
  - use `not_yet_lock_ready`
  - do not silently halt
- separate operational/tooling notes from conceptual blockers
- pre-provision fresh family worktrees with:
  - authoritative `.venv`
  - known worktree-tooling quirk note
- preserve round-2 family trunks under explicit run-suffixed branch names and
  start round 3 from fresh family trunks
