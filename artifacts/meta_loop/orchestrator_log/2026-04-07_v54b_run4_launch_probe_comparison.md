## V54-B Run-4 Launch Probe Comparison

Date: 2026-04-07

Scope: diagnose why the `V54-B` implementation worker repeatedly failed to begin
meaningful work on `v144-v54b-history-ledger-theme-impl-r4-retry1`.

### Probe Matrix

1. Minimal probe on clean retry branch with `fork_context=true`
   - result: no observable filesystem effect before timeout
   - witness: no new diagnostic file, no baton, no package diff

2. Minimal probe on clean retry branch with `fork_context=false`
   - result: success
   - witness:
     - `artifacts/meta_loop/V54/V54-B/diagnostics/launch_probe_round2_minimal.md`
     - `artifacts/meta_loop/V54/V54-B/batons/006_arc_worker_launch_probe_claim.json`

3. Controlled A/B probe on two fresh diagnostic branches from `arc/v54-r4`
   - `diag/v54b-launch-fork-r4` with `fork_context=true`
     - result: no completion, no probe files written after two wait windows
   - `diag/v54b-launch-nofork-r4` with `fork_context=false`
     - result: success
     - witness:
       - `/home/rose/work/LexLattice/odeu_v144_v54b_diag_nofork/artifacts/meta_loop/V54/V54-B/diagnostics/launch_probe_round3_nofork.md`
       - `/home/rose/work/LexLattice/odeu_v144_v54b_diag_nofork/artifacts/meta_loop/V54/V54-B/batons/007_arc_worker_launch_probe_claim.json`

4. Real `V54-B` implementation retry on live retry branch with `fork_context=false`
   - result: success
   - early witness:
     - `artifacts/meta_loop/V54/V54-B/diagnostics/implementation_checkpoint_round3.md`
   - implementation witness:
     - `artifacts/meta_loop/V54/V54-B/batons/007_arc_worker_implementation_claim.json`
     - package/source/test/schema diffs under `packages/adeu_history_semantics/` and `spec/`
   - independent verification:
     - `PYTHONPATH=packages/adeu_history_semantics/src:packages/adeu_ir/src .venv/bin/python -m ruff check packages/adeu_history_semantics`
     - `PYTHONPATH=packages/adeu_history_semantics/src:packages/adeu_ir/src .venv/bin/python -m pytest packages/adeu_history_semantics/tests -q`
     - result: `21 passed`

### Working Conclusion

The dominant launch defect for this slice is not the package, branch, or worktree.
The strongest available explanation is inherited-context launch instability:

- `fork_context=true` repeatedly stalled before first patch
- `fork_context=false` consistently reached the branch
- `fork_context=false` plus an explicit early checkpoint requirement was sufficient
  for full slice implementation

### Practical Follow-On Rule

For greenfield implementation slices in this pilot:

- prefer `fork_context=false`
- provide the worker with explicit controlling file paths and a bounded finish line
- require one early checkpoint artifact before the first substantive code pass
- do not interrupt early if the checkpoint lands and package files begin changing
