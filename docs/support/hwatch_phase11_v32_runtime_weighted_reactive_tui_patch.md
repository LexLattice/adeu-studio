# hwatch Phase 11 Run 2 Review And v32 Runtime-Weighted Reactive-TUI Patch

Authority layer: `post_eval_pressure_synthesis` + `meta_program_patch_proposal`.

Task:

```text
blacknon__hwatch.edfcb62
```

Controlling audit:

```text
phase11_run2_full_visibility_failure_audit.md
```

## 1. Core Verdict

The audit is correct, but its most important implication should be promoted from
“repair the remaining failure buckets” to a stronger meta-program invariant:

```text
For reactive / TUI / timeout-heavy programs, once result-artifact liveness is
repaired, the next gating object is runtime-weighted semantic closure.
```

Run 2 is materially better than Run 1 because every branch produced readable
results:

```text
score:        62
passed:       913
failed:       408
not_run:      0
total rows:   1321
branch error: none
duration:     about 57m20s
```

So the earlier `results_read_failed` problem is no longer masking the product
surface. The failures are now usable as product/test-surface evidence. But the
run is still not operationally healthy as an iteration loop because one branch
is both semantically dominant and runtime-dominant:

```text
branch 4764369abc4f:
  102 passed
  309 failed
```

The key diagnosis is therefore two-layered:

```text
Layer A: product ontology is now visible.
Layer B: evaluator/runtime feedback is too slow to drive ordinary patch loops.
```

That means the next transition is not simply:

```text
official failures -> patch TUI behavior
```

It must be:

```text
official failures
  -> runtime-weighted attribution
  -> timeout-amplifier separation
  -> fast-fail and command-boundary repair
  -> targeted subtree harnesses
  -> only then full official eval
```

## 2. What The Audit Got Right

### 2.1 Full visibility was restored

Run 1 had a branch-level result-read failure. Run 2 has no `not_run` rows and no
branch errors. That means the liveness repair should be considered real.

However, the fixed liveness condition should not be mistaken for a healthy
feedback loop. It changed the failure class from:

```text
branch result artifact unreadable
```

to:

```text
branch result artifact readable but expensive to produce
```

So the earlier gate:

```text
BRANCH_RESULT_ARTIFACT_LIVENESS_GATE
```

is satisfied, but a new gate is needed:

```text
BRANCH_RUNTIME_BUDGET_GATE
```

### 2.2 Failure count and runtime cost disagree

The high-count groups are led by keymap gaps, edge cases, pane navigation,
keymaps, ANSI, output gaps, batch, watch pane, exec, history, and boolean flag
parsing. But the high-runtime groups reveal a different optimization frontier:

```text
pane_navigation     369.9s / 25 failures
watch_pane          217.2s / 15 failures
output_gaps         201.3s / 22 failures
tui_filter          186.4s / 7 failures
keymaps             178.7s / 24 failures
keymap_gaps         174.4s / 40 failures
help_window         162.5s / 8 failures
tui_navigation      160.9s / 11 failures
ansi                138.3s / 22 failures
ansi_gaps           138.2s / 23 failures
edge_cases          123.3s / 36 failures
batch               100.6s / 16 failures
```

The meta-program should therefore rank repairs by:

```text
expected semantic closure
+ expected runtime reduction
+ owner blast-radius risk
+ preservation sentinel coverage
```

not by failure count alone.

### 2.3 Fast-fail failures are runtime amplifiers

The audit correctly identifies parser/control failures as first priority because
some invalid controls still enter live mode and wait up to 30 seconds. This is a
crucial distinction:

```text
invalid control wrong error text       = product compatibility failure
invalid control enters live TUI mode   = product failure + runtime amplifier
```

That means control-plane fast-fail belongs in both:

```text
1. Invocation and control-plane grammar
10. Runtime substrate and observation ecology
```

### 2.4 Flag ownership precedes shell, batch, and TUI repair

The drift examples such as:

```text
sh: 0: Illegal option -B
sh: 0: Illegal option -
```

show that recognized hwatch flags are leaking into the monitored command. This
is not a renderer problem. It is an ownership/quarantine problem:

```text
program flag token
  != child command token
  != shell wrapper token
  != monitored command string token
```

Any batch renderer or TUI patch done before this split risks building on a
wrong argv substrate.

### 2.5 Deep TUI failures are real, but not first

The audit is right that deep TUI failures are now real product evidence. But the
branch should not be patched by full-eval iteration. It should be decomposed
into file/subtree local harnesses:

```text
tests/test_help_window.py
tests/test_pane_navigation.py
tests/test_watch_pane.py
tests/test_tui_filter.py
tests/test_output_gaps.py
keymap action files / keymap subtrees
```

The full eval should become a periodic integration gate, not the inner loop.

## 3. Main Correction To The Audit

The audit’s batch order is good, but I would make the first step a no-code
runtime attribution pass before Batch 1:

```text
Batch 0: Runtime-weighted branch ledger and timeout-amplifier matrix
```

Reason: the branch contains multiple kinds of slow rows. Some are slow because
invalid input enters live mode. Some are slow because a correct TUI state machine
is missing. Some are slow because snapshot/read horizons are wrong. Some are
slow because command/shell children are not supervised correctly.

Those must be split before implementation, or the worker will again treat
“deep branch” as one repair surface.

Required Batch 0 outputs:

```yaml
runtime_weighted_failure_row:
  test_name: string
  branch_id: string
  runtime_seconds: float
  failure_family: string
  first_failure_surface: string
  did_enter_live_mode: true|false|unknown
  should_have_fast_failed: true|false|unknown
  timeout_source:
    parser_live_mode | tmux_snapshot | subprocess_timeout |
    stable_wait | pytest_timeout | cleanup_timeout | unknown
  primary_hob_node: string
  implementation_owner: string
  local_subtree_harness: string|null
  preservation_sentinels: []
  patch_batch: 0|1|2|3|4|deferred
```

A row cannot enter a TUI patch batch until it proves:

```text
not a fast-fail control-plane row
not a flag-quarantine row
not a shell-template row
not a batch-renderer substrate row
```

## 4. v32 Schema Additions

### 4.1 `BRANCH_RUNTIME_BUDGET_GATE`

Trigger:

```text
A branch consumes disproportionate runtime, contains timeout/tmux/PTY/subprocess
rows, or official eval takes too long to be the normal repair loop.
```

Required row:

```yaml
branch_runtime_budget:
  branch_id: string
  passed_rows: int
  failed_rows: int
  total_reported_test_time_seconds: float
  mean_seconds_per_test: float
  slowest_row_seconds: float
  top_runtime_families: []
  timeout_amplifier_families: []
  local_subtree_harnesses: []
  full_eval_allowed_as_inner_loop: true|false
  next_full_eval_authorization:
    after_fast_fail_repair |
    after_shell_boundary_repair |
    after_batch_renderer_repair |
    after_deep_tui_subtree_repair |
    periodic_integration_only
```

Blocking rule:

```text
If full official eval exceeds the runtime budget and a branch dominates runtime,
implementation handoff must use targeted subtree harnesses until the timeout
amplifier has been reduced.
```

### 4.2 `TIMEOUT_AMPLIFIER_TRIAGE_GATE`

Purpose:

```text
Separate genuine TUI semantic rows from rows that are slow because an earlier
invalid/control/argv/shell condition failed to terminate promptly.
```

Required classes:

```text
fast_fail_missed
flag_quarantine_missed
shell_template_missed
batch_liveness_missed
tmux_snapshot_horizon_missed
genuine_tui_state_machine_missed
cleanup_or_process_ecology_missed
```

Rule:

```text
Rows classified as fast_fail_missed, flag_quarantine_missed, or
shell_template_missed cannot be batched under deep TUI state-machine repair.
```

### 4.3 `FAST_FAIL_AS_RUNTIME_CONTROL_GATE`

Purpose:

```text
Treat invalid parser/control behavior as a runtime-budget obligation whenever
invalid input can enter live/reactive mode.
```

Required child obligations:

```text
missing-value diagnostics
range diagnostics
equals-form parsing
-- separator precedence
command-like help precedence
invalid display-option values
invalid key names
invalid action names
empty key/action names
invalid mode combinations such as diff-output-only without differences
stdout/stderr/exit terminal contract
no-live-mode guarantee for invalid controls
```

Closure rule:

```text
Fast-fail rows close only when both byte/exit compatibility and no-live-mode
liveness are proven.
```

### 4.4 `FLAG_QUARANTINE_AND_CHILD_ARGV_GATE`

Purpose:

```text
Prevent program-owned flags from leaking into child command argv, shell argv, or
monitored command strings.
```

Required split:

```text
program option token
program option value
ignored-but-consumed option
child command token
shell wrapper token
shell template token
monitored command string
post-`--` token
short-cluster token
```

Rule:

```text
Ignored display/resource flags must still be consumed if they are recognized by
the program. Ignored is not equivalent to pass-through.
```

### 4.5 `SHELL_EXEC_TEMPLATE_SUBSTRATE_GATE`

Purpose:

```text
Model shell execution as an embedded substrate with its own argv/template law.
```

Required branches:

```text
default shell wrapper
direct exec mode
--shell sh
--shell "bash -c"
--shell with {COMMAND}
--shell without placeholder
complex command string
glob/arithmetic expansion
shell exit/status propagation
stdout/stderr ownership
child timeout/cleanup
```

### 4.6 `REACTIVE_TUI_SUBTREE_HARNESS_GATE`

Purpose:

```text
Do not use full official eval as the inner loop for high-latency TUI subtrees.
```

Required harnesses:

```text
help-window harness
pane-navigation harness
watch-pane harness
tui-filter harness
output-mode harness
keymap-action harness
ANSI/render harness
history-pane harness
```

Each harness must report:

```text
runtime budget
observer horizon
initial state
input event sequence
expected viewport/pane snapshot
cleanup/tmux/session state
regression sentinels imported from parser, flag quarantine, shell, and batch
```

### 4.7 `REACTIVE_RENDERER_STRATIFICATION_GATE`

Purpose:

```text
Split batch rendering, ANSI terminal-byte language, and interactive viewport
state instead of treating all output mismatches as one renderer bucket.
```

Strata:

```text
batch stdout/stderr/output projection
batch header / line-number / diff grammar
ANSI SGR and special-character normalization
interactive TUI viewport snapshot
pane focus / scroll / history state
status/help overlay windows
```

Rule:

```text
ANSI/special-character repairs should not be patched independently before the
batch output-router substrate is stable, unless a row is proven to bypass batch
projection entirely.
```

## 5. Revised hwatch Ontology Integration

The task should activate a specialized class:

```text
REACTIVE_TUI_COMMAND_SCHEDULER
```

Inherited child obligations:

```text
1. ControlPlane.FastFailAndCompatibility
1. ControlPlane.FlagOwnershipAndShortClusters
5. CommandBoundary.ShellExecTemplateSubstrate
7. Scheduler.BatchAndLoopLiveness
7. ChildProcess.SupervisionAndTimeoutLaw
8. BatchRenderer.ByteGrammar
8. TerminalRenderer.ANSIUnicodeDialect
8. InteractiveTUI.ViewportPaneStateMachine
9. Diagnostics.ExitChannelAndFatalPrecedence
10. RuntimeObservation.PTYTmuxObserverHorizon
10. RuntimeObservation.BranchRuntimeBudget
12. Orchestrator.TargetedSubtreeHarnessGovernance
```

The deep branch should be represented as a composed object:

```text
Branch476RuntimeSurface
  ├─ fast-fail missed rows
  ├─ flag quarantine / child argv rows
  ├─ shell exec template rows
  ├─ batch renderer / scheduler rows
  ├─ keymap validation rows
  ├─ genuine keymap action rows
  ├─ ANSI byte-language rows
  ├─ help-window rows
  ├─ pane-navigation rows
  ├─ watch-pane rows
  ├─ tui-filter rows
  └─ cleanup / observer-horizon rows
```

This prevents the orchestrator from treating `4764369abc4f` as one patch target.

## 6. Implementation Batches Reframed

### Batch 0 — no code: runtime attribution and subtree harness compilation

Inputs:

```text
phase11 audit
per-test runtime table
failure rows
candidate logs if available
```

Outputs:

```text
runtime_weighted_failure_ledger
branch476_subtree_map
fast_fail_amplifier_rows
flag_quarantine_rows
shell_boundary_rows
batch_renderer_rows
deep_tui_rows
local subtree harness specs
full_eval_authorization state
```

Closure:

```text
No broad implementation yet.
```

### Batch 1 — fast-fail + flag quarantine

Primary owners:

```text
cli_parser
flag_ownership_classifier
keymap_validator
child_argv_builder
```

Goal:

```text
Reduce runtime and remove shell illegal-option drift.
```

Must prove:

```text
invalid controls do not enter live mode
recognized program flags are consumed before child argv construction
short clusters are decomposed or rejected according to reference behavior
stdout/stderr/exit/message contracts are preserved
```

### Batch 2 — shell / exec substrate

Primary owners:

```text
shell_template_compiler
direct_exec_runner
child_supervisor
```

Goal:

```text
Stabilize command-boundary behavior before renderer/TUI repair.
```

### Batch 3 — batch renderer core

Primary owners:

```text
batch_scheduler
output_router
batch_renderer
ansi_normalizer
```

Goal:

```text
Repair batch-visible projection grammar before interactive viewport repair.
```

### Batch 4 — deep TUI subtrees by local harness

Primary owners:

```text
tui_state_machine
keymap_action_dispatcher
viewport_renderer
pane_history_model
filter_mode_model
help_window_model
```

Goal:

```text
Repair the branch-476 semantic core without running full official eval on every
change.
```

Allowed inner loop:

```text
file/subtree harness only
```

Full official eval allowed only when:

```text
Batch 1 and 2 are green;
runtime budget is improved or bounded;
subtree harnesses are green;
preservation sentinels are green;
branch cleanup/tmux/session state is clean.
```

## 7. Orchestrator Rule

The orchestrator must not dispatch:

```text
fix the 309 failures in branch 476
fix TUI failures
fix keymaps/output/ANSI
```

Allowed baton shape:

```yaml
worker_baton:
  target_batch: Batch 1 | Batch 2 | Batch 3 | Batch 4
  primary_hob_nodes: []
  included_failure_rows: []
  excluded_failure_rows_with_reason: []
  runtime_budget_goal: string
  local_subtree_harnesses: []
  preservation_sentinels: []
  allowed_implementation_owners: []
  forbidden_implementation_owners: []
  full_eval_authorization: blocked | allowed_after_gate
```

The highest-risk illegal transition is:

```text
full-visible official eval
  -> huge branch failure count
  -> broad TUI implementation patch
```

The legal transition is:

```text
full-visible official eval
  -> runtime-weighted branch ledger
  -> timeout-amplifier split
  -> fast-fail/flag/shell/batch/deep-TUI subtree assignment
  -> bounded worker baton
```

## 8. Generalization Beyond hwatch

This patch applies to any program class with:

```text
TUI / curses / terminal UI
tmux/PTY test harnesses
watch/refresh loops
subprocess supervision
interactive keymaps
output panes/history/help windows
batch plus interactive modes
long waits or timeout-driven assertions
```

General invariant:

```text
For high-latency reactive programs, a failure row has two owners:
  semantic owner: what product behavior is wrong;
  runtime owner: why this row is expensive to observe.

A repair plan is incomplete until both owners are assigned.
```

## 9. Bottom Line

Run 2 is good news: the eval now reaches all branches and produces readable
artifacts. But the run is still not a practical feedback loop because the deep
TUI branch is both the largest semantic frontier and the largest runtime sink.

The next meta-program revision should therefore promote runtime-weighted repair
selection:

```text
result-artifact liveness
  -> branch runtime budget
  -> timeout-amplifier triage
  -> fast-fail and flag quarantine
  -> shell/exec substrate
  -> batch renderer substrate
  -> local TUI subtree harnesses
  -> periodic full eval
```

This is the safe way to move from score 62 without burning an hour on every
candidate and without patching deep TUI symptoms before the control/argv/shell
substrate is correct.
