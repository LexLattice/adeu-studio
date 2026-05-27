# `entr` Solving Progression: Safe Generalizations for the Program Ontology

Authority posture: derived from the final `entr` causal mapping as `manual_run_trace + post_eval_pressure`. This document abstracts the reusable ontology and method lessons without promoting `entr`-specific details as universal facts.

## 1. Core read

The `entr` reconstruction reached official green:

```text
684 passed / 0 failed / 1 skipped / 685 total
```

The decisive shift was not merely better patching. The program was reinterpreted from:

```text
run a command when files change
```

to:

```text
a reactive file/resource watch scheduler that multiplexes configuration streams,
filesystem events, keyboard/control events, child-process state, signals,
resource mutation, command binding, diagnostics, liveness, and exit law.
```

This makes `entr` a different kind of reconstruction case from `trdsql`.

`trdsql` mainly stress-tested:

```text
resource-backed language substrate + dialect sublanguages + renderer exactness
```

`entr` mainly stress-tested:

```text
reactive scheduler substrate + event-channel topology + process ecology + liveness contracts
```

Both confirm the same meta-rule:

```text
A visible feature label is not a closed behavior.
It imports inherited child obligations until each child is covered, proved
irrelevant, blocked, or explicitly deferred with expected risk.
```

## 2. What the progression showed

### 2.1 Early conceptual pass was directionally correct but under-expanded

The early ontology correctly saw that `entr` was not just a command runner. It identified a scheduler/process-supervisor/resource-topology program. The key insight was that flags are behavior operators:

```text
-d changes resource topology
-r changes child lifecycle
-x opens a status/reporting sublanguage
-s changes command boundary
-z changes parent exit law
-p changes startup scheduling
```

The miss was that several parents were recognized but accepted too early as scoped-ready:

```text
interactive keyboard plane
status filter sublanguage
directory direct-watch conflict branches
environment/config overlays
process-group ecology
```

Generalized lesson:

```text
Parent recognition is not closure.
Parent applicability imports child obligations.
Representative probes prove only scoped readiness unless sibling branches are
closed or explicitly deferred.
```

### 2.2 Cleanroom reference observation corrected the event model

The reference observations changed the interpretation of events:

```text
old: events are filesystem changes
new: events are typed control inputs from filesystem, keyboard, signal, and
     child-process state, each with its own resource channel and liveness law
```

Generalized lesson:

```text
Reactive programs must split configuration input from runtime event channels.
stdin may configure the program while /dev/tty, signals, child exit, filesystem
watchers, sockets, timers, or subprocess state act as independent event sources.
```

### 2.3 The score ladder tracks ontology depth, not patch count

The score progression was:

```text
Phase 9/10: 494 passed / 190 failed / score 71
Phase 12:   605 passed / 79 failed / score 90
Phase 13:   636 passed / 48 failed / score 94
Phase 14:   673 passed / 11 failed / score 98
Phase 16:   683 passed / 1 failed / rounded 100
Phase 17:   684 passed / 0 failed / official green
```

The largest jumps corresponded to ontology transitions:

```text
Phase 12:
  public schema re-entry over CLI, command binding, status/env/dir branches

Phase 14:
  interactive control plane reinterpreted as /dev/tty keyboard resource,
  not stdin-as-TTY

Phase 16:
  directory topology split by source route, command class, lifecycle, entry class,
  hidden-entry policy, and signal/status timing

Phase 17:
  direct-directory + direct executable + file-count change split from
  direct-directory + shell counter utility
```

Generalized lesson:

```text
Score movement should be mapped to ontology transitions.
A large gain usually means a parent discriminator was repaired.
A late one-row tail often means a final sibling under an already-known owner
still lacks one child discriminator.
```

## 3. Safe generic ontology extensions

These should be added to the general program ontology as reusable classes or gates.

### 3.1 `REACTIVE_SCHEDULER_PROGRAM_CLASS`

Trigger when the program:

```text
watches files/resources
runs commands after events
listens for keyboard/signal/timer/process events
restarts or supervises children
keeps a loop alive after work
uses a command/status script as part of behavior
```

Imported child obligations:

```text
EVENT_CHANNEL_TOPOLOGY
RESOURCE_WATCH_REGISTRATION
SCHEDULER_STARTUP_EVENT_LIVENESS
COMMAND_BOUNDARY_AND_ARGUMENT_BINDING
CHILD_PROCESS_SUPERVISION
INTERACTIVE_CONTROL_TERMINAL
STATUS_FILTER_SUBLANGUAGE
RESOURCE_MUTATION_LIFECYCLE
SIGNAL_PROCESS_GROUP_ECOLOGY
DIAGNOSTIC_EXIT_LIVENESS_CONTRACT
```

### 3.2 `EVENT_CHANNEL_TOPOLOGY_GATE`

Purpose:

```text
Separate every channel by role, lifecycle, observer, and authority.
```

Required axes:

```text
configuration stream vs event stream
stdin vs tty vs signal vs filesystem vs child-state vs timer vs network
startup event vs external event vs synthetic event
blocking vs nonblocking observation
observer horizon and timeout
side-effect ordering
liveness expectation after event
```

Key rule:

```text
Do not infer keyboard/control behavior from stdin shape.
Do not infer filesystem watcher behavior from static file-open behavior.
Do not infer child-process behavior from parent exit alone.
```

### 3.3 `CONFIG_STREAM_VS_CONTROL_STREAM_GATE`

The `entr` PTY closure showed a general class of bugs:

```text
file-list stdin was confused with interactive keyboard input
```

General gate:

```text
If a program reads initial configuration from stdin and also has interactive
runtime controls, the two streams must be modeled as separate resources.
```

Required probes:

```text
stdin-as-configuration under non-TTY
stdin-as-configuration while keyboard comes from /dev/tty or PTY
keyboard quit / continue / trigger keys
non-control key ignored
control stream absent
control stream present but configuration stream piped
composition with command/shell/restart/postpone modes
```

### 3.4 `RESOURCE_WATCH_REGISTRATION_GATE`

Reactive programs often distinguish:

```text
opened resource
registered watched resource
displayed resource identity
mutation-tracked resource
parent resource
child resource
symlink target resource
hidden entry resource
```

Required axes:

```text
file vs directory
parent directory vs direct directory
symlink path vs symlink target
missing resource at startup
resource deleted after registration
resource replaced/renamed over
hidden file vs hidden directory
child metadata mutation
file-count change
recursive or double-depth flags
```

Key rule:

```text
The file path read at startup is not automatically the watch identity.
Resource identity can move through parent directories, symlink policy, hidden-entry
policy, and mutation lifecycle.
```

### 3.5 `SCHEDULER_STARTUP_EVENT_LIVENESS_GATE`

The late `entr` tail was about scheduler semantics, not raw file watching.

Required axes:

```text
startup run vs postponed startup
first event run
debounce / consolidation
restart old child before new run
exit-after-run
remain-live-after-run
fatal event after run
parent exit code derived from child vs event vs directory condition
```

Critical cross-products:

```text
mode x resource topology x command class x event type
```

A direct-directory watch may behave differently with:

```text
shell counter utility
direct executable utility
simple echo finite command
interactive PTY loop
```

### 3.6 `COMMAND_BOUNDARY_AND_ARGUMENT_BINDING_GATE`

Required when a reactive program runs a user command.

Axes:

```text
direct argv execution
shell string execution
placeholder substitution
selected-path binding
shell $0 / argv0 binding
cwd and environment defaults
quoting and spaces in resource paths
command not found / exec failure
```

General rule:

```text
Command binding is a language boundary.
It must be modeled as its own sublanguage, not as string concatenation.
```

### 3.7 `CHILD_PROCESS_SUPERVISION_GATE`

Required when the parent launches, restarts, signals, waits on, or reaps children.

Axes:

```text
child process group vs single child
restart policy
termination signal choice
HUP/TERM/INT forwarding
already-exited child cleanup
zombie prevention
terminal-close cleanup
child stdout/stderr ownership
parent exit derived from child signal/status
```

General rule:

```text
If the program supervises children, process ecology is product behavior, not
harness noise.
```

### 3.8 `STATUS_FILTER_SUBLANGUAGE_GATE`

`entr` exposed a status helper substrate through `-x/-xx`.

General trigger:

```text
A program generates, invokes, reads, or preserves a helper script/filter/template
that transforms runtime status into user-visible reports.
```

Required axes:

```text
generated template shape
custom helper preservation
helper path/environment override
creation timing
permissions/executable state
input record grammar
exit/signal record grammar
stdout/stderr/status projection
failure of helper itself
```

General rule:

```text
A status helper is a subprogram. Treat it like a sublanguage plus resource
lifecycle, not as a string formatter.
```

### 3.9 `INTERACTIVE_CONTROL_TERMINAL_GATE`

Required when runtime keyboard controls, PTY/tmux behavior, curses/terminal, or `/dev/tty` appear.

Axes:

```text
control terminal exists / absent
watch-list stdin separate from control terminal
TTY vs pipe vs PTY vs tmux
startup run under interactive mode
trigger key
quit key
non-quit uppercase variants
ignored keys
composition with restart, clear, shell, postpone
observer horizon / timeout / nonblocking read
```

Rule:

```text
Interactive does not mean stdin is TTY.
Interactive means a runtime control resource exists and has its own event grammar.
```

### 3.10 `DIRECT_DIRECTORY_CONFLICT_LATTICE`

This is the most task-shaped gate, but the abstract form is useful for any watcher.

Trigger:

```text
A resource kind can be both direct subject and parent-of-subject.
```

Axes:

```text
direct resource route vs derived parent route
startup behavior
child-entry mutation behavior
hidden-entry policy
count-change fatal behavior
command-class-specific behavior
interactive composition
exit/liveness consequence
```

General rule:

```text
If one resource can be both watched object and container of watched objects,
create a conflict lattice before patching event behavior.
```

## 4. Method generalizations

### 4.1 Post-eval pressure worked because it was grouped by owner

The successful loop was:

```text
official rows
  -> grouped failure attribution
  -> smallest shared owner
  -> ontology repair
  -> regression-conserving patch
```

Do not generalize official test names. Generalize the grouping discipline.

### 4.2 Rejected broad patches are first-class evidence

Phase 15 solved some tail rows but caused 17 regressions in directory rows. That was not merely a bad implementation. It proved that the candidate theory had collapsed sibling branches under the direct-directory scheduler.

General rule:

```text
A rejected patch defines a forbidden patch class and a required parent ascent.
```

Required ledger row:

```yaml
rejected_patch_class:
  patch_ref: string
  solved_leaf_refs: []
  regressed_leaf_refs: []
  shared_owner: string
  collapsed_discriminator: string
  forbidden_future_strategy: string
  required_parent_ascent: string
  preservation_sentinels: []
```

### 4.3 Late tails often require command-class split, not more resource heuristics

The final one-row failure was not solved by changing directory watching globally. It required:

```text
direct directory + direct executable + file-count change
  != direct directory + shell counter utility
```

General rule:

```text
When a reactive scheduler tail persists after resource topology seems closed,
check whether command class changes the scheduler/exit/liveness contract.
```

### 4.4 PTY/interactive rows are not just resource ecology

Earlier jplot work introduced resource/observation ecology. `entr` adds a sharper point:

```text
A PTY can be the product control plane, not merely a harness condition.
```

So the ecology gate must split:

```text
pre-product masking
product control-channel semantics
observer horizon / liveness semantics
harness artifact side effects
```

### 4.5 Status/env/path timing is a first-class lifecycle branch

Environment paths and generated helper files may need to be created before a later blocking read or event wait. General rule:

```text
Side-effect timing relative to blocking observation must be terminalized.
```

## 5. Proposed v30 additions to the general HOB catalog

Add these generic numbered subtrees under the existing 12-family program ontology.

```text
7.x ReactiveSchedulerLifecycle
  7.x.1 Startup/postpone/first-event scheduling
  7.x.2 Event consolidation/debounce
  7.x.3 Exit-after-run and parent-exit law
  7.x.4 Remain-live horizon
  7.x.5 Event-fatal-after-command branch

7.y ChildProcessSupervision
  7.y.1 Direct child vs process group
  7.y.2 Restart and old-child termination
  7.y.3 Signal forwarding and parent status
  7.y.4 Already-exited child reaping
  7.y.5 Terminal-close cleanup

3.x WatchResourceTopology
  3.x.1 Startup resource list stream
  3.x.2 Registered watch identity
  3.x.3 Parent directory watch identity
  3.x.4 Direct directory subject identity
  3.x.5 Symlink follow policy
  3.x.6 Hidden entry policy
  3.x.7 Resource deletion/replacement policy
  3.x.8 Child metadata/file-count mutation

1.x MultiChannelControlPlane
  1.x.1 CLI flag grammar
  1.x.2 Configuration stdin
  1.x.3 Runtime control terminal
  1.x.4 Signal control plane
  1.x.5 Environment control overlay

5.x CommandBoundaryLanguage
  5.x.1 Direct argv command
  5.x.2 Shell command string
  5.x.3 Placeholder/selected-resource binding
  5.x.4 Shell argv0/$0 binding
  5.x.5 Command env/cwd defaults

5.y StatusFilterSubprogram
  5.y.1 Generated helper template
  5.y.2 Custom helper preservation
  5.y.3 Helper path/env override
  5.y.4 Helper input record grammar
  5.y.5 Helper exit/signal status grammar
  5.y.6 Helper creation timing and permissions

9.x ReactiveDiagnosticsExitLiveness
  9.x.1 Usage/help/invalid control bytes
  9.x.2 Watch-resource diagnostics
  9.x.3 Directory altered diagnostics
  9.x.4 Child exec diagnostics
  9.x.5 Parent/child exit composition
  9.x.6 Live timeout as success/failure surface

10.x InteractiveObserverTopology
  10.x.1 PTY/non-PTY/control-terminal availability
  10.x.2 Keyboard event grammar
  10.x.3 Watch-list stdin vs keyboard control split
  10.x.4 tmux/terminal observer profile
  10.x.5 Nonblocking read and observer horizon
```

## 6. Integration with existing meta-program gates

These additions do not replace the existing v29 tail-dialect discipline. They apply to a different program class.

Existing gates retained:

```text
HOB inherited-child enforcement
public schema re-entry
scoped-ready vs gold-ready separation
orthogonal semantic pools
methodological equivalence
anti-replay / generalization
orchestrator phase-transition enforcement
owner-aware regression conservation
rejected-patch memory
```

New reactive-specific gate bundle:

```text
REACTIVE_PROGRAM_BUNDLE =
  EVENT_CHANNEL_TOPOLOGY_GATE
  CONFIG_STREAM_VS_CONTROL_STREAM_GATE
  RESOURCE_WATCH_REGISTRATION_GATE
  RESOURCE_MUTATION_LIFECYCLE_GATE
  SCHEDULER_STARTUP_EVENT_LIVENESS_GATE
  COMMAND_BOUNDARY_AND_ARGUMENT_BINDING_GATE
  CHILD_PROCESS_SUPERVISION_GATE
  STATUS_FILTER_SUBLANGUAGE_GATE
  INTERACTIVE_CONTROL_TERMINAL_GATE
  DIRECT_DIRECTORY_CONFLICT_LATTICE
  DIAGNOSTIC_EXIT_LIVENESS_CONTRACT
```

## 7. What should not be over-generalized

Do not add these as universal obligations:

```text
/_ placeholder specifically
status.awk specifically
ENTR_STATUS_SCRIPT specifically
ENTR_FOLLOW_SYMLINK specifically
-d/-dd spellings specifically
space/q/Q key meanings specifically
directory altered exact text specifically
```

Safe abstraction:

```text
selected-resource placeholder binding
status helper environment/path override
symlink-follow environment overlay
single-depth vs double-depth directory recursion mode
runtime keyboard event grammar
resource mutation diagnostic text
```

## 8. Worker-handoff template for future reactive tasks

Before source patching, the orchestrator should require:

```yaml
reactive_program_handoff:
  active_class: REACTIVE_SCHEDULER_PROGRAM_CLASS
  event_channels:
    configuration_streams: []
    runtime_event_streams: []
    control_streams: []
    child_state_streams: []
  resource_topology:
    watched_subjects: []
    registered_identities: []
    parent_identities: []
    mutation_cases: []
  scheduler_laws:
    startup: []
    event: []
    restart: []
    exit_after: []
    remain_live: []
  command_boundary:
    direct_argv: status
    shell_string: status
    selected_resource_binding: status
    env_cwd_defaults: status
  process_supervision:
    process_group: status
    signal_forwarding: status
    zombie_prevention: status
  interactive_control:
    control_terminal: status
    keyboard_grammar: status
    observer_horizon: status
  status_subprogram:
    generated_template: status
    custom_override: status
    path_env_overlay: status
  diagnostic_exit_liveness:
    stdout_stderr_split: status
    parent_exit_law: status
    live_timeout_success: status
  preservation_sentinels: []
  rejected_patch_classes: []
  handoff_status: blocked | scoped_ready | implementation_ready | gold_ready
```

## 9. Bottom line

The reusable insight from `entr` is:

```text
For reactive tools, the hidden ontology is often not in data formats or output
renderers. It is in event-channel topology, scheduler lifecycle, command
boundary, resource mutation, process supervision, and liveness/exit law.
```

A future meta-program should therefore route watcher/scheduler/supervisor tools into a dedicated reactive bundle as early as the base ontology pass. Once that class applies, all event, resource, command, process, interactive, status, diagnostic, and liveness children should be inherited obligations unless explicitly proved irrelevant.
