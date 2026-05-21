# jplot v10 Abstraction Pass From Score 98

Task: `rs__jplot.2a54bcc`

Bundle reviewed: `programbench_jplot_gptpro_abstraction_bundle_20260520.zip`

Current official result in the bundle:

```text
score: 98
raw:   705 passed / 16 failed / 1 skipped / 722 total
```

Authority posture:

```text
official eval rows      = post-eval pressure / support
public reference scouts = public-reference observation, scoped
local gates             = implementation-calibration evidence
remaining row names     = not clean first-attempt evidence
```

This note treats the remaining rows as layer-transition misses and meta-program feedback, not as a patch list.

---

## 1. Score ladder readout

The 93 -> 98 ladder validates the v9 move from row-patching toward parent-discriminator repair.

```text
93 -> 95  clocked URL process, repeated fetches, signal exit, EOF split
95 -> 96  default steps split: default live URL vs explicit --steps=1
96 -> 97  PTY URL horizon split: non-PTY short horizon vs PTY longer horizon
97 -> 98  startup-visible protocol witness: ReportCellSize, iTerm image, Kitty image rows
```

The transition statistics from the included official eval JSONs:

| Transition | Fixed rows | New rows | Remaining non-passed rows | Interpretation |
|---|---:|---:|---:|---|
| 93 -> 95 | 13 | 1 | 31 | `CLOCKED_SOURCE_PROCESS` discovered a real parent; one new PTY branch was exposed. |
| 95 -> 96 | 4 | 0 | 27 | Flag presence vs resolved default was a real semantic discriminator. |
| 96 -> 97 | 6 | 0 | 21 | PTY/non-PTY horizon split was a real substrate discriminator. |
| 97 -> 98 | 4 | 0 | 17 | Startup protocol witness fixed some protocol-observation rows. |

The remaining 17 non-passed rows are not new regressions. They are the stubborn residue already present at score 93, except the exact surface of some rows changed as earlier masks were removed.

---

## 2. Actual remaining groups at score 98

The actual `score_98_eval.json` grouping is slightly different from `remaining_failure_groups.md`.

`remaining_failure_groups.md` says `all_zero_values` belongs to the port-masking group, but the score-98 JSON currently shows it as a render failure. It also omits `tests.test_graphics_protocols.test_kitty_protocol_basic_image_transmission` from the fixed-port group, although that row is an `Address already in use` failure in the actual JSON.

### 2.1 Observed failure mechanism groups

| Group | Rows | Score-98 surface | Layer-transition diagnosis |
|---|---:|---|---|
| Resource ecology / fixed-port masking | 6 | `OSError: [Errno 98] Address already in use` before the candidate can even run the specific branch | Probe/harness resource graph is still interfering with product observation. |
| Render transform exactness | 5 | `render() ... failed` with empty stderr | The render-success contract for data morphology is under-derived or not transferred. |
| Terminal no-source conflict | 2 | expected no-source, actual window-size | Substrate-sensitive conflict between public env-terminal scout and official terminal-common expectation. |
| Terminal loop persistence | 1 | PTY read gets `EIO` after about 5.1s | Observer horizon / loop persistence is under-modeled. |
| Protocol witness overreach | 1 | expected window-size diagnostic, actual large protocol/render byte stream | Startup-visible witness is not branch-scoped; witness bytes contaminate a fatal-error leaf. |
| Coverage harness side effect | 1 | no coverage data collected | Harness-side artifact pressure, not normal product semantics. |
| Tmux dependent skip | 1 skipped | dependency skip | Dependent substrate lane; not a product failure until parent is observable. |

### 2.2 Exact current row membership

Resource ecology / fixed-port masking:

```text
tests.test_graph_edge_cases.test_graph_with_marker_field
tests.test_graph_edge_cases.test_graph_with_flat_line_all_same_values
tests.test_render_coverage.test_render_with_http_source_covers_graph_code
tests.test_graph_edge_cases.test_graph_with_marker_and_flat_line
tests.test_graphics_protocols.test_kitty_protocol_basic_image_transmission
tests.test_graphics_protocols.test_kitty_protocol_image_id_alternation
```

Render transform exactness:

```text
tests.test_graph_edge_cases.test_graph_with_all_zero_values
tests.test_render_coverage.test_render_with_http_source_varied_data
tests.test_graph_edge_cases.test_graph_with_multiple_markers
tests.test_render_coverage.test_render_with_http_source_custom_rows
tests.test_graph_edge_cases.test_graph_with_multiple_series_for_color_coverage
```

Terminal no-source conflict:

```text
tests.test_terminal_common.test_neither_url_nor_stdin_provided_with_terminal
tests.test_terminal_common.test_neither_url_nor_stdin_with_multiple_specs
```

Singleton groups:

```text
tests.test_gap_fill_term.test_clearscrollback_escape_sequence_format
tests.test_tui_rendering.test_render_failure_with_steps_parameter
tests.test_tui_rendering.test_http_source_ticker_architecture_verification
eval.tests.test_interactive_tmux.test_ctrl_c_exits   # skipped dependency
```

---

## 3. Was the largest group really `field-spec grammar / dashboard graph topology`?

No, not at score 98.

That diagnosis was useful earlier, but the 98 residue should be split by deeper parent discriminators:

```text
1. shared probe/resource ecology
2. render-transform success contract
3. substrate-sensitive fatal gate conflict
4. observer horizon / loop persistence
5. protocol witness scope and budget
6. harness-side artifact obligation
```

The largest *observed failure mechanism* is fixed-port masking, with six rows. The largest remaining *product-semantics* subtree is render-transform exactness, with five direct render failures and some additional rows hidden behind port masking.

So the correct refinement is:

```text
old parent:
  field-spec grammar / dashboard graph topology

new parent split:
  POSITIONAL_DSL_AST                         mostly repaired / green enough
  RENDER_TRANSFORM_SUCCESS_CONTRACT          still not closed
  RESOURCE_ECOLOGY_INTERFERENCE_GRAPH        still masking several leaves
  PROTOCOL_WITNESS_SCOPE                     over-broad in one branch
  SUBSTRATE_CONFLICT_LEDGER                  unresolved terminal no-source rows
```

The field-spec grammar itself appears mostly solved. What remains is not primarily the parser's ability to accept `marker`, `counter`, `+`, comma options, or multiple specs. The remaining render rows are about mapping accepted data/topology into a successful drawable/protocol state under the evaluator's success oracle.

---

## 4. Which v9 operators were successful?

### 4.1 `CLOCKED_SOURCE_PROCESS`

This was the clearest success. It converted the shallow model:

```text
URL = fetch once, validate once, sleep forever
```

into:

```text
URL = clocked source process
    = fetch/read/validate/update/repeat/signal/cleanup
```

It fixed one-shot URL behavior, repeated fetch counts, short-interval stress rows, signal exit behavior, and EOF wording branches.

### 4.2 Flag presence vs resolved default

The 95 -> 96 jump shows that v9 still needed an explicit rule:

```text
absence of a control flag != explicit flag whose parsed value equals the default
```

This is a general meta-program lesson. A value lattice must track both:

```text
presence state: absent | present-default-equivalent | present-non-default
resolved value: concrete parsed value
```

### 4.3 `TERMINAL_PROTOCOL_SUBSTRATE`

The 96 -> 97 jump validates the idea that the same semantic program has different process horizons under different substrates:

```text
non-PTY env terminal: short bounded window-size path
PTY terminal: longer live dashboard path
```

This was not a data-source issue. It was a substrate/process-horizon issue.

### 4.4 Startup-visible protocol witness

The 97 -> 98 jump validates the existence of startup-visible protocol obligations:

```text
terminal capability query
ReportCellSize query
iTerm image witness
Kitty image witness
```

But the remaining `--steps` failure shows that the operator is under-scoped: witness bytes must be branch- and phase-limited.

### 4.5 `Warrant` discipline

The bundle keeps the clean evidence boundary intact. It explicitly marks official failures as post-eval pressure and public-reference scouts as scoped observations. This is a major success of the meta-program itself.

### 4.6 Partially successful but not yet executable: `SCOUT_RESOURCE_ECOLOGY`

v9 names probe/resource ecology, but the current result shows that naming it was not enough. It must become an executable gate before implementation handoff, especially for programs that combine:

```text
fixed ports
HTTP servers
long-lived child processes
PTYs
signals
parallel pytest workers
reruns
coverage side effects
```

---

## 5. Which misses were public-scout discoverable vs conceptual-descent discoverable?

### 5.1 Better conceptual descent from README/spec should have derived

```text
render success is an obligation, not merely render-byte emission
flat/all-zero/constant domains are transform degenerates
markers are overlays, not just field-spec parse options
multiple series imply color/identity/topology obligations
rows/custom-height compose with graph transform
startup protocol witness is branch-scoped, not universal prefix
observer horizon is part of the terminal loop contract
source/no-source precedence can be substrate-sensitive
```

These are not hidden-row facts. They follow from a program that is an interactive terminal graph renderer over streamed JSON data.

### 5.2 Better public scout should have discovered exactness

```text
exact request-count timing for URL mode
SIGINT/SIGTERM exit shape
empty vs truncated response error text
PTY vs non-PTY liveness horizon
whether no-source or window-size wins under each env/stdio combination
whether explicit --steps=1 should hit zero-range, render bytes, or window-size
whether startup protocol bytes may appear before fatal diagnostics
render-success outcome for flat/all-zero/marker/multiple-series/custom-row cases
whether repeated fixed-port probes collide under serial, rerun, and xdist-like schedules
```

The key scout pattern should be:

```text
not only: what does this branch output?
but also: what earlier/later branch did this output prove reachable,
and what shared resources remain live afterward?
```

### 5.3 Likely not cleanly public-scout discoverable from README alone

```text
coverage data collected by evaluator harness
dependency skip structure for tmux row
some exact parallel fixed-port collision patterns under official pytest-xdist scheduling
```

These should be represented as harness-surface or evaluator-conflict obligations, not laundered into product semantics.

---

## 6. Implementation transfer errors vs theory gaps

### 6.1 Mostly theory / meta-program gaps

```text
protocol witness scoping
observer horizon contract
render-success oracle contract
resource-ecology interference graph as an executable gate
harness-side artifact surface
conflict-isolated terminal no-source split
```

These are not merely bad code choices. They reflect missing terminal leaves or insufficient handoff gates.

### 6.2 Mostly implementation transfer / implementation-calibration errors

```text
render() success rows once the render-success contract is stated
fixed-port rows once a resource-ecology gate proves the leak/collision mechanism
PTY persistence once the observer horizon is locked
protocol overreach once witness scoping is locked
```

These can become implementation errors only after the corresponding probes are generated and their authority state is clear.

### 6.3 Conflict / evaluator-support rows, not ordinary implementation errors

```text
terminal no-source conflict:
  public env-terminal scout says one thing;
  official terminal-common rows expect another.

coverage harness side effect:
  likely about evaluator instrumentation or artifact production.

tmux dependency skip:
  child branch depends on parent substrate observability.
```

These should not drive blind patching until the warrant ledger says which authority layer owns them.

---

## 7. Probes to generate before any implementation patch

### P0. Resource ecology interference graph

Purpose: separate product semantics from probe substrate collisions.

Required probes:

```text
serial fixed-port repeated URL/render probes
parallel fixed-port URL/render probes
rerun-style repeated failures using the same port
process table before/after each probe
open TCP listener/socket state before/after each probe
HTTP client connection close / idle-connection behavior
signal cleanup and timeout cleanup
```

Expected output is not only stdout/stderr/exit. It must include resource-state deltas.

### P1. Render-transform success matrix

Purpose: lock success/failure oracle for data morphology.

Rows:

```text
single increasing series
varied data
flat line / all same values
all zero values
marker field
multiple markers
marker + flat line
multiple series / color identity
custom rows
rows=0 / terminal-sized rows
explicit --steps=1
explicit --steps=2
```

For each row record:

```text
exit code
stdout protocol classes
stderr
runtime horizon
whether harness regards render() as success
which branch owns failure if failure occurs
```

### P2. Protocol witness scope and suppression

Purpose: prevent startup witness bytes from being global unconditional output.

Matrix:

```text
valid render branch
window-size fatal branch
no-source fatal branch
zero-range / --steps=1 branch
unsupported terminal branch
screen/tmux unsupported branch
invalid field/source branch
```

For each branch:

```text
allowed startup bytes
forbidden startup bytes
whether diagnostic must appear
whether protocol bytes may precede diagnostic
whether protocol bytes may replace diagnostic
```

### P3. Terminal source-precedence conflict matrix

Purpose: isolate the public-reference vs official no-source conflict.

Matrix:

```text
non-TTY + no terminal env + no stdin
non-TTY + TERM_PROGRAM=iTerm.app + no stdin
non-TTY + TERM_PROGRAM=iTerm.app + stdin
PTY + no stdin
PTY + stdin
PTY + URL
multiple specs + no source
screen/tmux env + no source
```

This should produce a conflict ledger if public-reference and official rows remain incompatible.

### P4. Observer horizon / loop persistence probe

Purpose: establish how long the terminal loop must remain observable.

Rows:

```text
PTY URL live run observed for 6s, 10s, 15s
PTY no-url render path observed for clear-scrollback bytes
Ctrl-C after steady-state
SIGTERM after steady-state
master read after process lifecycle boundary
```

This prevents arbitrary constants such as a 5s horizon from accidentally defining product behavior.

### P5. Harness-side artifact probe

Purpose: decide whether coverage artifacts are product obligations, evaluator-only pressure, or impossible under the witness bundle.

Rows:

```text
run under local coverage-like harness
inspect generated coverage files
inspect environment variables / cwd / tempdir effects
record whether executable bundle can generate required artifacts at all
```

This probe may end as `conflict_isolated` or `post_eval_only` rather than implementation-ready.

### P6. Tmux dependent lane

Purpose: unblock only after parent branch is stable.

Rows:

```text
tmux startup without graphics gate
tmux URL run liveness
Ctrl-C exits under tmux
stdout/stderr/exit and process cleanup after Ctrl-C
```

Do not use this as a first patch target while parent resource/protocol branches are unstable.

---

## 8. Proposed v10 meta-program delta

Keep the v8/v9 kernel:

```text
Factor
Partition
Bind
Transform
Sequence
Expose
Compose
Warrant
```

Add the following generic macros and bookkeeper rules.

### 8.1 `RESOURCE_ECOLOGY_INTERFERENCE_GRAPH`

```text
RESOURCE_ECOLOGY_INTERFERENCE_GRAPH
  = Factor shared resources: ports, sockets, processes, PTYs, temp files,
    coverage files, terminal handles, signals, background loops
  + Bind resource owners: product, probe harness, evaluator, OS, dependency
  + Sequence setup/run/teardown/retry/rerun/parallel schedules
  + Compose shared-resource collisions across sibling probes
  + Expose resource failure surfaces: bind errors, EIO, timeout, stale files,
    missing coverage, zombie process, port still bound
  + Warrant product-vs-harness authority split
```

Mandatory trigger:

```text
Any program class with long-lived processes, network servers/clients, PTYs,
signal handling, filesystem side effects, or parallel test ecology.
```

Bookkeeper rule:

```text
A row that fails before the candidate-specific behavior is reached cannot be
promoted as product-theory evidence until resource ownership is assigned.
```

### 8.2 `OBSERVABLE_SUCCESS_CONTRACT`

```text
OBSERVABLE_SUCCESS_CONTRACT
  = Bind success denominator: exit code, timeout/non-timeout, byte class,
    stderr absence/presence, side effect, harness predicate
  + Transform semantic state into success/failure state
  + Sequence success lifecycle: startup, first render, steady state, teardown
  + Expose exact success oracle per surface
  + Warrant public/scoped/gold success authority
```

Why needed:

```text
The existing render-transform macro can describe graph bytes but still fail to
ask what the evaluator regards as render() success.
```

### 8.3 `WITNESS_SCOPE_AND_BUDGET`

```text
WITNESS_SCOPE_AND_BUDGET
  = Bind witness bytes/events to the branch they are allowed to prove
  + Sequence phase in which witness may appear
  + Expose allowed prefix/suffix/diagnostic coexistence
  + Compose witness bytes with fatal-gate precedence
  + Warrant witness-only vs full behavior-promotion boundary
```

Why needed:

```text
Startup-visible protocol witnesses fixed some rows but overreached in at least
one branch where the oracle still expected a window-size diagnostic.
```

Rule:

```text
A witness emitted to prove capability must not become an unconditional global
prefix unless the projection grammar says every branch permits it.
```

### 8.4 `OBSERVER_HORIZON_CONTRACT`

```text
OBSERVER_HORIZON_CONTRACT
  = Sequence startup horizon, first-output horizon, steady-state horizon,
    signal horizon, teardown horizon
  + Bind observer: user, public scout, test harness, terminal emulator,
    subprocess timeout
  + Expose liveness/early-exit/timeout/read-error surfaces
  + Warrant tolerance windows and authority layer
```

Why needed:

```text
Clocked-source liveness is not only request count. It is also the duration for
which external observers can still interact with the process.
```

### 8.5 `HARNESS_SIDE_EFFECT_SURFACE`

```text
HARNESS_SIDE_EFFECT_SURFACE
  = Factor artifacts expected outside ordinary stdout/stderr/files named by the
    product: coverage files, profiling output, logs, instrumentation records
  + Bind owner: product, build system, evaluator, language toolchain
  + Sequence when artifacts are created/flushed
  + Expose missing-artifact and stale-artifact surfaces
  + Warrant product obligation vs evaluator-only pressure
```

Why needed:

```text
Coverage rows should not silently become product semantics.
```

### 8.6 `CONFLICTED_SUBSTRATE_RULE`

```text
CONFLICTED_SUBSTRATE_RULE
  = Warrant public-reference observation and official pressure separately
  + Compose substrate dimensions that may explain the conflict
  + require either a conflict probe, source-postmortem, or explicit deferral
    before implementation handoff
```

Why needed:

```text
A single global terminal/source precedence law is too coarse when env-terminal,
real PTY, non-TTY, tmux, and official common-terminal rows disagree.
```

---

## 9. Revised task-specific scaffold for jplot

The next scaffold should organize repair around branch ownership, not row names.

```text
JPlotProgram
  ├─ ControlPlane
  │   └─ flag presence vs resolved value
  ├─ SourceProcess
  │   └─ URL polling, interval cadence, signals, cleanup
  ├─ TerminalSubstrate
  │   ├─ env terminal
  │   ├─ real PTY
  │   ├─ tmux/screen
  │   └─ no-source precedence under each substrate
  ├─ ProtocolWitness
  │   ├─ startup query witnesses
  │   ├─ image/protocol witnesses
  │   └─ branch-scoped witness suppression
  ├─ RenderTransform
  │   ├─ data morphology
  │   ├─ marker/counter overlay
  │   ├─ multi-series identity/color
  │   ├─ rows/height geometry
  │   └─ observable success denominator
  ├─ ObserverHorizon
  │   ├─ first output
  │   ├─ steady-state loop
  │   ├─ signal handling
  │   └─ teardown/readability
  ├─ ResourceEcology
  │   ├─ process lifetime
  │   ├─ HTTP connection lifetime
  │   ├─ fixed-port collision
  │   ├─ parallel/rerun schedule
  │   └─ cleanup proofs
  └─ HarnessSideEffects
      ├─ coverage artifact
      └─ evaluator-only conflict ledger
```

Implementation ownership should map to these modules only after probes P0-P6 are locked:

```text
startup_gate_driver
source_process_manager
terminal_session_manager
protocol_witness_emitter
render_transform_engine
success_oracle_adapter
resource_cleanup_guard
harness_side_effect_ledger
```

---

## 10. Handoff readiness at score 98

| Branch | Readiness state | Reason |
|---|---|---|
| Clocked URL process | scoped-ready / mostly implementation-transferred | Repeated fetch, signal, EOF rows were fixed. |
| Flag presence vs default | scoped-ready | Explicit-vs-implicit steps split fixed rows. |
| PTY/non-PTY source horizon | scoped-ready but observer-horizon incomplete | PTY rows improved, but clear-scrollback row still exits too early. |
| Startup protocol witness | scoped-ready with overreach risk | Fixed four rows, but now needs witness-scope gate. |
| Resource ecology | probe-ready, not implementation-ready | Remaining port failures occur before product branch observation. |
| Render transform success | probe-ready, not implementation-ready | Direct render success rows still fail. |
| Terminal no-source conflict | conflict-isolated | Public scout and official pressure disagree by substrate. |
| Coverage artifact | post-eval support only / harness-surface probe-needed | Not clean product evidence. |
| Tmux Ctrl-C | dependent-blocked | Skip depends on parent tmux observable branch. |

---

## 11. Recommended next sequence

Do not patch source first. Generate probes in this order:

```text
1. P0 Resource ecology interference graph
2. P2 Protocol witness scope and suppression
3. P1 Render-transform success matrix
4. P4 Observer horizon / loop persistence
5. P3 Terminal source-precedence conflict matrix
6. P5 Harness-side artifact probe
7. P6 Tmux dependent lane
```

Then patch only branches that have moved to scoped implementation-ready.

Likely score movement:

```text
P0 + resource cleanup / process lifecycle repair
  may unmask or fix the six fixed-port rows.

P1 + render-success repair
  targets five direct render rows and some rows currently masked by P0.

P2 + witness scoping
  targets the --steps expected-window-size row.

P4 + observer horizon
  targets clearscrollback persistence.

P3 conflict isolation
  prevents terminal no-source rows from causing broad regressions.

P5/P6
  should be handled as harness/dependent branches rather than primary product
  semantics unless probes prove otherwise.
```

---

## 12. Bottom line

The 93 -> 98 ladder confirms that v9's meta-program was directionally correct: score moved when repairs promoted missing parent discriminators rather than row patches.

But the 98 residue shows that v9 still lacks several executable gates:

```text
resource ecology as a graph, not a note
render success as an explicit oracle, not only bytes
protocol witnesses as scoped obligations, not global prefixes
observer horizons as external contracts, not arbitrary sleeps
harness side effects as warrant-bearing surfaces
conflicted substrate rows as conflict ledgers, not global laws
```

The proposed v10 revision should add those gates generically, while keeping the task-specific facts attached to the jplot artifact and authority layer.
