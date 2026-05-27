# hwatch Codex Output Review — v34 Schema Integration

Authority layer: review over `final_hwatch_reconstruction_causal_story.md` plus prior hwatch audits.

## 1. Verdict

The Codex causal story is strong and should be promoted into the general schema. It is not merely a phase recap. It identifies the correct causal mechanism:

```text
hwatch was solved by treating it as a reactive CLI/TUI command scheduler,
then closing the high-score tail through transfer-boundary exactness.
```

The most important feature is that the story does not treat every official failure as product evidence at the same level. It separates:

```text
not-run / result-artifact failure
  -> execution-topology / observation-ecology evidence

full visible failures
  -> product ontology / implementation-owner evidence

score-98 tail
  -> transfer-boundary exactness evidence
```

That is exactly the layer discipline the meta-program has been trying to enforce.

## 2. What Codex got right

### 2.1 Correct parent program object

The decisive broad ontology is:

```text
REACTIVE_CLI_TUI_COMMAND_SCHEDULER
```

This is better than:

```text
generic CLI
flag parser
periodic command runner
terminal renderer
```

because it imports the right inherited child obligations:

```text
control-plane grammar
command boundary / child argv ownership
shell/direct-exec/template substrate
batch scheduler and lifetime law
batch renderer byte grammar
TUI control-terminal topology
TUI pane/history/filter/keymap state machine
diagnostic and liveness contracts
resource/log/aftercommand side effects
branch-result artifact liveness
```

This is the safe abstraction. Do not generalize task-specific keys or flag names; generalize the scheduler/control/substrate/liveness structure.

### 2.2 HOB remand prevented false parent closure

The story correctly emphasizes that recognizing the reactive parent was not enough. The HOB audit blocked implementation until children such as event-channel topology, scheduler startup/liveness, command boundary, child process supervision, interactive control terminal, aftercommand status subprogram, logfile topology, and diagnostic/exit law were accounted for.

General schema rule:

```text
Reactive parent recognition imports child obligations.
Representative batch/TUI/keymap examples do not close the parent.
```

### 2.3 Branch-result artifact liveness was diagnosed at the right layer

The score-52 run with many `not_run` rows was not treated as a hidden TUI product tail. It was classified as branch execution topology / result artifact liveness. That was the correct layer.

General schema rule:

```text
If result artifacts are missing or unreadable, do not interpret not-run rows as
product ontology evidence. First prove branch-result artifact liveness.
```

### 2.4 Runtime was used as semantic evidence

Once all branches were visible, the next blocker was not only failure count. The slow branch made full official eval too expensive as an inner loop. Runtime-weighted classification exposed parser/control errors that were accidentally entering live mode and burning time.

General schema rule:

```text
For reactive/TUI tasks, runtime cost is not merely operational noise.
It can identify the earliest wrong transition: parser fast-fail, flag ownership,
shell boundary, observer horizon, or true TUI state-machine behavior.
```

### 2.5 Repair order was causal, not cosmetic

The successful ordering was:

```text
1. parser/control and flag quarantine
2. shell/direct/template command substrate
3. batch renderer and ANSI byte domains
4. live TUI with local subtree harnesses
5. high-score transfer tail
```

This matters because later layers depend on earlier ownership:

```text
renderer correctness depends on child-command ownership;
TUI exactness depends on renderer and process/liveness stability;
batch lifetime depends on whether tokens belong to parser control or child argv;
byte overlays depend on accepted control state propagation.
```

### 2.6 The score-98 tail was correctly reframed

The score-98 tail was not broad missing TUI behavior. It was adjacent transfer-boundary exactness:

```text
control token -> value token
control region -> command payload region
reactive stream -> bounded noninteractive sample
parsed option state -> renderer byte surface
semantic ANSI span -> raw diff byte domain
config source -> parser conflict law
control sublanguage validation -> runtime/liveness timing
```

This is the key high-score lesson.

## 3. What should be generalized into the program ontology

Add the following class to the general ontology catalog.

### 3.1 `REACTIVE_CLI_TUI_COMMAND_SCHEDULER`

Trigger when a program:

```text
runs or re-runs commands on an interval or event;
maintains a live loop;
has batch and interactive/TUI modes;
controls child processes;
projects changing command output;
uses PTY, tmux, keyboard, mouse, or terminal control;
has shell/direct-exec/template command forms;
has aftercommands, logs, history, pane navigation, filters, or keymaps.
```

Inherited children:

```text
1. control-plane grammar and token-region authority
2. command boundary and child argv ownership
3. shell/direct-exec/template substrate
4. child process supervision and signal/exit law
5. batch/noninteractive lifetime contract
6. batch renderer and ANSI byte grammar
7. TUI control-terminal topology
8. TUI pane/history/filter/keymap state machine
9. log/aftercommand/resource side effects
10. diagnostic/fatal/liveness contracts
11. observation ecology and branch-result artifact liveness
12. runtime-weighted repair planning
13. high-score transfer-boundary exactness
```

## 4. New v34 gates to add

### 4.1 `ORACLE_VISIBILITY_STATE_GATE`

Purpose:

```text
Classify whether an official run is measuring product behavior, observation
liveness, branch artifact production, or high-score tail exactness.
```

States:

```text
artifact_not_readable
branch_not_run
full_visibility_product_pressure
runtime_weighted_product_pressure
high_score_transfer_tail
final_green
```

Blocking rule:

```text
Do not patch product ontology from not-run rows until the visibility state is
full_visibility_product_pressure or better.
```

### 4.2 `BRANCH_RESULT_ARTIFACT_LIVENESS_GATE`

Trigger:

```text
results.xml missing/unreadable;
large not_run count;
branch error;
TUI/tmux/timeout-heavy branch;
long branch duration with partial visible progress.
```

Required row:

```yaml
branch_result_artifact_liveness:
  branch_id: string
  not_run_count: int
  branch_duration: string
  product_behavior_reached: yes | no | uncertain
  result_artifact_path: string
  artifact_written: yes | no | partial | unknown
  process_tree_clean: yes | no | unknown
  tmux_pty_state: clean | contaminated | unknown
  timeout_density: low | medium | high
  first_layer_owner: observation_ecology | candidate_liveness | harness | unknown
  product_tail_authorized: true | false
```

### 4.3 `RUNTIME_WEIGHTED_REACTIVE_TRIAGE_GATE`

Trigger:

```text
reactive/TUI branch runtime dominates feedback loop.
```

Required split:

```text
semantic owner: what behavior is wrong
runtime owner: why observing it costs time
```

Required categories:

```text
should_have_fast_failed
flag_leaked_to_child
shell_template_wait
batch_lifetime_wait
true_tui_state_wait
observer_horizon_wait
cleanup_contamination
```

### 4.4 `TOKEN_REGION_AUTHORITY_GATE`

Purpose:

```text
Decide whether each token belongs to parser control, option value, command
payload, shell template, keymap sublanguage, or config/env overlay.
```

This must run before batch lifetime and child command repair.

### 4.5 `OPTION_ARITY_AND_VALUE_CLASS_GATE`

Purpose:

```text
For every option, classify required value, optional value, forbidden value,
repeatable value, command-consuming value, and invalid-value behavior.
```

Surfaces:

```text
rc
stdout
stderr
help/usage routing
whether product execution starts
whether TUI/live mode is entered
```

### 4.6 `COMMAND_SUBSTRATE_GATE`

Purpose:

```text
Treat watched command execution as an embedded substrate, not a string append.
```

Substrate children:

```text
default shell string
custom shell wrapper
placeholder template
direct argv exec
aftercommand helper program
shell-vs-direct diagnostics
child exit vs parent exit policy
```

### 4.7 `BATCH_LIFETIME_CONTRACT_GATE`

Purpose:

```text
Split noninteractive reactive mode into bounded samples, bounded multi-frame
samples, persistent streams, command-error liveness rows, parser fast-fail, and
child-error parent-success rows.
```

Do not globally make batch one-shot or globally persistent.

### 4.8 `REACTIVE_RENDERER_BYTE_DOMAIN_GATE`

Purpose:

```text
Separate byte domains before renderer repair.
```

Byte domains:

```text
raw command bytes
selected stdout/stderr/output projection
terminal ANSI control sequences
line diff
word diff
watch diff
line-number overlay
reverse/tab/display transformations
TUI state rendering
```

### 4.9 `LOCAL_TUI_SUBTREE_HARNESS_GATE`

Purpose:

```text
Full official eval must not be the inner loop for high-latency interactive
state machines.
```

Required local harnesses when applicable:

```text
tmux/libtmux parity harness
tui2cli/key feeding harness
pane focus/navigation harness
history accumulation harness
filter/keymap harness
help modal harness
observer-horizon harness
```

### 4.10 `HIGH_SCORE_TRANSFER_TAIL_GATE`

Trigger:

```text
score >= high threshold and remaining failures are compact.
```

Rule:

```text
At high score, broad owner patches are forbidden unless row ownership proves
that the broad owner is still the earliest active failure layer.
```

Required row:

```yaml
high_score_tail_row:
  failure_ref: string
  primary_transfer_boundary: token_region | option_arity | lifetime | renderer_state | byte_domain | config_merge | validation_timing | other
  primary_owner: string
  preservation_sentinels: []
  forbidden_patch_classes: []
  local_tail_probe_refs: []
  official_authorization: scoped_tail | gold_tail
```

## 5. Integration with the existing HOB hierarchy

Recommended new top-level class:

```text
13 Reactive scheduler / interactive command programs
```

Suggested children:

```text
13.1 Event-channel topology
13.2 Config stream vs control stream
13.3 Command boundary and argv ownership
13.4 Shell/direct/template substrate
13.5 Child process supervision
13.6 Batch/noninteractive lifetime law
13.7 Batch renderer and ANSI byte grammar
13.8 TUI control-terminal topology
13.9 TUI state-machine surfaces
13.10 Logs / aftercommands / side effects
13.11 Diagnostic, exit, and liveness law
13.12 Observation ecology / result artifact liveness
13.13 Runtime-weighted repair planning
13.14 High-score transfer tail
```

This complements the earlier `entr` reactive scheduler class. `entr` emphasized filesystem event topology, watch-list stream, command substitution, status filters, process ecology, and PTY control. `hwatch` emphasizes child-command substrate, batch/TUI duality, renderer byte domains, runtime-weighted branch triage, and high-score tail transfer exactness.

## 6. Minor hardening patches for the Codex story

The Codex story is promotion-ready, but I would patch the final artifact in four places before using it as a canonical exemplar.

### 6.1 Add a phase-transition table

The prose is clear, but the orchestrator needs machine-checkable rows:

```yaml
phase:
  input_artifacts:
  transition_gate:
  allowed_next_phase:
  blocked_next_phase:
  evidence_status:
  product_tail_authorized:
  implementation_handoff_type:
```

### 6.2 Add explicit negative-history ledger

The story should record any rejected broad patch classes, even if they were minor, in the same durable way the trdsql run recorded rejected broad TBLN inference. If no broad patch was rejected, say so explicitly.

### 6.3 Split “Average 100” from “full green”

The story correctly records the intermediate Batch 5 run as `✅ / Average 100` with `1318 passed / 3 failed`, then final Batch 5b as `1321 / 1321`. This distinction should be preserved as a general gate:

```text
rounded score 100 != solved checkmark unless parsed rows are green.
```

### 6.4 Make post-eval test-file use a named authority state

The story says extracted eval test files and branch workspace were used only after official surfaces authorized tail repair. That should become a named state:

```text
post_eval_tail_authorized_source_surface
```

so future orchestrators do not accidentally treat test-file inspection as clean first-pass evidence.

## 7. Final schema sentence

The safe abstraction from hwatch is:

```text
For reactive CLI/TUI command schedulers, reconstruction must first prove the
reactive program object, then prove the transfer boundaries between parser,
command substrate, scheduler lifetime, renderer byte domains, interactive
control topology, and observation liveness. High-score tails are usually not
new ontology parents; they are transfer-boundary exactness obligations.
```

This should become the v34 addition to the general program ontology.
