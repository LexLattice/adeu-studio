# hwatch Phase18 v33 Tail Schema Integration Review

Authority layer: post-eval audit review / meta-program patch proposal.

Input reviewed:

- `phase18_remaining_failure_audit.md`
- Phase17/18 official result described in the audit: score `98`, `1285 passed / 36 failed / 1321 total`.

No candidate source files were modified.

---

## 1. Verdict

The Phase18 audit is strong and should be integrated. It correctly recognizes that the remaining 36 failures are not a broad missing ontology for `hwatch`. The broad class is already right:

```text
hwatch = reactive TUI / batch command scheduler
```

The tail lives below that broad class, in adjacent layer-transfer rules:

```text
control token -> value token
control region -> command payload region
reactive stream -> bounded noninteractive sample
parsed option state -> renderer byte surface
semantic ANSI span -> raw diff byte domain
```

This is the important generalization: at high score, remaining failures often move from **program-class discovery** to **transfer-boundary exactness**.

For `hwatch`, the next schema revision should therefore add a late-stage gate:

```text
REACTIVE_CLI_TUI_REGION_AND_LIFETIME_TAIL_PASS
```

This gate should be mandatory when a reactive CLI/TUI program reaches a high score but still has failures involving batch mode, command payloads, option arity, TUI display flags, keymaps, or diff/ANSI exactness.

---

## 2. What the audit gets right

The audit’s high-level grouping is correct. The tail is concentrated in three terminal discriminator families:

```text
1. batch-mode lifetime law
2. parser / control-token ownership
3. byte-exact compatibility overlays
```

It also correctly notes that the earlier evaluator-topology problem is gone: this run has no branch errors, no warnings, and no missing result artifacts. That matters because the 36 rows are now usable product-tail pressure rather than hidden branch-liveness pressure.

The failure map is coherent:

| Group | Count | Better parent |
|---|---:|---|
| Batch mode times out after producing output | 16 | `NONINTERACTIVE_REACTIVE_COMPLETION_CONTRACT` |
| Missing / invalid option values | 11 | `OPTION_ARITY_VALUE_CLASS_GATE` |
| Command-boundary / help / subcommand handling | 4 | `TOKEN_REGION_AUTHORITY_GATE` |
| Env/config duplicate option validation | 1 | `CONFIG_CLI_MERGE_VALIDATION_GATE` |
| TUI help-banner propagation | 1 | `ACCEPTED_CONTROL_TO_RENDERER_STATE_GATE` |
| Keymap multiplicity / malformed action boundary | 1 | `CONTROL_SUBLANGUAGE_VALIDATION_TIMING_GATE` |
| ANSI watch-diff raw byte grammar | 1 | `DIFF_DOMAIN_SELECTION_GATE` |
| Diff flag without value | 1 | overlaps `OPTION_ARITY_VALUE_CLASS_GATE` and `REACTIVE_LIVENESS_GATE` |

The root-cause summary is also right: `batch` was modeled as one persistent reactive stream; parser arity was not terminalized; command boundary was not first-class; and a few accepted controls did not propagate to their byte surfaces.

---

## 3. Main correction to the audit

The audit contains a mild order tension.

Near the top it says the practical repair order should be:

```text
1. batch lifetime law
2. parser/control-token ownership
3. small compatibility overlays
```

But its concrete recommended batches are:

```text
Batch 5A: parser region and arity gate
Batch 5B: batch lifetime matrix
Batch 5C: terminal overlays
```

I would resolve this as follows:

```text
method-safe order:
  5A parser region / arity first
  5B batch lifetime second
  5C overlays third

score-fast order, only if parser sentinels are imported:
  5B batch lifetime first
  5A parser region / arity second
  5C overlays third
```

Why parser first is safer:

- Some batch failures involve tokens that look like options but are actually command payloads.
- Batch lifetime cannot be safely classified until region ownership says whether a token belongs to parser, option value, or child command.
- Parser fast-fail rows can also reduce full-eval time by preventing invalid controls from entering live mode.

So the schema should not hand the worker “fix batch” as a free-standing patch unless the parser-region sentinels are already locked and imported.

---

## 4. Schema integration

### 4.1 Add to HOB class 1: Invocation and control-plane grammar

Add child nodes:

```text
1.x TOKEN_REGION_AUTHORITY
  Distinguishes option-control region, option-value region, command-payload
  region, and post-separator region.

1.x OPTION_ARITY_VALUE_CLASS
  For each option: required value, optional value, forbidden value, repeatable,
  command-consuming, dash-prefixed value allowed/disallowed, equals-form allowed.

1.x REGION_AWARE_HELP_AND_UNKNOWN_TOKEN
  Help/version/unknown-token authority is valid only in specific regions.
  After command boundary, formerly special tokens can become child argv bytes.

1.x CONFIG_CLI_MERGE_VALIDATION
  Environment/config/default tokens merge into the same parser conflict law as
  CLI tokens unless proven shadowed, overridden, or accumulated.
```

These nodes prevent the common mistake:

```text
recognized option spelling = global authority over all argv tokens
```

Correct rule:

```text
an option spelling has authority only in its active token region.
```

### 4.2 Add to HOB class 7: State, lifecycle, mutation, and event law

Add:

```text
7.x NONINTERACTIVE_REACTIVE_COMPLETION_CONTRACT
```

It splits each noninteractive reactive mode into:

```text
bounded sample
bounded multi-frame sample
persistent stream
explicit timeout/liveness probe
child-error liveness branch
fatal parser branch
```

The audit’s batch rows show this exactly: many ordinary `-b ... command` invocations produced expected frames but then timed out, while some special command-payload/error shapes must remain live or timeout-expected.

### 4.3 Add to HOB class 8: Output router, renderer, and byte grammar

Add:

```text
8.x ACCEPTED_CONTROL_TO_RENDERER_STATE
  Every accepted display-control option must have storage, propagation, and
  renderer parameterization rows.

8.x DIFF_DOMAIN_SELECTION
  Diff surfaces must declare whether the comparison domain is raw bytes,
  Unicode scalar values, grapheme clusters, visible cells, ANSI-normalized
  semantic spans, or another domain.
```

The `--no-help-banner` row is a state-propagation miss. The ANSI watch-diff row is a diff-domain miss.

### 4.4 Add to HOB class 5 or reactive sublanguage nodes

Add:

```text
CONTROL_SUBLANGUAGE_VALIDATION_TIMING
```

This applies to keymaps and similar mini-languages. It asks:

```text
Does invalid-looking syntax fail at parse time,
become an inert mapping,
accumulate with later valid mappings,
or defer failure until runtime/use?
```

This is important because a high-level “keymap parser” can be mostly correct while still failing exactly where validation timing differs from the reference.

### 4.5 Add to HOB class 12: Orchestration, handoff, and preservation governance

Add:

```text
HIGH_SCORE_TAIL_EXACTNESS_PASS
```

Trigger:

```text
score >= high-score threshold, broad ontology stable, failures <= compact tail,
and remaining failures are adjacent-layer transfer issues.
```

Required row fields:

```yaml
failure_row_ref: string
primary_hob_node: string
adjacent_transfer_boundary:
  token_to_value |
  token_region_to_command_region |
  stream_to_bounded_sample |
  option_state_to_renderer |
  semantic_span_to_raw_byte_domain |
  config_source_to_parser_conflict_law |
  sublanguage_validation_to_runtime_liveness
implementation_owner: string
preservation_sentinels: []
patch_class: bounded_microgrammar | lifetime_law | parser_region | renderer_overlay | byte_domain_overlay
allowed_scope: string
forbidden_patch_classes: []
closure_probe_refs: []
```

Blocking rule:

```text
At high-score tail, no broad owner rewrite is allowed without a row-level
transfer-boundary assignment and preservation sentinel set.
```

---

## 5. Proposed v33 gates

### G33.1 `REACTIVE_CLI_TUI_REGION_AND_LIFETIME_TAIL_PASS`

Mandatory for reactive CLI/TUI tools when a late tail contains batch, command boundary, keymap, TUI, ANSI, or parser-liveness failures.

Question set:

```text
For each accepted token and mode:
  What region owns it?
  What event ends that region?
  What values are required, optional, forbidden, repeatable, or command-consuming?
  Does this mode terminate naturally, stream forever, or rely on observer timeout?
  Does this output byte surface operate on raw bytes, decoded text, visible cells,
  or semantic spans?
```

### G33.2 `OPTION_ARITY_VALUE_CLASS_GATE`

Every option gets a row:

```yaml
option: string
required_value: true|false
optional_value: true|false
forbids_value: true|false
repeatable: true|false
dash_prefixed_value_allowed: true|false|unknown
equals_form_allowed: true|false|unknown
missing_value_exit: int|string
missing_value_stream: stdout|stderr
invalid_value_exit: int|string
invalid_value_stream: stdout|stderr
parser_or_runtime_validation: parser|runtime|deferred
```

### G33.3 `TOKEN_REGION_AUTHORITY_GATE`

Every argv token must be classified into a region:

```text
option-control region
option-value region
command-payload region
post-`--` command region
subcommand-like payload region
```

Special tokens such as `--help`, `-h`, `--unknown`, and `--differences` must be probed in at least two regions before global behavior is inferred.

### G33.4 `NONINTERACTIVE_REACTIVE_COMPLETION_CONTRACT`

Every noninteractive reactive mode must split:

```text
ordinary bounded command
ordinary multi-frame command
command failure
unknown-command payload
explicit liveness/timeout case
invalid parser case
```

Closure requires stdout/stderr/exit and process lifetime, not only rendered bytes.

### G33.5 `CONFIG_CLI_MERGE_VALIDATION_GATE`

Environment/config/default tokens are not merely prepended strings. They participate in parser semantics:

```text
duplicate non-repeatable -> error?
CLI overrides env -> allowed?
env shadows CLI -> allowed?
repeatable accumulates -> allowed?
source-specific diagnostic -> required?
```

### G33.6 `ACCEPTED_CONTROL_TO_RENDERER_STATE_GATE`

For every accepted display option:

```text
parser accepts it
state stores it
mode builder receives it
renderer consumes it
byte grammar changes only where scoped
```

### G33.7 `DIFF_DOMAIN_SELECTION_GATE`

Diff renderer branches must declare the diff domain:

```text
raw bytes
UTF-8 decoded text
Unicode scalar values
grapheme clusters
terminal display cells
ANSI-tokenized semantic spans
ANSI raw escape fragments
```

No global ANSI rewrite is allowed unless all relevant branches share the same domain.

### G33.8 `CONTROL_SUBLANGUAGE_VALIDATION_TIMING_GATE`

For mini-languages such as keymaps:

```text
syntax accepted / rejected
semantic action accepted / rejected
unknown action tolerated / inert / runtime-only
multiple declarations union / replace / error
duplicate key first-wins / last-wins / error
```

---

## 6. Repair scaffold for this hwatch tail

### Batch 0: no-code exact tail ledger

Before source patches:

```text
1. Attach each of the 36 rows to the v33 HOB node above.
2. Mark implementation owner: cli_parser, env_config_merge, batch_runtime,
   command_builder, tui_renderer, keymap_parser, diff_renderer.
3. Import preservation sentinels for already-green help, batch, TUI, keymap,
   diff, shell, and flag-quarantine rows.
4. Decide whether each row is parser-region, lifetime-law, renderer-overlay,
   validation-timing, or byte-domain.
```

### Batch 5A: parser region and arity

Primary owners:

```text
cli_parser
command_boundary_classifier
env_config_merge
```

Target:

```text
missing --interval / --limit / --tab-size / --shell / --aftercommand / --keymap
invalid --border=foo
add --help
-- --help
--batch --unknown
--batch --nonexistent-flag
--batch -- --nonexistent-flag
--differences without value
HWATCH + CLI duplicate --batch
```

Must preserve:

```text
top-level --help and -h behavior
ordinary command payloads
already-green unknown-token branches
shell/template command construction
recognized display flags consumed before child argv
```

### Batch 5B: batch lifetime matrix

Primary owners:

```text
batch_runtime
scheduler_lifetime_law
command_result_policy
```

Target:

```text
ordinary tests.test_batch.* rows with rc -1 timeout after expected output
```

Rule:

```text
Do not globally make batch one-shot.
Classify each batch invocation as bounded sample, bounded multi-frame sample,
persistent stream, or explicit timeout/liveness probe.
```

### Batch 5C: terminal overlays

Primary owners:

```text
tui_renderer
keymap_parser
diff_renderer
```

Target:

```text
--no-help-banner
keymap-multiple
ANSI changed-char watch diff
small remaining optional-value/liveness overlays
```

Patch style:

```text
branch-local overlays only;
no broad parser, TUI, keymap, or ANSI renderer rewrite.
```

---

## 7. Generalization beyond hwatch

The safe generic abstraction is not:

```text
hwatch batch needs rc0
hwatch keymap accepts unknown actions
hwatch ANSI diff includes CSI fragments
```

Those are task-specific.

The safe generic abstraction is:

```text
Reactive CLI/TUI programs have late tail failures at token-region, mode-lifetime,
state-propagation, validation-timing, and byte-domain boundaries.
```

This should be applied to any program that has one or more of:

```text
batch mode
watch / repeat / interval mode
child command execution
shell template execution
TUI key handling
config/env-injected argv defaults
keymap or shortcut sublanguage
ANSI/color/diff rendering
noninteractive mode that may either finish or stream
```

In such programs, a high-score tail pass must ask:

```text
Where does parser authority end?
Where does command payload ownership begin?
Which controls are parser errors versus runtime/liveness conditions?
Which modes are naturally bounded?
Which rendered surfaces are raw-byte exact rather than semantic-display exact?
```

---

## 8. Integration with prior reactive-program lessons

This extends the earlier `entr` lesson. `entr` showed that reactive tools need event-channel topology, command boundary, resource mutation, process supervision, and liveness/exit law. `hwatch` adds a later-stage refinement:

```text
Once broad reactive topology is correct, gold-tail failures often concentrate
in region ownership and lifetime exactness rather than new event classes.
```

So the reactive program class should now be split into two stages:

```text
Stage R1: broad reactive ontology
  event channels, resources, command boundary, child lifecycle, TUI/PTY,
  diagnostics, liveness/exit.

Stage R2: high-score transfer exactness
  token region, option arity, env/CLI merge, bounded vs persistent modes,
  display-control propagation, validation timing, byte-domain choice.
```

---

## 9. Readiness posture

The score-98 run should be classified as:

```text
broad_program_ontology_gold_ready: mostly yes
reactive_tail_transfer_ready: not yet
batch_lifetime_law_ready: probe-ready / implementation-ready after parser sentinels
parser_region_arity_ready: implementation-ready with preservation sentinels
byte_overlay_ready: implementation-ready as branch-local overlays
full_gold_closeout: blocked until 36-row tail ledger is exact
```

The remaining work is not exploratory ontology discovery. It is compatibility-theorem finishing.

---

## 10. One-sentence v33 rule

```text
For reactive CLI/TUI programs, a high-score tail cannot be closed by broad
scheduler, parser, or renderer patches; it must be closed by row-owned transfer
rules for token region, option arity, mode lifetime, state propagation,
validation timing, and byte-domain selection.
```
