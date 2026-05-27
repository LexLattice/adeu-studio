# Principled Recursive ODEU Meta-Program Experimental v35

Authority layer: support / experimental meta-program revision.

This v35 patch extends:

```text
docs/support/principled_recursive_odeu_meta_program_experimental_v32.md
docs/support/general_program_ontology_derived_v1_5.md
```

It integrates the `sibprogrammer__xq.b89f681` adversarial pre-eval experiment:

```text
artifacts/manual_runs/programbench_xq_v32_gpt55_medium_clean_20260525T014351+0300/adversarial_pre_eval_experiment/adversarial_pre_eval_comparison_closeout.md
.codex/review-shell/chatgpt-downloads/xq_adversarial_pre_eval_codex_review_v35-7.md
```

The core lesson:

```text
A phase is not ready merely because its positive artifact is complete.
It is ready only if an adversarial sibling-omission pass fails to find an
unwarranted next-phase blocker.
```

## 1. New Gate Family

Add:

```text
ADVERSARIAL_PRE_EVAL_OMISSION_GATE
```

Purpose:

```text
Before a phase transition, ask an independent reviewer to find behavior-bearing
siblings that the current artifact did not cover, merge, defer, or prove
irrelevant.
```

This gate is a phase-transition proof, not optional polish. It checks whether
the current ontology, scout, probe, or witness artifact has silently dropped
active behavior families.

## 2. Required Insertion Points

### 2.1 Post-Scout / Pre-Lock Delta Gate

```text
PUBLIC_SCOUT_TO_MANIFEST_DELTA_GATE
```

Inputs:

```text
public scout observations
current ontology / HOB activation
candidate probe manifest draft
```

Question:

```text
Which behavior-bearing scout observations are absent from the manifest?
```

Blocking rule:

```text
Every behavior-bearing scout observation omitted from the locked manifest must
be promoted, merged into a proved equivalence class, deferred with named risk,
or proved irrelevant.
```

This is the highest-yield insertion point. It prevents a broad scout from being
collapsed into a narrow representative manifest without an accountable omission
ledger.

### 2.2 Post-Lock Manifest Red-Team Gate

```text
REPRESENTATIVE_MANIFEST_RED_TEAM_GATE
```

Inputs:

```text
locked probe contract
scout ledger
ontology / HOB obligation tree
```

Question:

```text
Does this manifest prove the behavior family, or only representative examples?
```

Blocking rule:

```text
A probe manifest that calls itself representative cannot become implementation-
ready unless residual sibling families are explicitly scoped and accepted.
```

### 2.3 Local-Green Pre-Official Witness-Shape Gate

```text
LOCAL_GREEN_WITNESS_SHAPE_AUDIT
```

Inputs:

```text
local green candidate
implementation source or black-box behavior
locked manifest
known active sublanguages / renderers / routes
```

Question:

```text
Does the witness implement a generative behavior family, or only narrow
fixture-shaped mechanisms?
```

Blocking rule:

```text
Local 100% against locked probes does not imply official readiness if the
witness audit finds literal switches, fixture-shaped parsers, narrow renderer
logic, or absent public-surface mechanisms for active sublanguages.
```

## 3. Revised ProgramBench Sequence

The v35 ProgramBench loop becomes:

```text
P1A blind task-native ontology
P1B GPO projection
P1C intent / utility projection
P1D reciprocal diff
P1E merged activation / inherited obligations
P2 public scout
P2B post-scout adversarial delta gate
P3 probe contract
P3B manifest red-team gate
P4 implementation handoff
P5 local green
P5B witness-shape adversarial audit
P6 official eval posture authorization
```

The adversarial gate does not replace reciprocal GPO/task-native diff. It is a
second guard at the point where conceptual coverage becomes probes and probes
become witness authority.

## 4. Salience-Breaking Generic Probes

The `xq` experiment showed that adversarial workers can still stay inside the
README/scout salience cone. Two generic probes are now required where their
triggers apply.

### 4.1 Ambient Config Convention Probe

```text
AMBIENT_CONFIG_CONVENTION_PROBE
```

Trigger:

```text
CLI tool has config-like wording, debug/list modes, option defaults, command
name identity, or a domain where dotfile conventions are common.
```

Question:

```text
Can behavior be affected by ambient config files even without an explicit
--config argument?
```

Probe families:

```text
$HOME/.<cmd>
$HOME/.config/<cmd>/config
XDG_CONFIG_HOME/<cmd>/config
cwd-local config if plausible
explicit config vs ambient config precedence
invalid ambient config diagnostics
ambient config ignored/proved-irrelevant negative control
```

Closure rule:

```text
Config-like surfaces are not irrelevant merely because explicit config options
are absent or public scout did not make them salient. Ambient configuration must
be disproved, bounded, or deferred.
```

### 4.2 Format Role-Reversal Probe

```text
FORMAT_ROLE_REVERSAL_PROBE
```

Trigger:

```text
Any public format appears as input, output, conversion target, renderer,
serializer, printer, or autodetectable file extension.
```

Question:

```text
Is the format only a projection dialect, or can it also be an input,
autodetect, pass-through, parse, or convert dialect?
```

Probe families:

```text
format as output
format as input
format by extension autodetect
format through stdin autodetect if applicable
format under explicit flag
format as conversion source and target
format malformed input diagnostics
format roundtrip / tree preservation
```

Closure rule:

```text
A format advertised in one direction cannot be closed as renderer-only unless
the opposite direction has been tested, proved unsupported, or deferred.
```

## 5. Structured Document Transform CLI Profile

Add profile:

```text
STRUCTURED_DOCUMENT_TRANSFORM_CLI
```

Trigger when a program:

```text
reads structured documents;
selects nodes or paths through a selector language;
formats or converts markup/tree data;
mutates files in place;
routes multiple files/stdin/stdout;
prints to terminal/pager/color surfaces;
exposes JSON/XML/HTML-like input or output formats.
```

Inherited obligations:

```text
CONTROL_TOKEN_GRAMMAR
RESOURCE_ROUTE_AND_MUTATION_LIFECYCLE
SELECTOR_EXPRESSION_SUBLANGUAGE
STRUCTURED_DOCUMENT_PARSE_RECOVERY_GRAMMAR
MARKUP_FORMATTER_BYTE_GRAMMAR
FORMAT_DIRECTIONALITY_AND_TREE_PRESERVATION
DIAGNOSTIC_CHANNEL_EXIT_PRECEDENCE
TERMINAL_PAGER_COLOR_ECOLOGY
AMBIENT_CONFIG_TOPOLOGY
```

Do not promote task-specific leaves such as `.xq`, XPath, HTML void elements,
or CSS no-match into universal obligations. Promote their generic owners.

## 6. Required Artifact Schema

```yaml
adversarial_pre_eval_gate:
  gate_id: string
  insertion_point:
    post_phase1_ontology |
    post_public_scout_pre_lock |
    post_probe_lock |
    post_local_green_pre_official
  worker_input_ledger:
    allowed_refs: []
    forbidden_refs: []
    contamination_status: clean | contaminated | unknown
  omitted_behavior_families:
    - family_ref: string
      nearest_hob_node: string
      source_of_suspicion:
        task_native | gpo_prior | utility | scout_observation |
        manifest_gap | witness_shape | salience_breaker
      required_action:
        promote_to_manifest |
        merge_equivalence_class |
        prove_irrelevant |
        defer_with_named_risk |
        block_handoff
      example_probe_shapes: []
      sibling_risk: low | medium | high
  salience_breaker_results:
    ambient_config: pass | fail | blocked | not_applicable | deferred
    format_role_reversal: pass | fail | blocked | not_applicable | deferred
  transition_decision:
    allow_next_phase |
    allow_scoped_only |
    block_next_phase
```

## 7. Bookkeeper Rule

The transition bookkeeper must reject a transition if any of these are true:

```text
scout observation is behavior-bearing and absent from manifest;
probe manifest is called representative but sibling families are unscoped;
local green is used as official readiness while witness-shape audit flags
  literal or fixture-shaped implementation under an active open-domain family;
config-like surface is closed without ambient-convention disproof;
format is closed as output-only without directionality testing;
adversarial worker recommends block and orchestrator records only prose override.
```

Allowed override requires:

```text
explicit scope downgrade;
expected risk statement;
owned HOB nodes;
deferred probe rows;
posture label: scoped_experiment, not gold_attempt.
```
