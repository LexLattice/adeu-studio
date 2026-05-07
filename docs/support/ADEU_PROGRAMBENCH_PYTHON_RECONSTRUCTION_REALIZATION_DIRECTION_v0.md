# ADEU ProgramBench Python Reconstruction Realization Direction v0

Status: support / practical direction.

Authority layer: support.

This note records the practical post-`V85` ProgramBench direction. It is not a
selector, lock, implementation authority, benchmark-truth claim, ProgramBench
submission authority, source-ingestion authority, decompilation authority,
internet-use authority for benchmark tasks, or release authority.

## External Benchmark Context

ProgramBench is a cleanroom reconstruction benchmark. Current public
descriptors say the agent receives an execute-only compiled program plus usage
documentation, without source code, internet access, decompilation, prescribed
language, file layout, or skeleton. The agent probes observable behavior and
submits a replacement program evaluated against hidden behavioral tests.

Public benchmark descriptors also report a 2026 snapshot with 200 tasks,
248,853 behavioral tests, and all public models at 0% fully resolved in the
initial display snapshot.

Sources:

- `https://benchlm.ai/blog/posts/programbench-cleanroom-coding-benchmark`
- `https://benchlm.ai/benchmarks/programBench`

Suggested public descriptor observation shape:

```text
public_descriptor_observation@1
  retrieved_at
  source_url
  observed_descriptor
  advisory_only
  not_used_as_evaluation_truth
```

For this support note, `retrieved_at = 2026-05-06` and both source URLs above
are advisory context only.

ADEU should treat these public descriptors as benchmark context, not as
benchmark truth, task truth, hidden-test evidence, or implementation authority.

## Core Thesis

Python is a useful first reconstruction substrate because current models have
strong priors over it. Python is not the architectural point. The architectural
point is the bridge:

```text
canonical program concept
  -> language-specific realization options
  -> implementation obligations
  -> code idioms / stdlib surfaces
  -> witness probes
```

The concept database and the language realization overlay must remain distinct:

```text
Canonical ODEU Concept DB:
  defines what the concept is

Language Realization Overlay:
  defines how this concept can be lawfully instantiated in code
```

For example, `config_precedence` is not "Python dict merge." It is a program
law concept. In Python it may be realized through defaults, config file values,
environment variables, CLI flags, a merge function, a dataclass resolver,
`argparse` normalization, or an explicit precedence resolver.

## Candidate Record Shape

Recommended support shape:

```text
ConceptRealizationRecord@1
  concept_id
  target_language
  realization_role
  canonical_instruction
  preferred_stdlib_surfaces
  implementation_patterns
  contraindicated_patterns
  boundary_conditions
  failure_modes
  required_witnesses
  probe_templates
  example_snippets_advisory
```

Example:

```text
concept_id: stderr_diagnostic
target_language: python

canonical_instruction:
  Diagnostic text must be written to stderr, not stdout.

preferred_stdlib_surfaces:
  sys.stderr.write(...)
  print(..., file=sys.stderr)

contraindicated_patterns:
  bare print(...) for diagnostics
  uncaught traceback unless traceback behavior is witnessed

required_witnesses:
  stdout/stderr separation probe
  exit-code probe
```

Example:

```text
concept_id: cli_flag_value
target_language: python

preferred_stdlib_surfaces:
  argparse.add_argument("--flag")
  manual sys.argv parser if argparse formatting conflicts with oracle

boundary_conditions:
  missing value
  repeated flag
  unknown flag
  short/long aliases
  flag precedence over config/env

required_witnesses:
  --help probe
  missing-value probe
  invalid-flag probe
  repeated-flag probe
```

## ProgramBench Circuit

The target practical circuit:

```text
cleanroom evidence
  -> ProgramODEUProfile
  -> concept boundaries
  -> language realization plan
  -> implementation
  -> probe/equivalence audit
```

The worker should derive:

```text
Program has these O entities and D obligations,
and these language-level construction primitives
can implement each obligation with known edge probes.
```

That is stronger than:

```text
model, please code the inferred behavior
```

## Initial Concept Boundary Seeds

The first ProgramBench-facing O-lane seed should be explicit, even before
Python realization records exist:

```text
program_behavior
command
subcommand
cli_flag
positional_argument
stdin_input
stdout_output
stderr_diagnostic
exit_code
config_file
environment_variable
default_value
precedence_rule
parser_error
runtime_error
generated_output_artifact
filesystem_side_effect
probe_log
```

These seeds define review inventory pressure only. A seed row is not proof that
a concrete task contains the concept, and an incomplete boundary is not a
license to infer code behavior.

## Cleanroom Phase Separation

The ProgramBench-shaped lane should preserve four distinct phases:

```text
inference_phase:
  cleanroom-visible evidence only

local_development_phase:
  worker-generated probes/tests allowed
  still no forbidden evidence

evaluation_phase:
  hidden tests may judge artifact
  hidden tests are external court, not inference evidence

postmortem_phase:
  evaluation failures may inform harness research only under dev posture
  not retroactively admitted as inference evidence
```

## First Python Realization Pack

The first pack should stay tiny and Python standard-library-heavy:

```text
CLI:
  argparse, sys.argv, subparsers, manual parsing fallback

I/O:
  sys.stdin, sys.stdout, sys.stderr, pathlib, open(...)

Data/config:
  json, csv, configparser, tomllib, os.environ

Behavior:
  exit codes, deterministic sorting, text/binary mode, glob/path handling

Errors:
  parse error, missing file, malformed config, permission failure

Artifacts:
  stdout text, stderr diagnostics, generated files, directory side effects
```

The first practical arc should not attempt full ProgramBench participation.
Recommended name:

```text
PB-PY-0:
  ProgramBench Python Reconstruction Realization Pack
```

## Comparison Design

The minimum useful evaluation comparison:

```text
A. ADEU base harness
   cleanroom docs/probes -> direct Python implementation

B. ADEU + conceptual broker
   cleanroom docs/probes -> ProgramODEUProfile -> direct Python implementation

C. ADEU + conceptual broker + Python realization overlay
   cleanroom docs/probes -> ProgramODEUProfile -> PythonReconstructionPlan -> implementation
```

This isolates the value of the new components:

```text
B > A:
  conceptual retrieval / profile recovery helps

C > B:
  concept-to-code realization overlay helps
```

## Boundary Laws

For this support direction:

- Python realization guidance is advisory until selected by a later lock.
- Example snippets are not canonical implementations.
- Hidden ProgramBench evaluator tests are external court, not inference
  evidence.
- Cleanroom task evidence must not be supplemented with original source,
  decompilation, internet lookup, external repos, hidden tests, host secrets, or
  unrelated git history.
- Forbidden inference stores must not be registered, mounted, queried, or
  exposed to the worker during the inference phase. They belong in audit /
  postmortem posture, not live retrieval context.
- ProgramBench result rows must not claim benchmark truth unless a later
  benchmark authority surface explicitly authorizes that posture.
- `ProgramODEUProfile` is not implementation authority.
- `PythonReconstructionPlan` is not execution authority.
- Passing local probes is not hidden-test equivalence.

## Language Parametricity

The architecture should stay language-parametric:

```text
PythonRealizationPack@1
GoRealizationPack@1
RustRealizationPack@1
CRealizationPack@1
```

The canonical ODEU profile remains shared; realization overlays differ by
target language.
