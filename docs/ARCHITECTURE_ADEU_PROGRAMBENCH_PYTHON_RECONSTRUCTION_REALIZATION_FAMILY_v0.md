# Architecture ADEU ProgramBench Python Reconstruction Realization Family v0

Status: architecture / decomposition note for planned `PB-PY-0`.

Authority layer: architecture / decomposition.

This architecture note does not authorize ProgramBench participation,
benchmark submission, benchmark truth, hidden-test inference, original source
lookup, decompilation, internet use inside benchmark tasks, implementation,
code generation, command execution, runtime transition, product authority,
graph-memory authority, recursive policy amendment, PR creation, commit, merge,
release, or future-family selection by itself. It defines a narrow local
ProgramBench-shaped review family so later starter locks can select bounded
slices without turning cleanroom reconstruction planning into benchmark
execution.

## Family Thesis

`PB-PY-0` should test whether the closed `V85` semantic declaration and
canonical lookup substrate can help a real reconstruction-shaped software
problem without jumping to official ProgramBench solving.

The family circuit is:

```text
cleanroom evidence
  -> behavior ontology
  -> concept boundaries
  -> language realization options
  -> implementation obligations
  -> witness probes
  -> equivalence audit
```

The first target is Python because it is a strong reconstruction substrate for
current models, not because Python is the canonical concept layer. The
architectural split is:

```text
Canonical ODEU Concept DB:
  defines what the concept is

Language Realization Overlay:
  defines how the concept can be lawfully instantiated in code
```

Controlling invariant:

```text
PB-PY-0 may make a small ProgramBench-style Python realization pack and one
local cleanroom fixture reviewable, but it may not run official ProgramBench
tasks, expose forbidden evidence, claim benchmark truth, submit results, rank
models, or authorize implementation outside later bounded fixture review.
```

Operational cleanroom invariant:

```text
Forbidden inference stores must not be registered, mounted, queried, or exposed
to the worker during inference. Forbidden evidence may appear in audit /
postmortem posture only, not in live reconstruction context.
```

## Source Stack Consumed

`PB-PY-0` consumes:

- `V85` family closeout as semantic declaration / lookup review substrate;
- the V85 resident-model probe corpus as empirical support for closed branch
  selection, uncertainty routing, remand, and no unauthorized transition;
- the hardened conceptual-first retrieval support note as architecture /
  doctrine, not implementation authority;
- public ProgramBench descriptors as advisory benchmark context only.

No consumed source becomes benchmark truth, task truth, hidden-test evidence,
implementation authority, or official ProgramBench authority by being consumed.

## Family Slices

### `PB-PY-0-A`: Cleanroom Profile Intake And Fixture Contract

Starter surfaces:

- `programbench_cleanroom_reconstruction_profile@1`
- `program_odeu_concept_boundary_seed@1`
- `programbench_cleanroom_evidence_source_index@1`
- `programbench_reconstruction_non_authority_guardrail@1`
- `programbench_local_cleanroom_fixture_contract@1`

Purpose:

- record a cleanroom reconstruction profile without creating a solver;
- make evidence source visibility, currentness, and forbidden-store posture
  row-shaped;
- seed a tiny program ODEU concept boundary inventory before Python realization
  rows exist;
- define what will count as a lawful local cleanroom fixture later, without
  building that fixture;
- preserve phase separation between inference, local development, evaluation,
  and postmortem;
- prevent public descriptors, hidden tests, original sources, internet lookup,
  and local probe passes from becoming benchmark truth.

Forbidden:

- `ConceptRealizationRecord@1`;
- `PythonReconstructionPlan@1`;
- Python code generation;
- local cleanroom fixture implementation;
- official ProgramBench runner integration;
- official task execution, hidden-test handling, benchmark scoring, or model
  ranking.

### `PB-PY-0-B`: Python Realization Overlay

Later surfaces:

- `concept_realization_record@1`
- `python_reconstruction_realization_pack@1`
- `python_reconstruction_plan@1`
- `python_realization_witness_template@1`

Purpose:

- map canonical program concepts to lawful Python standard-library realization
  options;
- record preferred stdlib surfaces, implementation patterns,
  contraindications, boundary conditions, failure modes, required witnesses,
  and advisory examples;
- keep code idioms as realization options, not concept definitions;
- preserve that `PythonReconstructionPlan@1` is not execution authority.

Forbidden:

- fixture implementation or official benchmark participation unless selected
  by a later lock;
- hidden-test inference;
- claiming local probes prove hidden-test equivalence.

### `PB-PY-0-C`: Local Fixture And A/B/C Comparison Packet

Later surfaces:

- `programbench_local_cleanroom_fixture@1`
- `programbench_reconstruction_comparison_packet@1`
- `programbench_probe_equivalence_audit@1`
- `programbench_realization_family_closeout_alignment@1`

Purpose:

- instantiate one local ProgramBench-style fixture under the contract defined
  by `PB-PY-0-A`;
- compare:
  - base ADEU harness;
  - ADEU plus conceptual profile;
  - ADEU plus conceptual profile plus Python realization overlay;
- audit whether the concept-to-code realization overlay changes reconstruction
  quality under local, non-official evidence.

Forbidden:

- official ProgramBench run or result claim;
- model leaderboard ranking;
- hidden-test repair loop;
- using postmortem failures as retroactive inference evidence.

## Required Boundary Distinctions

`PB-PY-0` must keep these distinctions machine-checkable:

- cleanroom profile is not implementation authority;
- concept boundary seed is not proof a concept exists in a task;
- public descriptor observation is advisory context, not benchmark truth;
- hidden tests are external court, not inference evidence;
- forbidden evidence classification is insufficient if the worker can access
  the store;
- local fixture contract is not fixture implementation;
- Python stdlib surface is a realization option, not a canonical concept;
- local probe pass is not hidden-test equivalence;
- comparison packet is local research evidence, not model ranking;
- postmortem evidence is not retroactive inference evidence.

## Initial Concept Boundary Seeds

The first O-lane seed set is:

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

Seed rows may remain `boundary_incomplete`. The point is to make the program
ontology visible before Python realization begins.

## Phase Separation

```text
inference_phase:
  cleanroom-visible evidence only

local_development_phase:
  worker-generated probes/tests allowed
  still no forbidden evidence

evaluation_phase:
  hidden tests may judge artifact
  hidden tests remain external court, not inference evidence

postmortem_phase:
  evaluation failures may inform harness research only under dev posture
  not retroactively admitted as inference evidence
```

## Negative Laws

- "The public ProgramBench page says 200 tasks" is not "this task truth is
  fixed."
- "A hidden evaluator rejected the submission" is not "the worker may infer
  hidden tests."
- "Python can implement this with argparse" is not "`argparse` is the concept."
- "A local probe passed" is not "the replacement program is behaviorally
  equivalent."
- "A fixture contract exists" is not "a fixture has been built."
- "The overlay has realization records" is not "code may be generated."
- "The comparison packet improved C over B" is not "models may be ranked on
  ProgramBench."
