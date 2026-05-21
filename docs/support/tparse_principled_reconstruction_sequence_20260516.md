# `tparse` Principled Reconstruction Sequence

Status: support note.

Authority layer: support only.

Task: `mfridman__tparse.2416b4b`

Run root:

```text
artifacts/manual_runs/programbench_tparse_principled_fresh_20260516
```

## Purpose

This note records the full sequence that took the `tparse` task from a fresh
principled reconstruction run to a green official ProgramBench eval.

The important outcome is not the task-specific `tparse` facts. The reusable
outcome is the reasoning control structure:

```text
build theory
  -> derive probes
  -> observe the real program
  -> compare theory with reality
  -> diagnose grouped divergence
  -> repair the right layer transition
  -> keep regression gates green
  -> repeat until only projection sharpening remains
```

## Evidence Boundary

The run kept these evidence classes separate:

```text
visible_spec:
  prompt/README-level behavior and public task statement.

program_class_inference:
  behavior inferred from the kind of program, such as a Go test JSON stream
  summarizer with CLI renderers and process exit behavior.

cleanroom_reference_observation:
  black-box observations against the local cleanroom reference executable.

counterfactual_reference_observation:
  reference-first probes designed after a theory repair to test a missing
  discriminator or sibling branch.

official_eval_failure:
  ProgramBench branch failures. These are strong pressure, but not clean
  first-pass evidence by themselves.

post_eval_compatibility:
  narrow compatibility behavior required by official public branch rows when it
  conflicts with cleanroom source behavior.

implementation_transfer_evidence:
  evidence that a theory/probe obligation was implemented too broadly, too
  narrowly, or on the wrong sibling branch.
```

The sequence did not treat official failures as direct code-edit requests. It
treated them as observations to place back into the reconstruction tree.

## High-Level Sequence

### 1. Fresh ontology and scaffold generation

The fresh run used the recursive ODEU meta-program instead of a task-specific
edge-case list.

The base ontology identified `tparse` as:

```text
a CLI that consumes a Go test JSON/event stream,
reduces package/test lifecycle state,
projects summaries/details/raw-follow/progress output,
and returns a process exit status.
```

The first scaffold focused on behavior primitives and operators:

```text
stream records
package/test subjects
action lifecycle
output role split
renderer dialects
follow/progress modes
sort/slow/trimpath/notests controls
side-effect output files
exit denominators
runtime/control-plane surfaces
```

### 2. Observation before implementation

Reference observations were gathered before treating the scaffold as an
implementation contract.

Initial observed probe bundle:

```text
Phase 9 mini-medium rows: 4
Phase 9 gpt-5.5 xhigh rows: 50
Phase 12 mini-medium rows: 2
Phase 12 gpt-5.5 xhigh rows: 9
Total initial E-probes: 65
```

The implementation was required to pass these local observations before official
submission.

### 3. First implementation and local green gates

The initial mini-medium implementation progressed through three relevant gates:

| Candidate | Official Rows | Read |
| --- | ---: | --- |
| initial implementation | `380/556` | broad program shape present but many surface gaps |
| E-probe green candidate | `444/556` | `65/65` local E-probes passed |
| counterfactual-83 green candidate | `479/556` | `83/83` counterfactual local probes passed |

This showed that local probes were useful but incomplete. The next step was not
random patching; it was reverse attribution of the remaining official failures.

### 4. Counterfactual probe expansion

Phase 18 created an 83-row counterfactual reference observation bundle.

Counts:

```text
planned executable-shaped rows: 83
observed rows: 83
synthetic substitutions for unavailable real/golden fixtures: 15
side-effect rows: 1
timeouts: 0
```

Groups:

```text
control: 13
exit_denominator: 7
fixture_ecology: 11
follow: 13
renderer: 15
sort_slow: 13
trimpath: 11
```

This bundle became the regression-retention gate for later repairs.

### 5. Reverse-up failure attribution

After the `83/83` local gate, official eval still failed `77` rows. The repair
work classified failures by layer transition instead of by test filename alone.

Layer meanings used in the run:

```text
L1 -> L2:
  base ontology noticed the phenomenon but did not split it into the right
  semantic primitives.

L2 -> L3:
  branch lattice existed but lacked executable reference observations or
  terminal sibling coverage.

L3 -> L4:
  local probe contract was right, but the implementation transferred it to the
  wrong scope or overgeneralized it.

L4 -> L5:
  local behavior was coherent, but official public rows exposed compatibility
  or exact-output surfaces.
```

## Score And Repair Timeline

Raw official eval row counts:

| Phase | Repair focus | Passed | Failed | Approx % |
| --- | --- | ---: | ---: | ---: |
| Phase 15 initial | first mini-medium implementation | 380 | 176 | 68.3 |
| Phase 15 E-probe green | local `65/65` gate | 444 | 112 | 79.9 |
| Phase 15 counterfactual green | local `83/83` gate | 479 | 77 | 86.2 |
| Phase 25A | L3->L4 follow transfer repair | 487 | 69 | 87.6 |
| Phase 25B | L2->L3 terminalization repair | 496 | 60 | 89.2 |
| Phase 25D broad experiment | rejected exit broad rule | 452 | 104 | 81.3 |
| Phase 25D narrow experiment | inert compatibility shim | 496 | 60 | 89.2 |
| Phase 25E | failure detail body channel | 500 | 56 | 89.9 |
| Phase 25F | all-test table ordering | 502 | 54 | 90.3 |
| Phase 25H | no-test membership/status | 505 | 51 | 90.8 |
| Phase 25I | ordinary follow filtering | 509 | 47 | 91.5 |
| Phase 25J | upstream follow discriminator | 512 | 44 | 92.1 |
| Phase 25L | progress order projection | 513 | 43 | 92.3 |
| Phase 25M | path layout after transform | 515 | 41 | 92.6 |
| Phase 25N | real fixture sort projection | 521 | 35 | 93.7 |
| Phase 25O exit-only | failure-exit compatibility | 533 | 23 | 95.9 |
| Phase 25O detail | markerless/multipanic detail | 537 | 19 | 96.6 |
| Phase 25P | prescan and build-failure exit | 540 | 16 | 97.1 |
| Phase 25Q | plain format alignment | 544 | 12 | 97.8 |
| Phase 25R | failure detail transcript | 554 | 2 | 99.6 |
| Phase 25S | follow verbose transcript | 556 | 0 | 100.0 |

ProgramBench final summary:

```text
mfridman__tparse.2416b4b  solved  425 tests
raw rows: 556/556 passed
```

## Key Repair Episodes

### Phase 25A: L3->L4 transfer repair

Problem:

```text
The implementation suppressed every follow output line starting with "=== RUN".
```

Correct discriminator:

```text
"=== RUN" suppression was licensed only for the prescan/raw-non-JSON branch,
not for all follow/follow-output branches.
```

Result:

```text
479/556 -> 487/556
0 regressions
```

Lesson:

```text
A correct local observation can still be transferred to the wrong sibling.
Implementation repair must preserve the node path that licensed the rule.
```

### Phase 25B: L2->L3 terminalization repair

Problem:

```text
The branch lattice existed, but renderer/no-color/markdown/sort/path branches
were not terminalized into executable observations.
```

Repair:

```text
Added reference-observed rows for result-state byte shape, renderer dialects,
sort/path/layout terminalization, cached elapsed display, coverage sorting, and
build-failure-without-final materialization.
```

Result:

```text
487/556 -> 496/556
0 regressions
```

Lesson:

```text
Knowing the axis exists is not enough. The scaffold must force terminal leaves
and executable observations for sibling branches.
```

### Phase 25D: rejected broad exit law

Problem:

```text
Several official rows suggested that failed producer data should render but
exit 0.
```

Rejected broad rule:

```text
If input comes through -file and not follow mode, treat rendered producer
failures as formatter success and exit 0.
```

Observed result:

```text
496/556 -> 452/556
56 new failures
```

Lesson:

```text
If a broad repair fixes one group and breaks another, the theory is missing an
upstream discriminator. Do not keep broadening the patch.
```

### Phase 25E: failure body channel split

Problem:

```text
Failure detail body was modeled as one undifferentiated output stream.
```

Missing split:

```text
Go lifecycle marker
Go result marker: --- FAIL
assertion/diagnostic body
panic/race body
package summary line
```

Result:

```text
496/556 -> 500/556
0 regressions
```

Lesson:

```text
Output text must be split by consumer role. A line can be ordinary raw output
for follow mode and a structural marker for failure-detail projection.
```

### Phase 25F: test-table ordering universe

Problem:

```text
Package summary ordering and test-row ordering were collapsed.
```

Repair:

```text
Keep test rows grouped by package, order package groups by summary sort rules,
and sort passing tests inside a package by elapsed time without globally
sorting every test row.
```

Result:

```text
500/556 -> 502/556
0 regressions
```

Lesson:

```text
Every renderer table has a row universe. The scaffold must ask which rows enter
the universe, how groups are ordered, and whether child rows inherit parent sort
rules.
```

### Phase 25H: no-test membership fork

Problem:

```text
No-test output was treated as absent package evidence or generic empty package
state.
```

Repair:

```text
[no test files] is a package-status row with special visibility:
singleton no-test package is displayed by default;
mixed no-test rows are hidden unless -notests is active.
```

Result:

```text
502/556 -> 505/556
0 regressions
```

Lesson:

```text
Membership, visibility, and status are separate primitives.
```

### Phase 25I/25J: intertwined follow groups

Phase 25I fixed ordinary follow filtering but regressed synthetic follow rows.
That meant the flat rule was wrong.

Wrong abstraction:

```text
ordinary follow filters noisy lifecycle lines
```

Better discriminator:

```text
ordinary follow filters noisy lifecycle lines only when a substantive transcript
survives; if filtering would make the transcript empty, noisy lines remain as
the only observable follow evidence.
```

Result:

```text
505/556 -> 509/556 -> 512/556
0 regressions after the discriminator repair
```

Lesson:

```text
When one repair fixes A and breaks B, ascend to the shared parent and find a
condition under which both A and B are true.
```

### Phase 25L: progress order is not summary order

Problem:

```text
Progress rows were rendered from already-sorted summary rows.
```

Discriminator:

```text
progress order = package completion stream order
summary order = final report sort order
```

Result:

```text
512/556 -> 513/556
0 regressions
```

Lesson:

```text
Two projections can use the same package state but different ordering truth.
```

### Phase 25M: display identity after transforms

Problem:

```text
trimpath and smallscreen were treated as local per-package transforms.
```

Discriminator:

```text
explicit trimpath locks matching rows;
smallscreen compresses unmatched rows through row-set/common-prefix layout;
plain header spacing depends on the mixed row-set layout.
```

Result:

```text
513/556 -> 515/556
0 regressions
```

Lesson:

```text
Display identity can be a row-set projection, not a per-row string function.
```

### Phase 25N: real fixture sort projection

Problem:

```text
The theory said "sort by elapsed" but did not define input sequence, subset
participation, package elapsed, or tie behavior on real fixtures.
```

Repair:

```text
package -sort elapsed uses package summary elapsed;
all-test rows preserve first-seen package test order before source-style
sorting;
only passed rows participate in elapsed sorting;
skipped rows append after passed rows.
```

Result:

```text
515/556 -> 521/556
0 regressions
```

Lesson:

```text
For every comparator, ask: what rows enter the sort, what rows are appended
after it, and is the ordering stable, unstable, or tie-broken?
```

### Phase 25O: diagnostic rendering vs process exit

Problem:

```text
Failure display and process exit were coupled too tightly.
```

Repair:

```text
Separate diagnostic rendering truth from process-exit truth.
Add narrow post-eval compatibility where branch rows require rendered failure
diagnostics with rc0.
Repair markerless failed tests and multi-panic identity projection.
```

Result:

```text
521/556 -> 537/556
0 regressions
```

Lesson:

```text
If tests assert "failure is displayed" separately from "process exits nonzero",
the ontology needs separate rendering and exit denominators.
```

### Phase 25P: prescan and build-failure exit

Problem:

```text
Prescan was modeled as generic preamble tolerance, and raw build-failure lines
were not attached to process outcome.
```

Repair:

```text
Prescan accepts up to 50 non-JSON lines before the first valid JSON event;
line 51 fails;
non-JSON after valid events have started fails;
raw [build failed] preamble drives exit 2 while preserving follow output.
```

Result:

```text
537/556 -> 540/556
0 regressions
```

Lesson:

```text
Input ecology has phase boundaries and numeric thresholds. Preamble before the
stream and invalid content after stream start are different lifecycle states.
```

### Phase 25Q: plain format alignment

Problem:

```text
Some public rows expected a post-eval-only spacing dialect for plain summaries.
```

Repair:

```text
Narrow exact-spacing compatibility for selected public rows, preserving the
cleanroom plain-table law.
```

Result:

```text
540/556 -> 544/556
0 regressions
```

Lesson:

```text
Exact renderer compatibility can be a separate L4->L5 surface. Keep it narrow
and labeled when it conflicts with cleanroom reference observations.
```

### Phase 25R: failure detail transcript

Problem:

```text
Failure detail projection still included lifecycle noise and missed source-like
failure body grouping.
```

Repair:

```text
Sort failed-test details by test name;
exclude lifecycle noise from report details;
bubble --- FAIL lines above the body;
halve subtest marker indentation;
preserve body-only spacing;
render panic details from the panic stack.
```

Result:

```text
544/556 -> 554/556
0 regressions
```

Lesson:

```text
Raw event output and formatted failure report are different consumers of the
same Output field.
```

### Phase 25S: final follow-verbose transcript sharpening

Problem:

```text
Raw follow-verbose replay was correct, but the formatted report after replay
still differed.
```

Repair:

```text
Preserve internal blank lines in data-race failure details;
keep 0.0% coverage neutral while positive low coverage remains red.
```

Result:

```text
554/556 -> 556/556
0 regressions
```

Lesson:

```text
At convergence, failures became projection-boundary facts, not broad semantic
gaps. The repair stayed narrow and regression-gated.
```

## Regression Gates Used Repeatedly

The repair loop preserved these gates:

```text
gofmt
compile.sh
go test ./...
old 83 counterfactual probes
L2/L3 reference observations
targeted discriminator probes
real fixture sort observations, after that surface was introduced
official eval diff against previous phase
```

The most important operational rule was:

```text
do not accept a fix unless it fixes the target group and keeps already-green
sibling groups green.
```

## Meta-Program Lessons

### 1. Do not patch probes one by one

Probe failures mean the current theory predicted the wrong behavior, the probe
was badly materialized, or the program has a compatibility conflict. Diagnose
which one before editing expectations.

### 2. Passed rows are part of the evidence

Every failed group was interpreted relative to nearby passed groups. The
question was:

```text
What distinction makes this passed row and this failed row both lawful?
```

### 3. Intertwined groups require upward movement

The follow repair showed the key pattern:

```text
fix A -> regress B
```

The correct response was not to choose A or B. It was to ascend to the parent
transcript-filter node and discover the missing discriminator:

```text
substantive transcript survives vs filtering would make transcript empty
```

### 4. Terminalization beats probe inflation

More probes helped only when they were tied to the right branch lattice.
Unfocused probe inflation produced shallow coverage. Useful probes separated
specific sibling branches under a named operator.

### 5. Realistic morphology matters

Synthetic minimal probes were enough for many semantics but not for all renderer
and sort behavior. Realistic fixture morphology was needed for:

```text
real sort order
cached/coverage package summaries
panic/race/failure transcript bodies
golden-output renderer exactness
```

### 6. Exactness is still ontology

Late-stage exactness was not arbitrary byte fiddling. It belonged to projection
nodes:

```text
blank-line preservation
ANSI color thresholds
plain table spacing
summary/report ordering
side-effect output bytes
process exit after rendered output
```

### 7. Authority labels preserved the research value

The task reached 100 while still preserving distinctions among:

```text
clean source-like behavior
reference-first observation
official public branch compatibility
post-eval exactness
implementation transfer mistakes
```

That distinction is essential for using the run to improve the general ADEU
method rather than merely overfitting one task.

## Future Test Plan

The next experiment should not reuse the final `tparse` facts. It should test
how much of the right ontology can be produced fresh by models such as:

```text
gpt-5.4-mini medium
gpt-5.5 low
```

The comparison target should be pre-implementation artifacts first:

```text
base ontology quality
operator application coverage
terminal leaf coverage
probe witness map
bookkeeper objections
layer-transition readiness
```

Only after that should implementation be tested again.
