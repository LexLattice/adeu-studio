# GPTPro Review: Layered ADEU Derivation for `mfridman__tparse.2416b4b`

## Scope and authority

This is a packet-grounded theory/probe-method review, not a code patch. I used the attached packet’s README, meta-program documents, task-specific theory artifacts, reference/remand/V3/V4 probe outputs, official ProgramBench evaluation summary/JSON, and the loop-21 candidate source. I did not use external upstream source or web material.

Evidence labels used below:

- `meta_program`: generic generator/bookkeeper procedure.
- `pre_observation_theory`: generator/scaffold obligations before reference observation or before official eval.
- `reference_observation`: behavior captured by the reference executable through the packet’s probe systems.
- `post_eval_failure`: official evaluator outcomes and failure-pressure rows.
- `implementation_repair`: candidate-source and local repair-loop evidence.

## Executive conclusion

The ADEU scaffold cut through the `tparse` problem in the right high-level way: it stopped treating `tparse` as “parse JSON and print a table,” and decomposed it into a stream-to-state-to-render compiler with independent source, lifecycle, subject, renderer, side-effect, and exit/status truths. That decomposition is why the local gates became strong: preservation was `295/295`, V3 was `99/99`, V4 was `135/142`, and official score improved from loop-20 score `84` to loop-21 score `91`, with `499/556` raw rows passed.

The remaining gap is not a single missing flag or simple code bug. It is mostly compatibility depth: exact renderer bytes, fixture-scale Go-test morphology, follow/raw-output dialects, failure-detail block geometry, panic/build/race prescan breadth, path/sort/smallscreen cross-products, and branch-sensitive exit denominators. Several failures also show a local-oracle problem: the code can be green against local E-probes while still wrong against official fixture morphology. Those rows must stay labeled `post_eval_failure` until new reference-first probes lock exact behavior.

## 1. Base ontology of the program class

### 1.1 Input event stream

`tparse` consumes a line-oriented structured event stream, normally from `stdin` or `-file`. The visible class is Go `test2json`/`go test -json`, so the program’s base input ontology includes records, producer schema, field presence, field typing, record order, EOF, blank lines, malformed lines, and filesystem source selection.

Core event fields are `Time`, `Action`, `Package`, `Test`, `Output`, `Elapsed`, and `FailedBuild`. In the ADEU model, this is not a flat record. Each field has a separate behavior role:

- `Action`: lifecycle/control truth.
- `Package`: raw subject identity and aggregate grouping truth.
- `Test`: test/subtest subject identity truth.
- `Output`: raw follow bytes and multiple semantic classifiers.
- `Elapsed`: display, sort, slow, and package summary truth.
- `Time`: timestamped follow truth and parser/runtime-error truth.
- `FailedBuild`: build-failure/error-surface truth.

The important ontology split is between raw event identity and rendered/display identity. `-trimpath` can change displayed package names without changing grouping or raw identity. This prevents a false merge when two raw packages trim to the same visible name.

### 1.2 Parser/event lifecycle

The lifecycle is:

```text
open/select input
  -> scan lines
  -> decode JSON object
  -> field-shape validation
  -> event ingestion by Action/subject
  -> output-role classification
  -> package/test state accumulation
  -> optional follow/progress side effects
  -> finalization / incomplete lifecycle closeout
  -> renderer selection
  -> process exit closeout
```

The central ADEU insight is that validation, filtering, rendering, side effects, and exit are different stages. A row hidden from the rendered test table may still affect package summary or exit. Raw follow output may happen before a later parser failure. A write-open error for `-follow-output` can short-circuit decoding and rendering.

### 1.3 Package/test state model

The package/test state model is two-layered:

- package state: raw package name, display name, order, final status, elapsed, coverage, pass/fail/skip counts, package output, no-test/build/race/panic/cached flags;
- test row state: raw package, raw test name, display package/test, action, elapsed, output lines, benchmark marker.

A package-level event is not just a test event with missing test. Missing `Test` selects package-level subject truth. This matters for package finals, package output, build failures, no-test packages, race markers, and panic stack output.

### 1.4 Rendering surfaces

Rendering has multiple concrete surfaces:

- default/basic Unicode box tables with ANSI color unless disabled;
- plain aligned tables;
- markdown package sections, details blocks, code fences, emoji/status labels, and markdown tables;
- failure and panic banners;
- failure-detail blocks;
- no-test/build/race/panic/coverage-specific display paths;
- smallscreen splitting/wrapping for long paths and subtest chains;
- final newlines, blank-line geometry, padding, column widths, ANSI sequences, and alignment.

Renderer truth is byte-level truth. A one-space width difference, missing blank line, or wrong code-fence placement is a real behavioral mismatch in this program class.

### 1.5 Flag/control surfaces

The control ontology includes:

- control-plane: `-h`, `--help`, `-v`, `--version`, no-args/non-pipe diagnostics, unknown flags, bad flag values, stdout/stderr routing, final newlines;
- input source: `stdin`, `-file`, empty `-file`, missing files, directories;
- selection: `-all`, `-pass`, `-skip`, `-notests`;
- display/mode: `-format`, `-nocolor`, `NO_COLOR`, `-smallscreen`, `-noborders`, `-trimpath`;
- ordering/limits: `-sort`, `-slow`;
- raw/side-effect modes: `-follow`, `-follow-output`, `-follow-verbose`, `-include-timestamp`;
- workflow/secondary modes: `-progress`, `-compare`.

The important meta-lesson is that help output is not decoration. It is a source-expansion surface that must be observed and parsed into a complete flag inventory.

### 1.6 Exit/status semantics

Exit is not derivable from one rendered status column. It is a denominator registry. Denominators include:

- all-pass stream;
- failed test;
- package-level final fail;
- build failure;
- panic prescan;
- exact race marker;
- no-test stream;
- parser error before valid event;
- parser error after partial follow side effect;
- input-source/file error;
- follow-output write-open error;
- invalid flag or invalid option value;
- compare read/parse warnings;
- no-pipe/non-pipe stdin diagnostic.

The packet also records branch-sensitive or conflicting pressure: some official rows expect failed/build/panic display with exit `0`, while other fixture/golden rows require exit `1`. That conflict cannot be flattened into one global rule without new reference-first observations that distinguish morphology and invocation route.

### 1.7 Side-effect/follow surfaces

Side effects include raw stdout follow, follow-output file writes, timestamp prefixes, progress lines, and compare warnings. These surfaces are order-sensitive. Raw output may precede summary output. A side-effect file may contain bytes even when a later parser error exits nonzero. A follow-output open error may produce stderr and exit `0` without decoding the stream.

## 2. How ADEU decomposed the ontology

### 2.1 Generic decomposition method

`meta_program`: the generator v2 requires productive descent from visible spec into primitive inventory, indication-generated artifacts, counterfactual splits, axes/interactions, probe allocation, observation reconciliation, and D-ledger scaffold rows. It uses an authority ladder: discovered candidate → obligationized for tracking → probe-required pending observation → locked by visible spec or observation → explicit deferral.

`meta_program`: the adversarial bookkeeper v2 independently scans for forgotten producer fields, runtime surfaces, help/version surfaces, renderer-golden morphology, mode interactions, type/error surfaces, and lifecycle/denominator splits. It does not silently fix the scaffold; it emits blocking objections and repair templates.

### 2.2 Task-specific pass-1 shape

`pre_observation_theory`: pass 1 extracted primitives for event stream, input source, Go producer schema, action/package/test/output/elapsed/time/build fields, field absence, ordering, result filters, slow/sort, table format/color/smallscreen, follow/progress/compare/trimpath, help/version/parser/runtime, process exit, filesystem, and coverage.

It then created field-effect rows, producer-schema rows, de-lumped high-risk fields, type/error rows, subject-selection rows, field-presence lattice rows, lifecycle-stage rows, aggregate-denominator rows, renderer-compatibility rows, runtime-surface rows, axes, interactions, probes, and D-ledger obligations.

### 2.3 Bookkeeper-forced pass-2 repairs

`pre_observation_theory`: pass 2 added or split high-risk surfaces that pass 1 under-modeled:

- `Action:"start"` lifecycle;
- `Action:"bench"` benchmark behavior;
- `-trimpath` as a required-value/string lattice, not a boolean flag;
- hidden/possible `-follow-verbose`;
- `Output` child roles: raw follow, failure detail, panic, no-test, build, race, coverage;
- realistic Go-test stream morphology;
- decomposed exit/status denominators.

This is the point where the scaffold moved from “field list” to “base ontology.” It separated raw identity from display identity, output text from output roles, filter selection from aggregation, and rendered status from process exit.

### 2.4 Observation and remand

`reference_observation`: the first reference observation covered all planned `PR-001..PR-079` rows and produced 263 observation rows. It found important surprises: default all-pass still renders a package table; `start` and `bench` are accepted; `-trimpath` is value-shaped; `-follow-verbose` is recognized; exact race marker can force exit `1` while rendering PASS; invalid `-sort`/`-format` are soft exit-0 errors; `-file ""` falls back to stdin; follow-output write errors can exit `0`.

`reference_observation`: the remand phase resolved seven focused blockers: trimpath auto/display, trimpath collision/compare, bench denominator, incomplete lifecycle closeout, race marker split, compare no-diff behavior, and follow-output write-error precedence.

### 2.5 V3/V4 repair depth

`post_eval_failure` + `reference_observation`: after earlier official failures, V3 repaired help/version/control-plane, flag parser inventory, golden fixture morphology, follow side effects, trimpath/path/smallscreen, sort/slow/coverage, and failure/panic/build/race exit. V3 was `99/99` locally.

`post_eval_failure` + `reference_observation`: V4 added deeper failure-detail identity blocks, follow raw-line matrix, exit-code denominator registry, panic/prescan morphology, fixture-scale golden morphology, sort/slow/path/smallscreen cross-products, and input-source preflight. V4 was `135/142` locally, with the remaining seven all `stdout_sha256` mismatches.

## 3. Conceptual axes covered by task-specific theory

The task-specific theory covered the following axes well enough to drive high local and official scores:

| Axis family | Coverage posture |
|---|---|
| Input source and parser | `stdin`, `-file`, empty file arg, missing/dir file, empty/blank/malformed/truncated streams, early vs late parser failure. |
| Producer schema and field lattice | `Action`, `Package`, `Test`, `Output`, `Elapsed`, `Time`, `FailedBuild`, unknown fields, missing/null/empty/wrong-shape cases. |
| Event lifecycle | run/output/pass/fail/skip/pause/cont/start/bench, duplicates, incomplete lifecycle, package vs test finals. |
| Subject selection | package vs test vs subtest, package-level output, display identity vs raw identity, trimpath collisions. |
| Output-derived roles | raw follow, failure details, panic, no-test, build, race, coverage. |
| Aggregation and filtering | package summary, pass/fail/skip counts, default/all/pass/skip/notests visibility, hidden rows affecting summary/exit. |
| Sort/slow/coverage | elapsed, cover, name ordering, slow limits, per-package/global ambiguity, coverage parsing and missing coverage. |
| Renderer grammar | basic/plain/markdown, ANSI/no-color/env, smallscreen, invalid renderer options, banners, details, markdown code fences. |
| Control plane | help/version aliases, usage, invalid flags, bad option values, no-args/non-pipe input. |
| Side effects | follow stdout, follow-output file, timestamped output, write-open errors, partial side effects before parse failure. |
| Progress/compare | package progress lines, compare warnings/current-run rendering, no visible diff in remand observations. |
| Exit/status denominators | all-pass, fail, build, panic, race, parse, file, write, compare, no-test, invalid option/flag. |
| Realistic morphology | pass/fail/skip/nested/panic/no-test/build/coverage/multi-package streams, with V3/V4 adding more fixture realism. |

The main residual weakness is not absence of these axis names. It is insufficient depth inside several axes and insufficient cross-products between them.

## 4. Which probes instantiate which obligations

### 4.1 Initial and pass-2 probes

`pre_observation_theory`: `PR-001..PR-038` instantiate the first scaffold:

- `PR-001..004`: baseline, stdin/file, empty/malformed streams;
- `PR-005..010`: action taxonomy, package/test subjects, output association, subtests, duplicates, multi-package grouping;
- `PR-011..015`: filters, no-test, elapsed, slow, sort, cover;
- `PR-016..018`: format/color/smallscreen renderer snapshots;
- `PR-019..022`: follow, follow-output, timestamp, progress;
- `PR-023..025`: compare/trimpath/build failure;
- `PR-026..033`: field-specific type and presence lattice;
- `PR-034..036`: help/version/parser/filesystem/newline surfaces;
- `PR-037..038`: coverage and no-test output recognition.

`pre_observation_theory`: `PR-039..PR-079` instantiate the bookkeeper repairs:

- `PR-039..040`: `start` and `bench`;
- `PR-041..044`: trimpath value lattice and collision/compare;
- `PR-045`: `follow-verbose` recognition;
- `PR-046..052`: split `Output` roles;
- `PR-053..059`: renderer byte snapshots;
- `PR-060..068`: realistic stream morphologies;
- `PR-069..079`: decomposed exit/status denominators.

### 4.2 Remand probes

`reference_observation`: `R-001..R-007` close the seven focused blockers:

- `R-001`: trimpath auto/explicit/no-slash/banner-vs-table;
- `R-002`: trimpath display collisions and compare no-diff;
- `R-003`: bench row/count/exit behavior;
- `R-004`: package/test start incomplete lifecycle;
- `R-005`: exact race marker exit split;
- `R-006`: compare current-run rendering plus previous-file warnings;
- `R-007`: follow-output open error and valid-file/later-malformed precedence.

### 4.3 V3 probes

`reference_observation`: V3 had 99 reference-observed probes and replayed `99/99`:

- `FI_flag_parser_inventory`: 38;
- `HU_control_plane`: 12;
- `VE_version_identity`: 6;
- `GF_golden_fixture_morphology`: 8;
- `FO_follow_side_effects`: 8;
- `PF_failure_panic_build_race_exit`: 11;
- `SS_sort_slow_coverage`: 6;
- `TP_trimpath_path_smallscreen`: 10.

### 4.4 V4 probes

`reference_observation` and `implementation_repair`: V4 had 142 reference rows and loop-21 replayed `135/142`:

- `EX4_exit_denominator_registry`: 17 passed / 0 failed;
- `FD4_failure_detail_identity_blocks`: 35 passed / 1 failed;
- `FW4_follow_raw_line_matrix`: 11 passed / 0 failed;
- `GF4_fixture_scale_golden_morphology`: 33 passed / 2 failed;
- `HU4_input_source_preflight`: 12 passed / 0 failed;
- `PX4_panic_prescan_morphology`: 15 passed / 2 failed;
- `SP4_sort_slow_path_smallscreen`: 12 passed / 2 failed.

The seven residual V4 failures are all stdout byte mismatches, not exit/stderr mismatches: one failure-detail plain fixture, two panic/prescan plain fixtures, two sort/path/smallscreen fixtures, and two fixture-scale golden morphology fixtures.

## 5. Official pass/fail groups showing alignment

`post_eval_failure`: loop-21 official summary is strong evidence that many ontology layers are now aligned:

- official score `91`;
- raw rows `499 passed / 57 failed / 556 total`;
- previous loop-20 score `84`;
- net improvement `+31` raw passed rows;
- fully passed large groups include help/usage (`30/30`), argparse validation (`18/18`), display (`32/32`), edge cases (`15/15`), basic invocation (`11/11` in one suite plus `7/7` in eval), externalized fixtures (`10/10`), output display (`9/9`), parsing (`9/9`), flag-combination suites, formatting, summary tables, input handling, failed tests, follow mode in eval suite, sorting, CLI, trimpath, comparison, env config, progress mode, and several stdin/file suites.

The important interpretation is that the generic control-plane and parser surfaces that were earlier missed are now largely repaired. Help/version is no longer the dominant failure class. Basic input handling, invalid option handling, parser errors, many display/flag/filter surfaces, and many externalized fixture rows are officially green.

## 6. Remaining failures and what they indicate

`post_eval_failure`: remaining official failures cluster as follows:

- `tests.test_follow`: 9;
- `tests.test_format`: 8;
- `tests.test_harvest`: 7 plus one separately grouped prescan row;
- `tests.test_failure_details`: 5;
- `tests.test_path`: 5;
- `tests.test_sort`: 4;
- `eval.tests.test_tparse_golden_outputs`: 3;
- `tests.test_follow_mode`: 3;
- `tests.test_panic_handling`: 3;
- `tests.test_real_testdata`: 3;
- plus one-off display, edge, package summary, progress, additional coverage, and markdown flag/golden rows.

### 6.1 Missing ontology axis

At the current loop-21 layer, there are few wholly missing axis names. Earlier missing axes included long help/version aliases, no-args preflight, fixture-scale golden morphology, and mode interactions; V3/V4 added them.

The closest remaining missing/subordinate axes are more fine-grained:

- follow line classes are not yet decomposed deeply enough for fixture-scale follow behavior;
- failure-detail blocks need a more explicit header/body/separator/code-fence geometry axis;
- exit denominators need branch/morphology labels for render-only-failure vs failed-test/build/panic/race expectations;
- panic/build/race prescan needs richer source-location/multiple-block/package-level/test-level variants.

### 6.2 Under-specified interaction between axes

This is the largest residual theoretical category.

- `follow x line-class x follow-output x timestamp x progress x multi-package`: official follow failures show that one global prefix blacklist or one follow policy does not close the surface.
- `trimpath x smallscreen x renderer x long subtest chain`: path failures and V4 `SP4` mismatches show display identity, wrapping, and renderer grammar are still coupled.
- `sort x slow x coverage x cached/no-elapsed package x package grouping`: sort failures show global/per-package denominators and absent/malformed data need fixture-scale cross-products.
- `format x failure-detail x markdown code fence x color/no-color x real fixture`: markdown and golden failures show formatting cannot be separated from failure-detail morphology.
- `panic/build/race x renderer x follow x exit`: panic and real testdata failures show prescan classification interacts with renderer and exit rather than being one output classifier.

### 6.3 Exact renderer compatibility gap

This category is explicit in V4: the seven non-green V4 probes are all `stdout_sha256` mismatches. The observed residuals include:

- plain table column width differences by a space;
- missing or extra blank lines in basic/plain/markdown sections;
- markdown code fence placement (`"```\n--- FAIL:"` structural check failed in one official row);
- banner width/padding differences for panic blocks;
- failure-detail separator and identity-header geometry;
- smallscreen markdown spacing/alignment;
- golden follow/failed/panic stdout exact mismatches.

For `tparse`, these are not cosmetic. The evaluator has golden-output tests, so renderer bytes are a primary behavior surface.

### 6.4 Implementation drift despite correct theory

`implementation_repair`: several source-level patterns match known residual failures:

- `emitFollow` suppresses `=== RUN`, `=== PAUSE`, `=== CONT`, `--- PASS`, and `--- SKIP` unless `-follow-verbose`; official follow failures include rows expecting raw `RUN`/`PASS` lines in `-follow`/golden follow contexts. This is at least implementation drift against some official pressure, or evidence that the local follow probes overfit the wrong line-class branch.
- `exitCodeForState` returns `1` directly for package status `FAIL`, build, panic, or `HasBuild`. Many branch `3487890d9158` official rows expect failed/build/panic displays with exit `0`. This shows denominator conflict/branch sensitivity, and the implementation has one global exit policy.
- Plain/markdown/basic renderers are hand-built and locally green for many probes, but V4 and official goldens still fail on exact spacing, blank lines, code-fence geometry, and banner width. That is implementation drift at byte-compatibility level even where the theory has the right renderer axis.
- Failure detail rendering sometimes preserves body text but not the exact identity-header ordering expected by official/golden fixtures.

These should not be promoted to clean first-pass truth. They are `implementation_repair` findings supported by local source inspection plus `post_eval_failure` pressure.

### 6.5 Probe insufficiency or probe overfitting

This is the other major category. The local gates are useful but not sufficient:

- Preservation `295/295` and V3 `99/99` did not imply official completeness; earlier official score was `76` and then `84`.
- V4 `FW4_follow_raw_line_matrix` is `11/11`, yet official follow/golden-follow rows still fail. That means the line matrix is under-sampled or did not include the right fixture morphology.
- V4 `EX4_exit_denominator_registry` is `17/17`, yet official rows still show exit denominator conflicts. The registry has the right shape, but its rows are not branch/morphology-complete.
- V4 `GF4_fixture_scale_golden_morphology` still has 2 local failures and official golden outputs still fail. The fixture mesh is now conceptually right but still too narrow or not exactly matched.
- V4 `SP4` and `PX4` failures show that local probes found the right areas but remain sensitive to exact plain/markdown widths and panic output morphology.

The local oracle is internally coherent, but it is still not a representative oracle for all official fixture families.

## 7. Generic meta-program refinements

The meta-program should be refined to derive these axes earlier without task-specific hindsight.

### 7.1 Promote help/version to a mandatory source-expansion phase

`meta_program` already added this in v2, but the generic rule should be stricter: for any CLI that mentions help, usage, version, or full usage, implementation handoff is blocked until help/version/no-args/invalid-flag/precedence/stdout-stderr/final-newline observations are complete and every help-listed flag is obligationized or explicitly deferred.

### 7.2 Require fixture-scale golden morphology before implementation handoff

Renderer-heavy programs that summarize another tool’s output need more than synthetic probes. The generator should require GF rows for pass, fail, mixed pass/fail/skip, nested/deep subtests, no-test/empty, build, panic/stack, race/diagnostic, coverage, and multi-package streams. Each high-risk morphology should be crossed with at least one renderer and one raw/process surface before handoff.

### 7.3 Add a branch-sensitive conflict ledger earlier

When official or reference pressure suggests conflicting behavior, do not force one global rule. Add conflict rows keyed by morphology, invocation route, fixture family, branch/source, and evidence layer. Examples: failed-package exit `0` vs `1`, follow suppression vs full raw preservation, sort ascending vs descending, panic final-pass exit traps.

### 7.4 Make output role de-lumping a standard procedure

For any program that consumes another program’s logs, `Output` must be split into roles before probes: raw follow, diagnostic body, identity header, package final line, build output, panic stack, race warning, no-test marker, coverage line, ordinary log, and line-class filtering. Each role needs subject ownership, timing, renderer effect, and exit effect.

### 7.5 Treat failure details as structured blocks

Failure detail theory should distinguish identity header, elapsed/source identity, body text, stack trace, separator, blank-line geometry, package-level lines, and markdown code-fence boundaries. This should be a generic renderer-heavy rule, not a tparse-specific patch.

### 7.6 Require an exit denominator registry from the first pass

Any CI/test summarizer must model exit as a registry separate from render status. The registry should include render-only failure, failed test, package fail, build, panic, race, parser error, no-pipe, file error, write error, compare warning/delta, invalid flag, and soft invalid option.

### 7.7 Add mode-interaction closure as a gate, not a note

If modes share renderer/path/follow/order/denominator/exit surfaces, one probe per mode is not enough. The generator should create bounded pairwise/triple MI rows and explain why they close the shared surface.

### 7.8 Track synthetic-vs-real fixture coverage

Probe coverage tables should include fixture realism. A synthetic probe can lock a small behavior, but it cannot certify a real fixture family unless the generator proves pass-through. The bookkeeper should flag `synthetic_only_high_risk_surface` separately from generic probe coverage.

### 7.9 Add local-oracle anti-overfit checks

Before official eval, the harness should run a holdout set deliberately generated from the unprobed cross-products: long outputs, real stack traces, multiple packages, cached packages, build/race/no-test variants, markdown/plain/basic cross-products, and follow/progress/timestamp/file interactions. If local green depends on tiny synthetic rows, readiness should be downgraded.

### 7.10 Preserve evidence-layer hygiene

Official failures can design new probes; they must not become clean first-pass truth. The generic meta-program should require every repair row derived from official failure pressure to carry `post_eval_failure` or `postmortem_inference` until a reference-first observation locks it.

## Bottom line

The ADEU theory now owns the correct ontology shape for `tparse`: event stream, lifecycle, subject identity, output roles, renderer grammar, mode controls, side effects, and exit denominators. The remaining gap is the depth and representativeness of that ontology under exact renderer bytes and fixture-scale mode interactions.

The next theoretical refinement should not add random tests. It should strengthen the generic scaffold so it derives, before implementation handoff:

```text
help/control-plane bootstrapping
fixture-scale golden morphology
mode-interaction closure
output-role and failure-block de-lumping
panic/build/race prescan morphology
branch-sensitive exit denominator registry
synthetic-vs-real probe coverage accounting
```

Only after those are reference-observed should the implementation repair loop try to close the remaining official failures.
