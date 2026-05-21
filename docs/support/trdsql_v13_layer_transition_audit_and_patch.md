# trdsql v11/v12 Audit and v13 Meta-Program Patch

Task: `noborus__trdsql.d8c5ff6`

Bundle: `programbench_trdsql_gptpro_audit_bundle_20260521.zip`

Requested task from `README_FOR_GPTPRO.md`: audit the three comparable clean-origin/scoped `trdsql` runs layer by layer; explain why the v12 GPT-5.5 run transferred worse than the v12 GPT-5.4-mini run despite broader local observations; decide whether the local locks were replayable or too narrow; separate meta-program, model, handoff, and implementation causes; propose v13 changes and a clean next-run recipe.

## 0. Executive diagnosis

The v12 GPT-5.5 score collapse is not primarily a `trdsql` ontology failure. It is first a **witness-bundle / target-substrate failure**.

The v12 GPT-5.5 candidate passed `90 / 91` locked local reference observations, but official eval failed `1332` rows. Inspecting the official eval JSON shows that **all 1332 failed rows contain the same candidate runtime diagnostic**:

```text
SyntaxError: f-string expression part cannot include a backslash
```

The failing code path is in the submitted executable around the table-creation helper:

```python
conn.execute(f"CREATE TABLE {qname} ({', '.join('\"'+c.replace('\"','\"\"')+'\" TEXT' for c in cols)})")
```

That syntax is accepted by newer Python grammar but rejected by the older interpreter used by the official evaluation substrate. Therefore, the local parity checker validated a witness under one substrate, while official eval ran it under another. In the constructive-witness vocabulary:

```text
local:    W ; Πlocal ; Σlocal  ⊢ Cᴡ : Ωscoped
official: W ; Πofficial ; Σeval ⊬ Cᴡ : Ωscoped
```

This means the candidate was never a valid witness bundle for the evaluator substrate. The official score of `3` is therefore not strong evidence about product behavior, SQL ontology, or renderer coverage. It is mostly evidence that v12 lacked a hard **TARGET_SUBSTRATE_ABI_GATE** and **PACKAGED_ARTIFACT_PARITY_GATE**.

There is a second, independent problem: the v12 GPT-5.5 implementation appears locally replay-oriented. The candidate source contains exact timestamps and fixture/path-specific branches such as `people.csv`, `SELECT 1`, and timestamp literals from locked observations. The one local mismatch was a duplicate `-debug SELECT 1` observation with identical argv but different timestamped stderr bytes. That shows the observation lock itself was not distinguishing deterministic byte grammar from dynamic byte grammar.

So the short answer is:

```text
v12 fixed public-schema re-entry, but not witness-bundle validity.
The 5.5 run did not merely overfit the probes; it first failed to inhabit the target substrate.
The local parity score was therefore epistemically invalid as transfer evidence.
```

## 1. Run-by-run comparison

| Run | Meta-program | Model | Handoff posture | Local gate | Official result | Primary interpretation |
|---|---|---|---|---:|---:|---|
| v11 Run B | v11 | GPT-5.5 medium | scoped clean run | selected scoped probes green | score `52`; `755 passed / 647 failed / 1 skipped / 1403` | Stronger implementation ambition, but public schema re-entry was missing; many official failures were known ontology/probe gaps. |
| v12 mini | v12 | GPT-5.4-mini medium | `official_experiment_with_known_scope_gaps` | `34 / 34` | score `25`; `380 passed / 1022 failed / 1 skipped / 1403` | Cleaner method boundary and source-origin control, but implementation/scaffold too shallow for broad SQL/input/output behavior. |
| v12 5.5 | v12 | GPT-5.5 medium | `scoped_implementation_attempt` | `90 / 91` | score `3`; `70 passed / 1332 failed / 1 skipped / 1403` | Not a product-behavior transfer result. Official failures are dominated by a Python grammar/runtime mismatch in the witness bundle. |

Important row-overlap result:

```text
v11 passed / mini failed: 457 rows
mini passed / v11 failed: 82 rows
v11 passed / v12-5.5 failed: 695 rows
mini passed / v12-5.5 failed: 335 rows
```

This confirms that v12 5.5 was not simply “less complete” than mini. It was invalidated by the official execution substrate.

## 2. Layer-transition diagnosis

The bundle’s requested layer stack is:

```text
visible packet / public schema scout
  -> schema re-entry ontology
  -> obligation ledger / bookkeeper
  -> probe contract
  -> reference observation lock
  -> deferral closure
  -> implementation handoff
  -> candidate implementation
  -> local parity
  -> official eval failures
```

### 2.1 v11 Run B: statement recovery improved, but public schema re-entry was missing

v11 recognized the visible README-level ontology well: `trdsql` is a CLI table-query/conversion tool that parses text-like resources, executes SQL, and renders rows. The official score of `52` came from implementation ambition: it built a generic SQLite-backed row loader and handled enough file-backed SQL/input/output surfaces to pass many rows.

But the audit correctly diagnosed v11’s main failure as:

```text
L4 reference observation -> L2 recursive descent re-entry missed
```

The clean `-help` observation exposed a much larger schema than the README:

```text
-a / -A
-config / -db / -dblist / -driver / -dsn
-debug
input flags/options: -ig -icsv -ijson -iltsv -itbln -itext -iwidth -iyaml -id -ih -ijq -ilr -inull -inum -ir -is
output formats/options: -oat -ocsv -ojson -ojsonl -oltsv -omd -oraw -otbln -ovf -oyaml -oaq -ocrlf -od -oh -onowrap -onull -oq -out -out-without-guess -oz
```

v11 recorded the help output but did not reopen the theorem statement deeply enough. Its failures were therefore true ontology/probe gaps: output renderer exactness, SQL transform semantics, TBLN/YAML grammar, analyze modes, compression, DB/config/driver, jq, stream split, and null semantics.

Layer root:

```text
L4 -> L2 public schema re-entry miss
L1 -> L2 embedded SQL too file-centric
L2 -> L3 format/renderer leaves not terminalized
L3 -> L4 stdout/stderr sometimes collapsed
L5 -> L6 local gate too small
```

### 2.2 v12 mini: method boundary improved, but behavior model remained underpowered

The v12 mini run added the right meta-program features:

```text
IMPLEMENTATION_ORIGIN_BOUNDARY_GATE
PUBLIC_SCHEMA_REENTRY_GATE
split stdout/stderr/file observation locks
known-scope handoff posture
```

It honestly labeled itself as:

```text
official_experiment_with_known_scope_gaps
```

and passed only a small local parity set:

```text
34 / 34
```

The official score of `25` is therefore not surprising. It reflects a shallow clean implementation over a large public schema. Its failures are mostly product-theory and implementation-depth failures, not substrate-collapse failures. Largest official groups included SQL features, external trdsql queries, input formats, output formats, advanced queries, readers/writers, and input options.

Layer root:

```text
L2 -> L3: representative probes did not terminalize broad grammar families
L3 -> L5: scoped exclusions knowingly remained outside implementation
L5 -> L6: local gate was small but honest
L6 -> L7: official eval exercised broad gold surfaces not in the scoped contract
```

### 2.3 v12 GPT-5.5: public schema and local parity were broader, but witness validity failed

The v12 GPT-5.5 run did more public-schema work than mini. It recorded help aliases, version aliases, unknown/missing flag behavior, debug, expression-only SQL, route variants, more input/output formats, compression values, config/db smoke, and `91` total observation directories.

But the implementation handoff and local checker did not validate the same witness bundle that official eval would execute. The local parity checker ran:

```text
phase7_implementation/submission_src/executable
```

through local `subprocess.run(...)` in the current environment. It did not prove:

```text
1. the packaged ProgramBench tarball expands correctly;
2. compile.sh produces the same executable official eval will run;
3. the executable parses under the official interpreter;
4. the shebang resolves to a compatible runtime;
5. local parity runs inside an evaluator-equivalent container/substrate.
```

Official eval then failed before product behavior on virtually every row. That is:

```text
candidate implementation -> local parity -> official eval
```

but the real missing layer is between witness construction and local parity:

```text
Cᴡ authoring
  -> Cᴡ packaging
  -> Cᴡ target-substrate ABI validation
  -> local parity
```

v12 did not yet require that transition.

Layer root:

```text
Implementation witness produced code that was valid under Σlocal but invalid under Σeval.
Local parity used the wrong substrate and therefore over-promoted Cᴡ.
Official failures are mostly witness-bundle invalidity, not product ontology evidence.
```

## 3. Why did v12 GPT-5.5 transfer worse than v12 mini?

Primary cause:

```text
v12 GPT-5.5 candidate source used Python grammar not accepted by the official interpreter.
```

The score difference is therefore not a clean model-capability comparison.

Secondary causes:

1. **The 5.5 worker optimized for exact locked observation parity.** Evidence: hardcoded timestamps and fixture-specific branches appear in the candidate source. This made the implementation brittle even before official product coverage is considered.
2. **The broader local observation set increased replay temptation.** `91` exact byte observations without corresponding metamorphic/held-out siblings can encourage exact-output synthesis instead of a generative program model.
3. **The local parity checker lacked target-substrate proof.** It compared bytes in the local environment, not in the official execution environment.
4. **Dynamic bytes were locked as exact bytes.** Timestamped debug/SQL diagnostics should have been modeled as dynamic grammar or normalized observations. Exact byte locking forced the candidate toward timestamp literals.
5. **The v12 handoff posture was scoped, but the implementation still needed a minimum general architecture floor.** It specified many observed leaves, but not enough implementation architecture invariants such as “use a real SQL substrate rather than per-probe dispatch” and “must pass unseen expression/input/renderer siblings.”

The mini run scored higher not because it was theoretically better, but because it did not suffer the catastrophic target-runtime syntax failure. Its failures were more ordinary undercoverage.

## 4. Did v12 GPT-5.5 overfit exact locked probes?

Answer: **probably yes at the local implementation level, but official score collapse itself cannot prove product overfit because target-substrate failure dominates.**

Evidence of replay risk:

```text
- candidate source contains exact timestamp literals from reference observations;
- candidate source contains fixture-specific checks such as people.csv branches;
- local parity failed one duplicate debug observation because identical argv produced different timestamped stderr bytes;
- P8 held-out/metamorphic probes were reserved but not executed as a blocking pre-official gate;
- the official run never reached enough product behavior to measure generalization because the executable failed to parse.
```

So classify this as:

```text
replay_risk_observed
product_generalization_unmeasured_due_to_substrate_failure
```

not as:

```text
official_eval_proves_probe_overfit
```

## 5. Were the 91 locked observations too replayable, too narrow, or missing generative probes?

Yes. The 91 observations were useful as public-surface evidence, but too many were exact snapshots rather than rule witnesses.

Specific weaknesses:

| Observation design issue | What happened | v13 repair |
|---|---|---|
| Dynamic timestamps locked as exact bytes | Same argv could have distinct timestamped stderr. Candidate hardcoded observed dates. | Add `DYNAMIC_OBSERVATION_CANONICALIZATION_GATE`. |
| Held-out probes reserved, not enforced | P8 listed metamorphic ideas but did not gate implementation. | Make held-out/metamorphic probes blocking for scoped-transfer claims. |
| Source literal overlap unchecked | Candidate could encode exact fixture names and timestamps. | Add `CANDIDATE_LITERAL_OVERLAP_AUDIT`. |
| Local parity not target-substrate equivalent | `90/91` was measured under local Python, not official runtime. | Add `TARGET_SUBSTRATE_ABI_GATE` and `PACKAGED_ARTIFACT_PARITY_GATE`. |
| Representative leaves overcalled “gold-ready” | Many format/route leaves were representative, not generative families. | Add `REPRESENTATIVE_LEAF_TRANSFER_LIMIT`. |
| Architecture invariants missing | Handoff named surfaces but did not force real SQL/format/router architecture. | Add `IMPLEMENTATION_STRATEGY_FITNESS_GATE`. |

## 6. Did v12 stricter scoped handoff reduce implementation ambition?

Partly yes.

v12 correctly prevented false gold claims. That was a methodological improvement. But it also created a failure mode:

```text
scoped exact observations
  -> implementation optimizes for local byte parity
  -> broad abstract behavior model receives less pressure
  -> official eval generalization can drop
```

v11 was less disciplined, but its implementation had a more general SQLite-backed architecture. That made it pass `755` rows even though its ontology was incomplete. v12 mini and v12 5.5 had better epistemic hygiene, but weaker or invalid witness construction.

The v13 fix is not to weaken scoped handoff. It is to add an **implementation architecture floor**:

```text
A scoped handoff may be scoped in public behavior, but the implementation must still be generative for the program's core substrate.
```

For `trdsql`, the architecture floor is:

```text
embedded SQL engine + source/table binder + input decoder family + output router/renderer family
```

not:

```text
exact locked argv/fixture replay
```

## 7. Attribution: meta-program vs model vs handoff vs implementation

### 7.1 Meta-program weaknesses

v12 was missing these gates:

```text
TARGET_SUBSTRATE_ABI_GATE
PACKAGED_ARTIFACT_PARITY_GATE
DYNAMIC_OBSERVATION_CANONICALIZATION_GATE
DUPLICATE_ARGV_NONDETERMINISM_GATE
CANDIDATE_LITERAL_OVERLAP_AUDIT
IMPLEMENTATION_STRATEGY_FITNESS_GATE
REPRESENTATIVE_LEAF_TRANSFER_LIMIT
OFFICIAL_FAILURE_SURFACE_DOMINANCE_GATE
```

It had public schema re-entry, but not enough witness-bundle validity and anti-replay enforcement.

### 7.2 Implementation-handoff weaknesses

The handoff allowed local parity to mean too much. It did not require:

```text
- evaluator-like runtime/substrate declaration;
- syntax/compile check under target ABI;
- packaged artifact smoke before local parity;
- local parity against the packaged artifact, not workspace source;
- anti-replay/literal-overlap audit;
- dynamic-byte normalization;
- architecture-level owner map for SQL/input/output implementation.
```

### 7.3 Model/worker weaknesses

The GPT-5.5 worker produced invalid official-runtime Python and apparently hardcoded dynamic observation values. That is an implementation quality failure by the worker.

The GPT-5.4-mini worker produced a lower-ambition but syntactically valid implementation. Its score reflects undercoverage rather than a catastrophic artifact failure.

### 7.4 Candidate implementation transfer errors

The v12 GPT-5.5 run’s dominant transfer error is:

```text
Python grammar version mismatch in submitted executable.
```

This should be classified as:

```text
witness_bundle_invalid
candidate_substrate_transfer_error
```

not as:

```text
SQL semantics gap
renderer gap
format dialect gap
model capability comparison
```

### 7.5 Product-theory gaps still present after substrate repair

Once the witness bundle is valid, the true `trdsql` product gaps likely remain:

```text
SQL expression/advanced query semantics
input dialect grammars: YAML, JSONL, jq/path, TBLN, text, fixed-width
output renderer byte grammars: oat, tbln, vf, yaml, raw/csv edge cases
output options: quote, quote-all, delimiter, CRLF, headers, nowrap, nulls
source routing: stdin, wildcards, query-file, table-file, path-to-table identity
compression readers/writers and file route guessing
config/db/driver diagnostics and no-op/smoke behavior
analyze/debug dynamic diagnostics
null semantics across SQL/input/output
```

Those are real program-theory/implementation leaves, but the v12 GPT-5.5 official result cannot quantify them because execution failed first.

## 8. Proposed v13 meta-program patch

Keep the v8-v12 kernel:

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

Add v13 as a **witness-bundle and transfer-validity hardening release**.

### 8.1 New macro: TARGET_SUBSTRATE_ABI_GATE

```text
TARGET_SUBSTRATE_ABI_GATE
  = Factor target runtime: interpreter/compiler, version, OS, stdlib, toolchain,
    dependency availability, shebang resolution, env PATH, cwd, file permissions.
  + Partition language/runtime feature lattice: accepted syntax, unavailable
    libraries, version-specific behavior, line-ending/path behavior, locale.
  + Bind candidate artifact to substrate: source file, generated executable,
    compile.sh output, package root, shebang, import path.
  + Sequence build -> syntax check -> smoke -> local parity -> official eval.
  + Expose pre-product failure surfaces: SyntaxError, ImportError,
    compile_failed, missing executable, bad shebang, permission denied.
  + Warrant product evidence only if candidate product behavior is reached.
```

Trigger:

```text
Any candidate is interpreted, compiled, generated, packaged, shebang-driven,
uses external libraries, depends on stdlib version, or is evaluated in a
container different from the authoring environment.
```

Rule:

```text
A candidate cannot be local-parity-ready until it parses/builds and passes a
minimal smoke command under the declared target ABI or an evaluator-equivalent
compatibility matrix.
```

For Python candidates, minimum checks:

```text
python3.X -m py_compile source_or_executable
./compile.sh in package root
./executable -version or no-args smoke
./executable with one expression-only command
same checks inside the closest available evaluator-like container
```

If the exact evaluator Python is unknown, use a conservative matrix:

```text
Python 3.10, 3.11, 3.12, 3.13 where feasible
```

and block features whose acceptance depends on only the newest interpreter unless the evaluator is proven to support them.

### 8.2 New macro: PACKAGED_ARTIFACT_PARITY_GATE

```text
PACKAGED_ARTIFACT_PARITY_GATE
  = Factor Cᴡ into source, compile script, executable, package tarball,
    permissions, generated resources, dependency pins, and entrypoints.
  + Sequence pack -> unpack -> compile -> smoke -> locked parity.
  + Expose package-level failures before product rows.
  + Warrant local parity only for the exact artifact official eval will run.
```

Rule:

```text
Local parity over workspace source is smoke evidence only.
Local parity that supports official submission must execute the packaged
artifact after the same compile/install path official eval uses.
```

Required record:

```yaml
packaged_artifact_parity_gate:
  package_ref: submission.tar.gz
  unpack_root_listing_hash: ...
  compile_script_ref: compile.sh
  compile_exit: ...
  executable_ref: executable
  executable_shebang: ...
  executable_permissions: ...
  target_runtime_ref: ...
  smoke_refs:
    - no_args_or_help
    - version_if_available
    - minimal_success
    - minimal_failure
  locked_parity_runner_ref: ...
  parity_artifact_identity: packaged_artifact | workspace_executable
  promotion_effect: blocks_official_if_not_packaged_artifact
```

### 8.3 New macro: OFFICIAL_FAILURE_SURFACE_DOMINANCE_GATE

```text
OFFICIAL_FAILURE_SURFACE_DOMINANCE_GATE
  = Cluster official failures by first externally visible failure surface.
  + If a single pre-product artifact/substrate message dominates, classify the
    run as witness-bundle invalid before product-theory repair.
```

Trigger:

```text
Official failures contain repeated compile/runtime/import/shebang/package errors.
```

Rule:

```text
If more than a small threshold of failed rows share the same pre-product
candidate failure surface, stop product diagnosis and repair the witness bundle.
```

Suggested threshold:

```text
>= 20% of official failures, or >= 50 rows, or any compile_failed/missing executable.
```

v12 GPT-5.5 classification:

```text
1332 / 1332 official failed rows contain the same SyntaxError message.
=> witness_bundle_invalid; product-theory diagnosis blocked.
```

### 8.4 New macro: DYNAMIC_OBSERVATION_CANONICALIZATION_GATE

```text
DYNAMIC_OBSERVATION_CANONICALIZATION_GATE
  = Factor observed bytes into deterministic tokens and dynamic tokens.
  + Bind dynamic tokens to source: timestamp, PID, path, tempdir, random id,
    locale, error prefix, environment, version.
  + Transform dynamic source into a grammar or normalization rule.
  + Expose byte oracle as exact, regex/semantic, normalized-hash, or conflict.
  + Warrant exact-byte promotion only when dynamic tokens are frozen by design.
```

Trigger:

```text
Observed stdout/stderr/file bytes contain timestamps, temp paths, random ids,
PIDs, generated names, environment-specific paths, or duplicate argv with
non-identical bytes.
```

Rule:

```text
Dynamic observations cannot be locked as ordinary exact byte leaves unless the
source of dynamism is controlled. Otherwise they must be normalized or modeled
as grammar classes.
```

v12 GPT-5.5 example:

```text
-debug SELECT 1 observations had timestamped stderr. Exact byte locks induced
hardcoded timestamps and one duplicate-argv local mismatch.
```

### 8.5 New macro: DUPLICATE_ARGV_NONDETERMINISM_GATE

```text
DUPLICATE_ARGV_NONDETERMINISM_GATE
  = Detect two or more locked observations with identical argv/stdin/files_before
    but different stdout/stderr/exit/files_after.
  + Classify the difference as dynamic token, substrate difference, conflict, or
    observation contamination.
  + Block exact-byte parity claims until resolved.
```

Rule:

```text
Identical input cannot define two deterministic exact byte leaves unless an
unrecorded hidden variable is added to the observation key.
```

Required action:

```text
Add the hidden variable to the probe contract, normalize the dynamic token, or
mark the pair conflict-isolated. Do not force implementation to match both.
```

### 8.6 New macro: CANDIDATE_LITERAL_OVERLAP_AUDIT

```text
CANDIDATE_LITERAL_OVERLAP_AUDIT
  = Scan candidate source and generated resources for high-entropy substrings
    from locked reference outputs, exact timestamps, exact fixture names,
    exact probe argv tuples, and exact file contents.
  + Classify overlaps as legitimate constants, public help text, generated
    renderer grammar, suspicious replay, or prohibited oracle embedding.
```

Rule:

```text
A candidate with unexplained high-overlap literals may be scoped-smoke-ready,
but cannot be anti-replay-ready.
```

Do not over-enforce: common public strings such as `Usage`, format names, flag names, and `trdsql version devel` are legitimate. The audit targets high-entropy dynamic values and fixture-specific branch logic.

### 8.7 New macro: IMPLEMENTATION_STRATEGY_FITNESS_GATE

```text
IMPLEMENTATION_STRATEGY_FITNESS_GATE
  = Bind each high-risk ontology parent to an implementation strategy,
    not merely to locked outputs.
  + Require a generative owner for the program's core substrate.
  + Require held-out siblings that prove the strategy rather than argv/fixture
    replay.
```

For embedded-language tools such as `trdsql`, minimum strategy rows:

```text
SQLSubstrate:
  strategy = real SQL engine or explicitly bounded SQL parser
  must cover expression-only and file-backed query modes.

SourceBinder:
  strategy = table identity + path/stdin/query-file/table-file router.

InputDialects:
  strategy = decoder family with stated column/value/null rules.

OutputRouter:
  strategy = renderer family and file route/compression strategy.

Diagnostics:
  strategy = parse/resource/SQL/debug dynamic grammar, not exact timestamp replay.
```

Rule:

```text
A scoped implementation may be limited in branch coverage, but it must still be
generative for the included parent families.
```

### 8.8 New macro: REPRESENTATIVE_LEAF_TRANSFER_LIMIT

```text
REPRESENTATIVE_LEAF_TRANSFER_LIMIT
  = Mark a leaf observed by one representative fixture as representative-only,
    not family-ready, unless sibling/metamorphic coverage proves the generator.
```

Rule:

```text
`gold-ready representative` is not the same as `family gold-ready`.
The handoff must specify which one is intended.
```

Recommended statuses:

```text
representative_scoped_ready
representative_transfer_limited
family_gold_ready
family_deferred_with_expected_risk
```

### 8.9 Revised local parity semantics

v13 local parity should be split:

```text
workspace_smoke_parity:
  runs source/executable in authoring workspace; never enough for official.

packaged_substrate_parity:
  runs packaged artifact after compile in target/eval-like substrate; required
  before official eval.

anti_replay_transfer_parity:
  runs held-out/metamorphic siblings hidden from implementation construction;
  required for broad transfer claims.
```

A run may report `90/91 workspace parity`, but it must not call that an official-preflight gate unless packaged-substrate parity also passes.

## 9. Task-specific trdsql repair scaffold for the next clean run

### 9.1 First repair target: witness bundle, not product behavior

Before touching SQL or format semantics, run:

```text
T0 Target substrate ABI scout
T1 Packaged artifact compile/smoke
T2 Packaged locked parity rerun
T3 Official-failure dominance check
```

For the current v12 GPT-5.5 candidate, the first patch would be to remove Python-version-specific f-string syntax. But for a clean next run, do not patch from official failure text as product evidence. Instead, add the v13 gate that forbids such a candidate from reaching official eval.

### 9.2 Core generative architecture required

A clean v13 `trdsql` implementation handoff should require these implementation owners:

```text
TRDSQLProgram
  ├─ ControlPlane
  │   ├─ Go-flag-like parser
  │   ├─ help/no-args/version/alias exits
  │   └─ missing/unknown flag diagnostics
  ├─ SQLSubstrate
  │   ├─ expression-only SQL
  │   ├─ file-backed SQL
  │   ├─ query-file route
  │   ├─ table-file/source route
  │   ├─ aliases/subqueries/functions/operators where supported by engine
  │   └─ SQL/resource diagnostics
  ├─ SourceBinder
  │   ├─ path-to-table identity
  │   ├─ stdin keyword route
  │   ├─ JSON path suffix / jq minimal route
  │   ├─ wildcard route
  │   └─ extension guessing
  ├─ InputDialects
  │   ├─ CSV/header/delimiter/null/skip/limit/preread/rownum
  │   ├─ JSON/JSONL/nested/path
  │   ├─ LTSV
  │   ├─ YAML
  │   ├─ TBLN
  │   ├─ text
  │   └─ fixed-width
  ├─ OutputRouterAndRenderers
  │   ├─ stdout vs -out file route
  │   ├─ output guessing / out-without-guess
  │   ├─ csv/json/jsonl/ltsv/md/raw/oat/tbln/vf/yaml
  │   ├─ header/delimiter/quote/quote-all/CRLF/null/nowrap
  │   └─ compression writers and compressed readers where in scope
  ├─ ModeFamilies
  │   ├─ -a full analysis
  │   ├─ -A suggestion-only
  │   ├─ -debug dynamic diagnostics
  │   └─ db/config/driver/dsn/dblist smoke/diagnostics
  └─ WitnessBundle
      ├─ target runtime ABI
      ├─ package/compile/entrypoint
      ├─ dependency pins/fallbacks
      └─ anti-replay audit
```

### 9.3 Probes to generate before any implementation patch

#### P0 — Target substrate and packaged artifact

```text
P0-A: record local and eval-like python versions, shebang resolution, PATH, cwd.
P0-B: unpack submission.tar.gz, run compile.sh, record executable metadata.
P0-C: run py_compile or equivalent syntax check under target/matrix interpreters.
P0-D: run packaged executable no-args, -version, SELECT 1, missing file.
P0-E: compare workspace parity vs packaged-substrate parity.
```

#### P1 — Dynamic observation normalization

```text
P1-A: run identical -debug SELECT 1 twice; compare timestamp token behavior.
P1-B: run SQL error twice; compare timestamp/error prefix behavior.
P1-C: classify dynamic fields: exact, regex, normalized, or conflict.
```

#### P2 — Anti-replay / literal-overlap audit

```text
P2-A: scan source for exact timestamps from observations.
P2-B: scan for high-entropy stdout/stderr substrings.
P2-C: scan for fixture-specific dispatch branches.
P2-D: require explanations or downgrade anti-replay readiness.
```

#### P3 — SQL generative substrate

```text
SELECT 1
SELECT 2
SELECT NULL
SELECT CAST('123' AS INTEGER)
SELECT 1 AS a, 2 AS b
SELECT 1+2
SELECT * FROM csvfile
SELECT aliasing / WHERE / ORDER / LIMIT over changed fixture
JOIN two generated files
subquery over generated fixture
invalid syntax
missing table
missing column
```

The implementation may see the rule family, but at least one expression and one file-backed sibling should be held out.

#### P4 — Source route metamorphics

```text
same table via FROM path vs -t source route
same query via argv vs -q file
same data via file path vs stdin keyword
extension guessing true/false with no-extension file
JSON path suffix vs -ijq representative
wildcard no-match and wildcard multi-match
```

#### P5 — Input dialect matrix

```text
CSV header/no-header, delimiter, empty cell, inull, rownum, skip/limit/preread
JSON object array, nested object, JSONL, scalar/empty/malformed
YAML sequence/object/null/nested
LTSV simple and special chars
TBLN roundtrip plus malformed/intuitive specimen
text one-column and blank lines
fixed-width spec grammar representative
```

#### P6 — Output renderer / router matrix

```text
csv/json/jsonl/ltsv/md/raw/oat/tbln/vf/yaml over same semantic rows
header/no-header
quote-all / quote char / delimiter / CRLF
onull over SQL NULL and input-converted NULL
stdout vs -out
-out guessing vs -out-without-guess
compression: gz/bz2/xz and zstd/lz4 if dependencies are available or modeled
special chars, trailing newlines, empty rows, multi-column rows
```

#### P7 — Mode and diagnostics

```text
help/no-args/-h/--help exit/channel matrix
version aliases
unknown/missing flag matrix
-a vs -A on changed CSV fixture
-debug normal query and SQL/resource error
config/db/driver/dsn/dblist smoke and missing/malformed config
```

#### P8 — Official-like transfer preflight

```text
Run packaged-substrate parity on all locked reference rows.
Run held-out/metamorphic siblings not used to author the implementation.
Run failure-surface dominance classifier.
Block official eval if pre-product candidate failures dominate.
```

## 10. v13 bookkeeper additions

Add blocking objections:

```text
target_substrate_abi_unproven
packaged_artifact_not_parity_checked
workspace_parity_promoted_to_official_parity
pre_product_failure_surface_dominates
syntax_or_compile_failure_misclassified_as_product_gap
dynamic_observation_locked_as_exact_without_source_control
duplicate_argv_conflict_unresolved
candidate_literal_overlap_unexplained
representative_leaf_promoted_to_family_gold
held_out_metamorphic_gate_reserved_but_not_run
implementation_strategy_missing_for_core_substrate
scoped_handoff_without_expected_transfer_band
```

For every official-eval failure cluster, the bookkeeper must first ask:

```text
Did the candidate reach product behavior?
```

If no:

```text
classify as witness_bundle_invalid / substrate_abi_failure / package_failure /
resource_ecology_failure / dependency_failure before product repair.
```

## 11. v13 next-run recipe

Use a clean run; do not import source-derived contamination or official failure specifics as behavior truth.

### Step 1 — Public schema scout

Reuse v12’s public schema re-entry shape, but separate:

```text
schema inventory
representative probe observations
dynamic-byte observations
runtime/substrate observations
```

### Step 2 — Ontology re-entry with architecture floor

Require the tree to state:

```text
SQLSubstrate generative strategy
InputDialect strategy
OutputRenderer strategy
Diagnostic dynamic grammar strategy
WitnessBundle target ABI strategy
```

### Step 3 — Probe contract with deterministic/dynamic classes

Every reference observation row records:

```text
stdout_exact_or_normalized
stderr_exact_or_normalized
exit
file effects
runtime/substrate key
hidden dynamic fields
locked_discriminator_ref
representative_or_family_status
```

### Step 4 — Build implementation under scoped label, but generative core

Handoff type may remain:

```text
scoped_implementation_attempt
```

but the implementation must still satisfy:

```text
not exact argv dispatch
not fixture signature dispatch
not timestamp literal replay
not reference byte embedding as primary behavior
```

### Step 5 — Packaged target-substrate gate before local parity

```text
unpack submission
run compile.sh
run target/matrix syntax check
run smoke commands
then run locked parity on the packaged artifact
```

### Step 6 — Literal-overlap audit

Run before official eval. Any suspicious dynamic literals or exact fixture-output copies must be explained or demote the run to `scoped_smoke_only`.

### Step 7 — Held-out/metamorphic gate

Run at least:

```text
SQL expression perturbation
CSV fixture perturbation
stdout/file route sibling
JSON/YAML nested sibling
renderer special-char sibling
debug timestamp repeat
```

### Step 8 — Official eval only after preflight

Before official eval, emit:

```yaml
official_preflight:
  target_substrate_abi_gate: passed
  packaged_artifact_parity_gate: passed
  dynamic_observation_gate: passed_or_normalized
  literal_overlap_audit: passed_or_scoped_risk
  held_out_metamorphic_gate: passed
  handoff_type: scoped_implementation_attempt | official_experiment_with_known_scope_gaps | gold_implementation_attempt
  expected_transfer_band: ...
  known_uncovered_families: ...
```

If any target-substrate or package gate fails, official eval is blocked.

## 12. Revised interpretation of the three runs

### v11 Run B

```text
Useful evidence for public-schema re-entry and statement recovery gaps.
Implementation ambition was higher than v12 mini/5.5, hence score 52.
But v11 should not be considered methodologically stronger because it allowed scoped gaps into official posture.
```

### v12 mini

```text
Useful clean v12 control run.
It shows v12 hygiene can preserve clean boundaries, but the implementation and probe scope were too narrow for the broad public schema.
```

### v12 GPT-5.5

```text
Useful negative evidence for witness-bundle validity and anti-replay controls.
Not a reliable measure of GPT-5.5 product reconstruction ability on trdsql.
Its official rows are dominated by target-substrate SyntaxError, so product-theory diagnosis must be blocked until the witness bundle passes v13 preflight.
```

## 13. Compact v13 self-amendment record

```yaml
self_amendment_record:
  candidate_advancement_ref: trdsql_v13_layer_transition_audit_and_patch.md
  integration_class: structural_integration
  ontology_delta:
    - witness-bundle validity becomes a required layer between implementation and parity
    - target substrate ABI becomes a first-class substrate node
    - dynamic byte observations become grammar/normalization leaves
    - packaged artifact identity becomes the parity object, not workspace source
    - representative leaves are separated from family gold leaves
  epistemic_delta:
    - local parity is invalid as transfer evidence unless target-substrate parity passes
    - official failures dominated by pre-product candidate errors cannot become product-theory evidence
    - high local parity with literal overlap is replay-risk evidence, not anti-replay evidence
  deontic_delta:
    - official eval is blocked by target_substrate_abi_unproven or packaged_artifact_not_parity_checked
    - implementation handoff must include a generative architecture floor for core program substrate
    - dynamic observations must be normalized or conflict-isolated before exact-byte parity claims
  utility_delta:
    - prevents score-3 style collapses where the candidate never inhabits the evaluator substrate
    - preserves v12 public schema gains while restoring v11-like generative implementation pressure
  governance_preservation_posture: O/E/D/U legibility preserved; source contamination remains forbidden
  ratification_status: experimental_support_revision
```

## 14. Bottom line

The next meta-program revision should not merely add more `trdsql` probes. It should insert a new invariant:

```text
No code witness can be evaluated as a program witness until the witness bundle
is proven to run under the target substrate.
```

Then it should strengthen v12’s public-schema re-entry with:

```text
anti-replay probes
metamorphic siblings
dynamic-byte normalization
architecture-floor handoff
packaged-substrate parity
```

That is the v13 path: preserve clean reconstruction and public schema descent, but make the candidate prove that it is a valid, generative witness bundle before any official eval pressure is interpreted as product-theory evidence.
