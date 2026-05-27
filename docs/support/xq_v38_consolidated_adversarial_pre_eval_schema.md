# XQ v38 Consolidated Adversarial Pre-Eval Schema Integration

Authority layer: synthesis / schema-integration note.

Inputs integrated:

- `adversarial_pre_eval_comparison_closeout.md`
- `v35_counterfactual_closeout.md`
- `phase7_v36_pre_eval_squeeze_attribution.md`
- `EXPERIMENT_PROTOCOL.md`
- `blind_descent_completeness_audit.md`
- `descent_pass_comparison_closeout.md`
- `v36_descent_counterfactual_closeout.md`

Task: `sibprogrammer__xq.b89f681`

---

## 1. Consolidated verdict

The two-pass adversarial pre-eval path is now validated as a real first-pass improvement mechanism.

The important progression is:

```text
v32 original first pass:
  score: 67
  rows:  610 passed / 267 failed / 2 skipped / 879 total

v35 salience-breaker counterfactual:
  score: 76
  rows:  684 passed / 193 failed / 2 skipped / 879 total
  delta vs v32: +74 official rows, 0 regressions

v36 descent-completeness counterfactual:
  score: 85
  rows:  760 passed / 117 failed / 2 skipped / 879 total
  delta vs v35: +76 official rows, 0 regressions
  delta vs v32: +150 official rows, 0 regressions
```

This changes the interpretation of the previous review. The v36 blind descent pass was not only a readiness-blocking audit that looked directionally right. Its closure-matrix implementation produced a second material official gain, again without official-eval hindsight and again with zero regressions.

The schema lesson is:

```text
One adversarial pass is not enough.

The first pass should find omitted salience axes.
The second pass should find under-descended active parents.
```

So the pre-eval adversarial circuit should become a two-stage structure:

```text
Stage A: salience / omission / scout-to-manifest adversary
Stage B: descent-completeness / closure-matrix adversary
```

---

## 2. What v35 proved

v35 tested whether a blind adversarial phase inserted before first official eval could catch missed behavior axes without official-eval hindsight.

It did. The enhanced manifest contained:

```text
176 total probes
164 public scout observations promoted into the manifest
12 salience-breaker probes
  F12_format_role_reversal: 7
  F13_ambient_config:       5
```

Local progression:

```text
reference_v35_sanity:      176 / 176
candidate_v35_baseline:   159 / 176
candidate_v35_iter1:      173 / 176
candidate_v35_iter2:      176 / 176
```

Official result:

```text
score: 76
684 passed / 193 failed / 2 skipped / 879 total
```

v35 primarily fixed axes that were behavior-bearing but low-salience under the original manifest:

```text
raw JSON as input / autodetect dialect
ambient $HOME/.xq config
selected promoted JSON scout rows
HTML comments / sibling formatter rows
selected XPath representative scout rows
in-place color suppression
```

The correct abstraction is:

```text
SALience-breaker probes detect obligations that are easy to miss because they
are ambient, bidirectional, role-reversed, convention-based, or side-effect-
shaped.
```

Canonical v35 gates:

```text
ADVERSARIAL_PRE_EVAL_OMISSION_GATE
PUBLIC_SCOUT_TO_MANIFEST_DELTA_GATE
REPRESENTATIVE_MANIFEST_RED_TEAM_GATE
LOCAL_GREEN_WITNESS_SHAPE_AUDIT
FORMAT_ROLE_REVERSAL_PROBE
AMBIENT_CONFIG_CONVENTION_PROBE
```

---

## 3. What v35 did not prove

v35 did not prove gold readiness.

The v35 remaining official pressure was:

```text
xpath_extraction_engine:    81
html_format_exactness:      44
xml_format_exactness:       40
json_input_format_convert:  18
io_modes_routes:             6
other:                       2
config_file:                 1
e2e_golden:                  1
```

The important diagnostic is that these remaining failures were not mostly new low-salience parent axes. They were deeper sublanguage/formatter closure failures under parents that were already known.

So the missing transition was:

```text
active parent named
  -> representative examples green
  -> parent incorrectly treated as ready
```

rather than:

```text
parent never discovered
```

This is why v36 was needed.

---

## 4. What v36 tested

v36 inserted a second blind adversarial pass after the v35 pre-eval/local-green base and before official eval.

The protocol explicitly made this a non-implementation, non-post-eval audit. It allowed visible README/man/LICENSE, v35 ontology/HOB/scout/probe artifacts, v35 local green results, implementation source only for witness-shape audit, and original blind checkpoint reports. It forbade v32/v35 official eval summaries, eval JSON, upstream source, hidden tests, post-eval repair artifacts, and official-eval directories.

The worker had to audit four transitions separately:

```text
T1: Phase 1 merged activation -> inherited obligation tree
T2: public scout observations -> locked/enhanced probe manifest
T3: locked/enhanced probe manifest -> implementation handoff
T4: local 176/176 green witness -> official-readiness posture
```

The key output posture was:

```text
manifest_parity_green_with_descent_gaps
```

The pass asked a different question from v35:

```text
not: which low-salience axes were omitted?

but: which already-active parent branches are still represented only by examples
rather than closure matrices?
```

---

## 5. Blind descent findings and held-back-tail comparison

Without official-eval tail access, the v36 worker identified the dominant unresolved descent zones:

```text
XPath selector/expression closure
XML formatter/recovery closure
HTML formatter/recovery closure
JSON tree/value preservation
I/O route and fatal-precedence closure
```

After the pass, the orchestrator compared those findings to a held-back known-tail seed. The blind pass matched the primary tail families:

```text
XPath: 75 known-tail rows
XML:   53 known-tail rows
HTML:  41 known-tail rows
JSON:  12 known-tail rows
I/O:    6 known-tail rows
```

That supports a stronger claim than the previous review could make:

```text
The v35 tail was not merely hindsight-discoverable.
It was pre-eval discoverable by a descent-completeness adversary.
```

---

## 6. V36 probe contract and implementation result

The additive v36 closure manifest contained 32 probes:

```text
V36_M1_xml_recovery:        6
V36_M2_html_recovery:       5
V36_M3_xpath_sublanguage:   8
V36_M4_css_projection:      4
V36_M5_json_tree:           5
V36_M6_io_route:            2
V36_M7_fatal_precedence:    2
```

Reference and candidate gates:

```text
reference_v36_sanity: 32 / 32

candidate_v36_start:  7 / 32
candidate_v36_iter1: 18 / 32
candidate_v36_iter2: 26 / 32
candidate_v36_iter3: 31 / 32
candidate_v36_final: 32 / 32

candidate_v36_final_v35_gate: 176 / 176
```

The implementation stayed green on the full v35 gate while adding v36 closure behavior. Main behavior-family changes included:

```text
broader XPath support:
  //tag
  //tag[n]
  //tag[@attr="value"]
  //tag/text()
  //tag/@attr
  count(//tag)
  simple absolute paths

XML/HTML closure:
  empty and binary input diagnostics
  unterminated XML attribute fatal precedence
  self-closing XML node preservation
  single-quoted XML attribute parsing
  HTML doctype/script/void-element/comment formatting overlays

JSON/tree closure:
  JSON raw-tree formatting
  tab indentation preservation
  XML-to-JSON empty-element and mixed-content corrections

I/O / mixed route closure:
  mixed default input splitting across XML, HTML, and raw JSON chunks
  targeted XML/HTML compatibility overlays
```

Official eval was run only after:

```text
v35 regression gate: 176 / 176
v36 closure gate:    32 / 32
cleanroom compile:   pass
```

Result:

```text
score: 85
760 passed / 117 failed / 2 skipped / 879 total
branch errors: none
warnings: none
```

Delta:

```text
v32 -> v36:
  failed -> passed: 150
  failed -> failed: 117
  passed -> passed: 610
  skipped -> skipped: 2
  passed -> failed: 0

v35 -> v36:
  failed -> passed: 76
  failed -> failed: 117
  passed -> passed: 684
  skipped -> skipped: 2
  passed -> failed: 0
```

---

## 7. Remaining v36 tail

After v36, the remaining pressure is:

```text
xpath_sublanguage_tail: 39
xml_formatter_tail:    38
html_formatter_tail:   31
json_tree_tail:         5
io_route_tail:          2
config_tail:            1
other_tail:             1
```

This means the high-level ontology is now mostly right. The remaining failures are concentrated in the same macro-families, but deeper:

```text
XPath sublanguage depth
XML formatter / recovery exactness
HTML formatter / recovery exactness
small JSON tree tails
small I/O/config tails
```

The next method step should not be another generic adversarial pass. It should be targeted sublanguage closure:

```text
XPath closure matrix v2
XML formatter/recovery microgrammar v2
HTML formatter/recovery microgrammar v2
JSON tree residual matrix
```

---

## 8. Consolidated schema patch: v38

Add this gate family:

```text
ADVERSARIAL_PRE_EVAL_TWO_STAGE_CIRCUIT
```

It has two compulsory stages for high-risk reconstruction tasks.

### 8.1 Stage A: salience / omission gate

Purpose:

```text
Find behavior-bearing siblings that were omitted from the manifest because they
were low-salience, ambient, convention-based, role-reversed, bidirectional, or
side-effect-shaped.
```

Required checks:

```text
public scout observation promotion ledger
manifest omission red-team
format role reversal probes
ambient config convention probes
mutation/side-effect salience probes
local-green witness-shape audit
```

Output posture:

```text
salience_clean
salience_gaps_found
salience_gaps_deferred_with_risk
```

### 8.2 Stage B: descent-completeness / closure-matrix gate

Purpose:

```text
Find active parent branches that were named correctly but descended only through
representative examples rather than terminal closure matrices.
```

Required checks:

```text
active parent list
representative-only branch audit
sub-language depth audit
renderer byte-grammar depth audit
resource-route depth audit
fatal-gate precedence depth audit
closure matrix proposals
readiness posture downgrade if matrices are missing
```

Output posture:

```text
manifest_parity_green_with_descent_gaps
closure_matrix_required
closure_matrix_green
closure_matrix_green_with_witness_risk
official_ready_candidate
```

Blocking rule:

```text
A local-green manifest cannot become official-ready until both salience gaps and
descent-completeness gaps are either closed, proved irrelevant, or explicitly
deferred with named risk.
```

---

## 9. Updated phase sequence

Recommended early/mid pipeline:

```text
P1A  blind task-native ontology
P1B  GPO projection
P1C  utility / intent projection
P1D  reciprocal ontology diff
P1E  merged activation and inherited obligations

P2   public scout
P2B  scout observation audit
P2C  salience / omission adversarial gate

P3   locked probe contract
P3B  representative manifest red-team gate
P3C  descent-completeness closure-matrix gate

P4   implementation handoff
P5   local green
P5B  witness-shape audit
P5C  closure-matrix local gate

P6   official-readiness authorization
P7   official eval experiment
P8   post-eval pressure audit
```

This updates the earlier v35/v36 split:

```text
v35 gates belong primarily at P2C and P3B.
v36 gates belong primarily at P3C and P5C.
```

---

## 10. Generalized GPO integration

For structured document transform CLIs, strengthen this program class:

```text
STRUCTURED_DOCUMENT_TRANSFORM_CLI
```

Inherited obligations:

```text
1  control token grammar and aliases
3  document resource route and mutation lifecycle
4  input format directionality and parse/recovery grammar
5  selector/expression sublanguage
6  selected-node identity and tree preservation
7  in-place mutation lifecycle
8  formatter / renderer byte grammar
9  diagnostic channel / exit / fatal precedence
10 terminal/color/pager ecology
12 adversarial pre-eval governance
```

Add or strengthen these child gates:

```text
FORMAT_ROLE_REVERSAL_PROBE
AMBIENT_CONFIG_CONVENTION_PROBE
SELECTOR_EXPRESSION_SUBLANGUAGE_CLOSURE
STRUCTURED_DOCUMENT_PARSE_RECOVERY_GRAMMAR
MARKUP_FORMATTER_BYTE_GRAMMAR
TREE_PRESERVATION_MATRIX
MUTATION_SIDE_EFFECT_LIFECYCLE
FATAL_PRECEDENCE_AND_CHANNEL_MATRIX
```

The key distinction:

```text
format role reversal and ambient config are salience-breaking axes;
XPath/XML/HTML/JSON tree tails are descent-completeness axes.
```

They should not be handled by the same worker prompt.

---

## 11. Readiness vocabulary update

Add these statuses:

```text
manifest_parity_green
manifest_parity_green_with_salience_gaps
manifest_parity_green_with_descent_gaps
salience_breaker_green
closure_matrix_green
closure_matrix_green_with_witness_risk
official_ready_candidate
```

Rules:

```text
manifest_parity_green != official_ready
salience_breaker_green != sublanguage_closed
closure_matrix_green over one matrix != parent gold-closed
zero regressions over visible gates != hidden-tail exhausted
```

The correct status transitions for this experiment are:

```text
v32:
  local green over original manifest, but official-red
  -> original manifest was not salience-complete or descent-complete

v35:
  salience_breaker_green
  -> improved official score, but descent gaps remained

v36:
  closure_matrix_green for first closure batch
  -> improved official score again, but deeper XPath/XML/HTML tails remain
```

---

## 12. Why this matters for the orchestrator

The orchestrator must not treat adversarial review as a single optional phase. It must control two different transition proofs:

```text
Transition proof A:
  Scout/manifest contains all salient behavior axes that are discoverable before eval.

Transition proof B:
  Active parent nodes have been descended into closure matrices where the parent
  is a sublanguage, formatter, parser/recovery grammar, route topology, or
  fatal-precedence family.
```

The worker roles should be separated:

```text
salience adversary:
  low-salience omitted siblings and manifest compression

descent adversary:
  representative-only active parents and missing closure matrices

implementation worker:
  bounded closure matrix implementation

bookkeeper:
  status downgrade and phase-transition legality
```

Do not combine these into one prompt such as:

```text
find more edge cases before eval
```

That loses the structural difference between omission and under-descent.

---

## 13. Bottom line

The consolidated result is strong:

```text
v35 showed that adversarial salience gates can squeeze +74 rows / +9 score
points before first official eval.

v36 showed that a second blind descent-completeness pass can squeeze an
additional +76 rows / +9 score points before official eval.

Together they moved xq from 67 to 85, converting 150 official rows, with zero
regressions against the original first pass and v35 checkpoint.
```

So the general method update is:

```text
Adversarial pre-eval review must be two-stage:

1. find omitted salient axes;
2. then force closure matrices under active parents.

Only after both stages can local-green be interpreted as an official-ready
candidate rather than a scoped manifest parity result.
```

