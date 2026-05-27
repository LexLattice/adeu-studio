# XQ v39 Second-Descent Result Integration / v40 Schema Patch

Authority layer: support / method-integration review.

Input artifact: `v39_pre_eval_descent_closeout.md`.

## 1. Verdict

The v39 pass is a real positive method result, but it changes the recommended next phase.

It confirms that a second Stage-B descent-completeness pass can still recover official rows before post-eval/source-tail repair, while preserving all earlier regression gates. But the marginal yield dropped from the first descent pass. That means the method has likely moved from:

```text
broad under-descended parent recovery
```

into:

```text
targeted microgrammar exactness / source-compatible tail closure
```

So v39 should be integrated as evidence for a **descent saturation and targeted microgrammar transition rule**, not as a license to keep running generic adversarial descent indefinitely.

## 2. Measured Result

The additive v39 manifest contained 33 probes:

```text
V39_M1_xpath_deeper_closure:             10
V39_M2_xml_microgrammar_closure:          6
V39_M3_html_rawtext_recovery_closure:     7
V39_M4_json_indent_tree_closure:          6
V39_M5_route_config_precedence_closure:   4
```

Reference and candidate gates:

```text
reference_v39_sanity:       33 / 33
candidate_v39_start:        13 / 33
candidate_v39_iter1:        30 / 33
candidate_v39_iter2:        33 / 33
candidate_v39_final:        33 / 33
candidate_v39_final_v35:   176 / 176
candidate_v39_final_v36:    32 / 32
```

Official measurement:

```text
score: 88
raw:   781 passed / 96 failed / 2 skipped / 879 total
branch errors: none
warnings: none
```

Progression:

```text
v32 first pass:                 score 67, 610 passed / 267 failed / 2 skipped
v35 salience counterfactual:    score 76, 684 passed / 193 failed / 2 skipped
v36 descent counterfactual:     score 85, 760 passed / 117 failed / 2 skipped
v39 second descent pass:        score 88, 781 passed /  96 failed / 2 skipped
```

Delta:

```text
v32 -> v39: +171 rows, 0 regressions
v35 -> v39:  +97 rows, 0 regressions
v36 -> v39:  +21 rows, 0 regressions
```

## 3. Interpretation

The sequence now shows three distinct pre-eval improvement regimes:

```text
Stage A: salience / omission recovery
  v32 -> v35: +74 rows

Stage B1: broad descent-completeness closure
  v35 -> v36: +76 rows

Stage B2: residual descent / terminal leaf squeeze
  v36 -> v39: +21 rows
```

The v39 pass remained useful because it targeted still-active parents that had not been terminalized deeply enough:

```text
deeper XPath child-path, predicate-child, union, wildcard-attribute predicate,
and malformed-bracket behavior

XML BOM, multiline-comment, unknown-entity, and unclosed-EOF behavior

HTML raw-text script/style, pre/comment/optional-list/void-attribute overlays

raw JSON custom indentation and sorted raw-object rendering

ambient config multiple-equals handling

route/fatal-precedence preservation around bad XPath/CSS and missing files
```

But the reduced gain indicates that another broad “find more descent gaps” pass is likely lower ROI than a targeted microgrammar pass.

## 4. Remaining Tail After v39

The remaining official pressure is now:

```text
xml_formatter_tail:      34
html_formatter_tail:     29
xpath_sublanguage_tail:  26
io_route_tail:            2
json_tree_tail:           2
config_tail:              1
css_selector_tail:        1
other_tail:               1
```

This is not an ontology-parent discovery problem anymore. The parent classes are known:

```text
structured document formatter/recovery
selector/expression sublanguage
format directionality and tree preservation
route/config/fatal precedence
```

The broken layer is mostly:

```text
terminal microgrammar / target-compatible byte behavior
```

## 5. v40 Schema Additions

### 5.1 `PRE_EVAL_DESCENT_YIELD_ACCOUNTING_GATE`

Purpose:

```text
Record whether additional pre-eval adversarial passes are finding new parents,
new child matrices, or only small terminal leaves.
```

Required row:

```yaml
pre_eval_descent_yield:
  pass_id: string
  previous_base: string
  added_probe_count: int
  parent_families_touched: []
  new_parent_count: int
  new_child_matrix_count: int
  terminal_leaf_count: int
  local_start_pass_rate: string
  local_final_pass_rate: string
  regression_gate_refs: []
  official_delta_if_measured:
    score_delta: int | null
    newly_passing_rows: int | null
    regressions: int | null
  posture:
    high_yield_parent_recovery |
    high_yield_child_matrix_recovery |
    low_yield_terminal_squeeze |
    saturated_generic_descent
```

### 5.2 `DESCENT_SATURATION_AND_ESCALATION_GATE`

Rule:

```text
If a second or later generic descent pass produces mostly terminal microgrammar
leaves and substantially lower yield than the previous descent pass, stop broad
adversarial descent and switch to targeted microgrammar/source-tail closure.
```

Suggested trigger:

```text
new_parent_count = 0
remaining failures concentrate in ≤ 3 known parent families
latest measured gain < 50% of prior descent-pass gain
or added probes are mostly formatter/parser byte microgrammar variants
```

For v39:

```text
v36 gain: +76 rows
v39 gain: +21 rows
remaining tail: XML/HTML/XPath dominant
classification: low_yield_terminal_squeeze
next posture: targeted_microgrammar_closure
```

### 5.3 `TARGETED_MICROGRAMMAR_CLOSURE_GATE`

Trigger:

```text
Remaining pressure is concentrated under already-known sublanguages, formatters,
recovery grammars, or byte projections.
```

Required matrix:

```yaml
targeted_microgrammar_closure:
  parent_family: XML | HTML | XPath | JSON | CSS | route_config | other
  microgrammar_axes: []
  public_reference_probe_rows: []
  negative_sibling_rows: []
  byte_or_tree_or_exit_surfaces: []
  target_library_or_source_tail_needed: true | false
  preservation_gate_refs: []
  implementation_owner: string
  closure_status:
    matrix_needed |
    reference_locked |
    source_tail_needed |
    implementation_ready |
    deferred_with_risk
```

### 5.4 `SOURCE_TAIL_ESCALATION_AFTER_PUBLIC_MICROGRAMMAR_GATE`

Rule:

```text
If a known formatter/parser microgrammar remains red after two public-reference
microgrammar passes, source-tail or target-library equivalence analysis becomes
a justified next method, not a failure of blind ontology.
```

This is especially relevant for:

```text
XML recovery/error/encoding microgrammar
HTML formatter/raw-text/optional-tag byte grammar
XPath predicate/function semantics
```

## 6. Updated XQ Pre-Eval Circuit

The pre-eval sequence should now be:

```text
P1A  blind task-native ontology
P1B  GPO projection
P1C  utility/intent projection
P1D  reciprocal ontology diff
P1E  merged activation and inherited obligations

P2   public scout
P2B  scout observation audit
P2C  salience / omission adversarial gate

P3   locked probe contract
P3B  representative manifest red-team gate
P3C  first descent-completeness closure-matrix gate
P3D  second descent squeeze only if novelty/yield posture supports it
P3E  descent saturation gate

P4   targeted microgrammar closure matrix or source-tail authorization
P5   implementation handoff
P6   local green + regression stack
P7   official-readiness authorization
P8   official eval experiment
```

## 7. Recommended Next XQ Move

Do not run another generic descent pass.

Use one targeted tail batch:

```text
Batch 0: exact 96-row tail ownership
  Attach every remaining official row to XML, HTML, XPath, JSON, route/config,
  CSS, or other. Split formatter byte failures from parser/recovery failures.

Batch 1: XML/HTML formatter and recovery microgrammar
  Largest combined surface: 63 rows.
  Target XML recovery/error/encoding and HTML raw-text/optional-tag/void/comment
  byte grammar.

Batch 2: XPath predicate/function microgrammar
  Target deeper predicates, functions, union, namespaces/attributes if public,
  malformed selector diagnostics, no-match identity, and projection interaction.

Batch 3: tiny residuals
  JSON tree/indent, route/config precedence, CSS residual, and one-off other tail.
```

If Batch 1 or Batch 2 cannot be closed by public-reference probes without degenerating into fixture mimicry, escalate to source-tail / target-library compatibility with an explicit evidence boundary.

## 8. Generalized Lesson

The xq progression now supports a four-part adversarial pre-eval doctrine:

```text
1. Salience adversary:
   find omitted low-salience axes and role reversals.

2. Descent-completeness adversary:
   find active parents that were represented by examples rather than closure
   matrices.

3. Descent-yield accounting:
   decide whether another generic descent pass is still discovering meaningful
   structure or only terminal variants.

4. Targeted microgrammar/source-tail transition:
   once broad descent saturates, close known formatter/parser/selector tails
   with targeted matrices or justified source-tail analysis.
```

The safe abstraction is:

```text
Pre-eval adversarial passes are not one monolithic red-team step.
They are a staged circuit with a saturation point.
After salience and parent-descent wins are exhausted, the method should narrow
into microgrammar closure rather than keep asking for generic adversarial review.
```
