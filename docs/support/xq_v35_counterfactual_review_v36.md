# XQ v35 Counterfactual Review v36

Authority layer: support / schema-integration review note.

Source reviewed:

```text
.codex/review-shell/chatgpt-downloads/xq_v35_counterfactual_review_v36.md
```

This support note records the reusable conclusions from the GPTPro review of
the `sibprogrammer__xq.b89f681` v35 counterfactual run.

## Result Summary

The v35 counterfactual run was bounded to pre-official-eval evidence:

```text
allowed:
  visible README / man / LICENSE
  public reference executable observations
  Phase 1-3 artifacts
  blind adversarial checkpoint reports
  v35 meta-program patch

forbidden:
  first official eval failure summary
  official eval JSON
  upstream source
  hidden tests
  post-eval repair artifacts
```

The enhanced manifest had:

```text
176 total probes
164 public scout observations promoted into the manifest
12 salience-breaker probes
```

Probe progression:

```text
reference_v35_sanity: 176 / 176
candidate_v35_baseline: 159 / 176
candidate_v35_iter1:    173 / 176
candidate_v35_iter2:    176 / 176
```

Official movement:

```text
v32 first pass:
  score: 67
  raw:   610 passed / 267 failed / 2 skipped / 879 total

v35 counterfactual:
  score: 76
  raw:   684 passed / 193 failed / 2 skipped / 879 total
```

Delta:

```text
old failed -> new passed: 74
old passed -> new failed: 0
```

Interpretation:

```text
The v35 adversarial pre-eval gates are validated as first-pass improvement
gates. They are not validated as full coverage or gold-readiness gates.
```

## What v35 Proved

The v35 run proved that several missed official rows were discoverable before
official eval through public-reference and adversarial pre-eval work:

```text
ambient $HOME/.xq config
raw JSON as input / format role reversal
HTML comment serialization
JSON HTML escaping behavior
in-place color suppression
selected XPath representative gaps
```

The zero-regression result matters: the added gates improved behavior without
trading away previously green official rows.

## What v35 Did Not Prove

The remaining tail was still substantial:

```text
xpath_extraction_engine:      81
html_format_exactness:        44
xml_format_exactness:         40
json_input_format_convert:    18
io_modes_routes:               6
other:                         2
config_file:                   1
e2e_golden:                    1
```

This pressure is deeper than salience-breaking. It points to sublanguage and
formatter closure:

```text
XPath functions / predicates / axes
XML physical grammar and byte formatting tails
HTML recovery / formatter exactness
JSON conversion edge cases
narrow IO route tails
```

## Schema Lesson

Split:

```text
salience-breaking probes
  ambient, role-reversed, directional, mutating, convention-based, or
  terminal-mediated axes that ordinary scout may underweight.

sublanguage closure probes
  depth matrices for active grammars, renderers, selectors, transforms,
  recovery laws, and route families.
```

The v36 meta-program revision should therefore add:

```text
PRE_EVAL_SALIENCE_BREAKER_GATE
FORMAT_ROLE_REVERSAL_PROBE
AMBIENT_CONFIG_CONVENTION_PROBE
SCOUT_OBSERVATION_PROMOTION_LEDGER
ROW_LEVEL_DELTA_ATTRIBUTION_LEDGER
SUBLANGUAGE_CLOSURE_ESCALATION_GATE
```

## Next XQ Sequence

The review recommends no immediate code patch. First:

```text
Batch 0:
  row-level delta attribution for the 74 wins;
  row-level ownership for the 193 remaining failures;
  split salience-breaker vs scout-promotion contribution.
```

Then:

```text
Batch 1: XPath selector/expression sublanguage matrix.
Batch 2: XML physical grammar / formatter / recovery matrix.
Batch 3: HTML formatter / recovery matrix.
Batch 4: JSON directionality / tree-preservation tail and IO route closure.
```
