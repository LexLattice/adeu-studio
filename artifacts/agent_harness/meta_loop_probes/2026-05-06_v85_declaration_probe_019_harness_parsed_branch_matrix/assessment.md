# V85 Declaration Probe 019 Assessment

Probe 019 tested the Probe 018 recommendation directly: remove resident-authored raw parsing and ask the resident only for opaque closed branch selection over harness-parsed candidates.

Matrix:

```text
CREATE ui.menu@v1   -> operator admit, object admit, version admit, full pointer admit
CREATE ui.toast@v3  -> operator admit, object gap, version gap, full pointer null
FLORP ui.menu@v1    -> operator gap, object admit, version admit, full pointer null
CREATE ui.menu@v99  -> operator admit, object admit, version gap, full pointer null
FLORP ui.toast@v99  -> operator gap, object gap, version gap, full pointer null
```

Result:

```text
shape pass:                10 / 10
branch pass:               10 / 10
consistency pass:          10 / 10
full pointer policy pass:  10 / 10
overall pass:              10 / 10
```

Model split:

```text
gpt-5.4-mini medium:  5 / 5
gpt-5.4 medium:       5 / 5
```

The important finding is that the resident models were reliable as branch selectors once parsing and canonical materialization were taken out of their hands. The prior failure modes did not recur:

```text
Probe 017:
  mini nearest-repaired FLORP -> CREATE in a canonical component field

Probe 018:
  branch selection succeeded, but resident-authored raw version token parsing drifted

Probe 019:
  harness parsed raw fields
  resident selected branches only
  all five cases passed for both models
```

The core safety property held:

```text
canonical full pointer admission occurs only when:
  operator admission passes
  object class admission passes
  object version ref admission passes
```

No specimen repaired:

```text
FLORP -> CREATE
ui.toast -> ui.menu
ui.menu@v99 -> ui.menu@v1
FLORP ui.toast@v99 -> CREATE ui.menu@v1
```

The architectural read is now firmer:

```text
harness:
  parse raw pointer fields
  provide closed semantic branch choices
  materialize canonical fields from selected branch ids
  compute routing status

resident:
  select closed branch ids
  explain bait rejection and uncertainty
  stop after branch selection
```

Evidence boundary:

```text
proven:
  harness-parsed closed branch selection works across the five-case matrix
  gpt-5.4-mini is adequate for this bounded resident branch-selection role
  full pointer safety and component independence hold under explicit D-law

not proven:
  natural hidden-route semantic binding
  large-registry generalization
  branch selection without explicit D-law
  resident-owned canonical parsing or materialization authority
```

Recommended next probe:

```text
Probe 020 should either:
  use a larger mixed registry with multiple valid operators/classes/version refs,
  or hide semantic labels behind branch ids and evidence rows more aggressively.

The goal is to test whether the resident follows registry evidence and D-law
when there are multiple plausible valid admissions, not only one registered path.
```
