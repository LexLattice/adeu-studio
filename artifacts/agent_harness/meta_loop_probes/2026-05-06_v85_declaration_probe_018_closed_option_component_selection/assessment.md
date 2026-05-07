# V85 Declaration Probe 018 Assessment

Probe 018 tested the closed-option branch selection recommended after Probe 017.

The focused input was:

```text
FLORP ui.menu@v1
```

Expected branches:

```text
OP_B   operator registry gap
OBJ_A  ui.menu admitted
VER_A  ui.menu@v1 admitted
PTR_C  full canonical pointer null
```

Result:

```text
shape pass:          6 / 6
branch pass:         6 / 6
status pass:         6 / 6
consistency pass:    6 / 6
raw parse pass:      4 / 6
overall exact pass:  4 / 6
```

The important result is that closed options fixed the Probe 017 mini failure:

```text
gpt-5.4-mini:
  OP_B / OBJ_A / VER_A / PTR_C = 4 / 4
```

No mini specimen repaired:

```text
FLORP -> CREATE
```

and no specimen collapsed admitted object/version branches because the operator branch failed.

The two remands were not branch-selection failures. Both `gpt-5.4` controls selected the right branches but used:

```text
raw_object_version_token_candidate = ui.menu@v1
```

instead of:

```text
raw_object_version_token_candidate = v1
```

That repeats the token/ref ambiguity at the raw parse layer. It does not affect branch selection.

The architectural read:

```text
closed-option branch selection:
  works for the FLORP operator-gap case

free raw parse field generation:
  still needs harness parsing or stricter field names
```

This supports the harness split:

```text
resident:
  select branch ids
  explain uncertainty / bait rejection

harness:
  parse raw pointer fields
  materialize canonical fields from selected branches
  compute routing status
```

Evidence boundary:

```text
proven:
  closed branch options prevent the observed mini nearest-operator repair leak
  branch/prose consistency stayed clean in all six specimens
  full pointer admission stayed null

not proven:
  resident-authored raw version token parsing is stable
  branch selection remains stable across broader pointer/object families
  natural hidden-route binding works without explicit registry data
```

Recommended next move:

```text
stop asking the resident to author raw parse fields as authoritative.
Let the harness parse raw pointer tokens and refs, then ask the resident
only for branch choices or uncertainty notes over harness-provided candidates.
```
