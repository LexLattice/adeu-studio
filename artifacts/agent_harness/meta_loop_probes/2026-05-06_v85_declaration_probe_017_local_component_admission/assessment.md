# V85 Declaration Probe 017 Assessment

Probe 017 tested the refined component-admission law from Probe 016:

```text
operator token -> canonical_operator

object class token -> canonical_object_class
        |
        +-- object-bound version ref -> canonical_object_version_ref

all admitted -> canonical_semantic_pointer
```

The probe also split version fields:

```text
raw_object_version_token_candidate
raw_object_version_ref_candidate
canonical_object_version_ref
```

and required closed status values for:

```text
pointer_kind
component_admission_status
canonical_lookup_status
selection_status
stop_posture
```

Result:

```text
strict body shape pass:       8 / 8
version token/ref shape pass: 8 / 8
full pointer safety pass:     8 / 8
component value pass:         7 / 8
routing status pass:          7 / 8
overall exact pass:           6 / 8
```

The main improvement from Probe 016 held:

```text
CREATE ui.toast@v3
```

Both models preserved:

```text
canonical_operator = CREATE
canonical_object_class = null
canonical_object_version_ref = null
canonical_semantic_pointer = null
```

So the explicit local component D-law fixed the earlier safe over-blocking case.

The remaining true component failure was mini on:

```text
FLORP ui.menu@v1
```

It preserved the raw operator:

```text
raw_operator_candidate = FLORP
```

but wrongly emitted:

```text
canonical_operator = CREATE
```

while also claiming `operator_registry_gap`. That is a nearest-operator repair leak at the component level. It did not admit the full canonical pointer, so the global safety law held, but the local canonical component was wrong.

The second remand was status-only:

```text
CREATE ui.menu@v99
```

The mini specimen had the right component values, but used:

```text
canonical_lookup_status = object_class_version_registry_gap
```

instead of the sharper:

```text
canonical_lookup_status = object_version_registry_gap
```

That shows why routing status should probably be harness-computed even when the model body shape is closed.

Model posture:

```text
gpt-5.4:
  4 / 4 exact pass

gpt-5.4-mini:
  2 / 4 exact pass
  3 / 4 component value pass
  3 / 4 routing status pass
```

The evidence boundary is now:

```text
proven:
  split version token/ref shape is stable in this prompt form
  explicit D-law fixes operator over-blocking for CREATE ui.toast@v3
  full pointer safety remains stable
  gpt-5.4 handles this component graph cleanly

not proven:
  gpt-5.4-mini can reliably avoid nearest-operator component repair
  model-authored routing status is safe enough to drive transitions
  natural hidden-route binding works without explicit registry data
```

Recommended next step:

```text
move canonical component admission and routing statuses into harness-computed fields,
or run a focused remand probe for the mini FLORP case:

  invalid canonical_operator = CREATE
  remand reason = canonical_operator_component_mismatch
  D-law = unknown operator must keep canonical_operator null
```
