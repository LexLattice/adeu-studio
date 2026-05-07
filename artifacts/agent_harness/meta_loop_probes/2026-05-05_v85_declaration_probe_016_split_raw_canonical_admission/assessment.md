# V85 Declaration Probe 016 Assessment

Probe 016 tested the split raw/canonical admission schema suggested by Probe 015.

The tested registry was intentionally tiny:

```text
registered operator: CREATE
registered object class: ui.menu
registered object version: ui.menu@v1
```

The body shape separated:

```text
raw_semantic_pointer_candidate
raw_operator_candidate
raw_object_class_candidate
raw_object_version_candidate

canonical_semantic_pointer
canonical_operator
canonical_object_class
canonical_object_version
```

Result:

```text
strict body shape pass: 8 / 8
component admission pass: 7 / 8
canonical full-pointer policy pass: 8 / 8
nearest repair / raw promotion leak: 0
raw object-version format split:
  token-only: 3 / 8
  object-bound: 5 / 8
```

The good result is that every specimen preserved the raw pointer and kept the full canonical pointer null unless all components were registry-backed.

The one component-admission miss was useful:

```text
CREATE ui.toast@v3
```

One `gpt-5.4-mini` specimen correctly blocked `ui.toast` and `v3`, but also nulled:

```text
canonical_operator
```

The expected split behavior is:

```text
canonical_operator = CREATE
canonical_object_class = null
canonical_object_version = null
canonical_semantic_pointer = null
```

So the model preserved the fail-closed full-pointer rule, but did not fully preserve independent component admission.

This is the new D-law to make explicit:

```text
canonical component admission is independent.
Blocking one component must not erase other registry-backed components.
Full pointer admission still requires all components.
```

The second schema result is that `raw_object_version_candidate` remains ambiguous. Some specimens emitted:

```text
v3
v99
```

while others emitted:

```text
ui.toast@v3
ui.menu@v99
```

That means the next schema should split:

```text
raw_object_version_token_candidate
raw_object_version_ref_candidate
canonical_object_version_ref
```

Probe 016 therefore supports the raw/canonical split, but it also shows that component admission needs its own explicit rule and version candidate fields need tighter names.

Evidence boundary:

```text
proven:
  resident models can use split raw/canonical fields
  full canonical pointer remains null unless all components are admitted
  nearest-class, nearest-operator, and latest-version repairs can be blocked
  strict filing shape is stable for this split schema

not yet proven:
  low-end residents reliably preserve independent component admission without a stronger D-law
  version-token vs object-bound-version naming is stable
  natural hidden-route binding works without explicit registry data in prompt
```

Recommended next probe:

```text
Probe 017:
  same split schema
  explicit independent-component D-law
  explicit version-token/ref split
  include bait that says "if object is blocked, null the operator too"
```
