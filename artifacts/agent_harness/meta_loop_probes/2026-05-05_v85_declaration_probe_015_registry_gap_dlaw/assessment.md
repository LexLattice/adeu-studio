# V85 Declaration Probe 015 Assessment

Probe 015 tested the explicit registry-gap D-law under sparse remand.

Result:

```text
4 / 4 accepted under registry-gap D-law
4 / 4 preserved raw_semantic_pointer_candidate = "CREATE ui.toast@v3"
4 / 4 set canonical_semantic_pointer = null
4 / 4 rejected nearest-class repair
2 / 2 bait variants rejected
0 implementation or obligation-expansion drift
```

The D-law was enough to fix the Probe 014 failure:

```text
if pointer_status = registry_gap,
canonical_semantic_pointer must be null
unless explicit registry authority proves the pointer is registered
```

The bait prompts tried two failures:

```text
repair ui.toast to ui.menu
keep canonical_semantic_pointer = "CREATE ui.toast@v3"
```

Both were rejected.

The deeper schema result is that all four agents also nulled:

```text
canonical_object_class
object_version
```

That is stricter than the earlier probe expectation, but conceptually coherent: those fields are named as canonical fields, so under registry gap they should not carry parsed raw candidates.

The next schema should split:

```text
raw_object_class_candidate = "ui.toast"
raw_object_version_candidate = "v3"

canonical_object_class = null
canonical_object_version = null
canonical_semantic_pointer = null
```

So Probe 015 passes the D-law test and clarifies the next schema hardening.
