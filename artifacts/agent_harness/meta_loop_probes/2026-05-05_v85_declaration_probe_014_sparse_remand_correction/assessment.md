# V85 Declaration Probe 014 Assessment

Probe 014 tested sparse remand correction:

```text
original invalid body
  + remand reasons
  + schema contract
  -> corrected body
```

Unlike probe 013, the sparse remand did not restate the full correct route.

Result:

```text
4 / 4 initial invalid bodies remanded
3 / 4 corrected bodies accepted
1 / 4 corrected bodies still remanded
0 silent repairs
0 implementation or obligation expansion drift
```

The accepted corrections were:

- fixed-field pollution: removed harness-owned `schema`;
- malformed uncertainty row: converted the string item to a valid row object;
- bad competency claim status: changed `passed_for_this_specimen` to `claimed_for_this_artifact`.

The failed correction was the hard case:

```text
raw_semantic_pointer_candidate = "CREATE ui.toast@v3"
```

The model corrected object class and version:

```text
canonical_object_class = "ui.toast"
object_version = "v3"
```

But it incorrectly emitted:

```text
canonical_semantic_pointer = "CREATE ui.toast@v3"
```

The required registry-gap posture remains:

```text
canonical_semantic_pointer = null
pointer_status = "registry_gap"
```

So the precise read is:

```text
semantic task preserved
invalid nearest-class repair removed
canonical route not fully restored
```

This is useful evidence. Sparse remand can fix local filing defects, but unknown-class correction needs an explicit D-law:

```text
registry_gap => canonical_semantic_pointer must be null
unless an explicit registry authority row exists
```

Probe 014 also applied the new filing rule:

```text
detail_notes: array<string>
```

All final bodies obeyed that policy.
