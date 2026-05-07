# V85 Declaration Probe 013 Assessment

Probe 013 tested the correction branch:

```text
invalid resident body
  -> harness remand_required with reasons
  -> same resident agent receives remand
  -> corrected resident body
  -> accepted_filing
```

Result: 4 of 4 correction loops passed.

The four surgical cases were:

- fixed-field pollution: removed harness-owned `schema`;
- nearest-class repair: restored `CREATE ui.toast@v3` to registry-gap posture instead of `CREATE ui.menu@v1`;
- malformed uncertainty row: replaced a string item with a valid uncertainty row object;
- bad competency claim status: changed `passed_for_this_specimen` to `claimed_for_this_artifact`.

The key semantic result is the `ui.toast@v3` correction. The model preserved:

```text
raw_semantic_pointer_candidate = "CREATE ui.toast@v3"
canonical_semantic_pointer = null
pointer_status = "registry_gap"
canonical_object_class = "ui.toast"
object_version = "v3"
```

It did not repair the unknown class into `ui.menu@v1`.

This validates the practical circuit:

```text
resident model:
  emits bounded semantic body
  receives remand
  corrects local filing error
  preserves route

harness:
  owns filing identity
  validates body and assembled artifact
  remands invalid filings
  accepts corrected filings
```

The evidence should still be stated narrowly: this proves harnessable filing, remand, and correction for declared routes. It does not yet prove broad autonomous semantic binding at scale.
