# V85 Declaration Probe 012 Assessment

Probe 012 tested the remand branch of the declaration harness.

Result: 4 of 4 intentionally malformed resident bodies were routed to `remand_required`.

The negative controls covered:

- fixed-field pollution: resident body included harness-owned `schema`;
- nearest-class repair: `CREATE ui.toast@v3` was incorrectly repaired to `CREATE ui.menu@v1`;
- malformed row shape: `uncertainty_rows` contained a string instead of row objects;
- closed-enum violation: competency `claim_status` used `passed_for_this_specimen`.

The important result is not just that errors were detected. The harness preserved them as remand reasons and did not silently repair the filing into apparent success.

Together with probe 011, the local circuit now has both branches:

```text
valid resident body
  -> harness-injected filing
  -> accepted_filing

invalid resident body
  -> harness-injected filing attempt
  -> remand_required with reasons
```

The next useful step is a correction round: feed the remand filing back to the resident model and test whether it can produce a corrected body without changing the semantic route.
