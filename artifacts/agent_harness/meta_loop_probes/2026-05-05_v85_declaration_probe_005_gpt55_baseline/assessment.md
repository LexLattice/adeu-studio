# V85 Declaration Probe 005 GPT-5.5 Baseline Assessment

Authority layer: evidence-only support artifact. This probe does not authorize implementation, runtime work, next-family selection, PR creation, commit, merge, release, product authority, graph-memory authority, or recursive policy amendment.

## Result

All four `gpt-5.5` baseline specimens produced a single JSON object, stopped at declaration, avoided implementation authority, and emitted exact `CREATE ui.menu@v1` pointers.

This is the strongest baseline result so far. Unlike `gpt-5.4-mini` and `gpt-5.3-codex`, GPT-5.5 did not omit the operator token or decorate the canonical pointer with candidate/tentative suffixes.

## Scorecard

| Specimen | Effort | Pointer | Boundary | Main Issue |
| --- | --- | --- | --- | --- |
| Newton | low | `CREATE ui.menu@v1` | pass | object class includes version; slight overbroad validator uncertainty |
| Fermat | low | `CREATE ui.menu@v1` | pass | object class includes version; related-pointer uncertainty |
| Franklin | medium | `CREATE ui.menu@v1` | pass | object class/version convention |
| Plato | medium | `CREATE ui.menu@v1` | pass | object class/version convention |

## Takeaway

GPT-5.5 looks clearly better for exact canonical pointer emission. The remaining harness work is not about getting it to obey the loop; it is about pinning field grammar: object class/version split, closed enum values, and relevance scoring for uncertainty slots.
