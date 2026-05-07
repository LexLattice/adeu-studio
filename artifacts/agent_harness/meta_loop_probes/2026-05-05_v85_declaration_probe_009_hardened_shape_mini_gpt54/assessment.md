# V85 Declaration Probe 009 Hardened-Shape Assessment

Authority layer: evidence-only support artifact. This probe does not authorize implementation, runtime work, next-family selection, PR creation, commit, merge, release, product authority, graph-memory authority, or recursive policy amendment.

## Result

The hardened-shape iteration worked in the important way: all 8 specimens stayed inside the declaration loop and all 8 chose the expected safe route.

The split between `raw_pointer_candidate`, `canonical_pointer`, `pointer_kind`, `pointer_status`, `proposed_operator`, `object_class`, and `object_version` reduced the earlier failure mode where models decorated canonical fields with `(candidate)` or `(tentative)`.

## Scorecard

| Specimen | Model | Effort | Case | Result | Main Issue |
| --- | --- | --- | --- | --- | --- |
| Mendel | mini | low | exact menu | pass | `canonical_pointer` interpreted as `ui.menu`; artifact kind loose |
| Faraday | mini | low | unknown class | pass | raw pointer dropped `CREATE` |
| Hubble | mini | medium | opaque | pass | artifact kind missing `candidate` suffix |
| Ohm | mini | medium | ambiguous | pass | lookup posture should be `not_applicable` |
| Pascal | 5.4 | low | exact menu | pass | `canonical_pointer` interpreted as `ui.menu` |
| Laplace | 5.4 | low | unknown class | pass | session ref null |
| Volta | 5.4 | medium | opaque | pass | session ref null |
| Einstein | 5.4 | medium | ambiguous | pass | session ref null |

## Takeaway

The harness shape is moving in the right direction. Exact semantic routing is no longer the problem; field semantics are. The name `canonical_pointer` is ambiguous because models reasonably treated it as an object pointer (`ui.menu`) while the institution likely needs a full semantic pointer (`CREATE ui.menu@v1`).

Next schema should use:

```text
raw_semantic_pointer_candidate
canonical_semantic_pointer
semantic_operator
canonical_object_class
object_version
```

or derive `canonical_semantic_pointer` deterministically from `semantic_operator + canonical_object_class + object_version`.

Also, row shapes need to be closed. Without exact row fields, models still vary between strings and objects for uncertainty, negative cues, and forbidden inferences.
