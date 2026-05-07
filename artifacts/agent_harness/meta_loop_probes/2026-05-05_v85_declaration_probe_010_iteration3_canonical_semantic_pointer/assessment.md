# V85 Declaration Probe 010 Assessment

Iteration 3 tested the schema repair from probe 009: full `canonical_semantic_pointer`, separate `canonical_object_class` / `object_version`, harness-supplied session refs, exact artifact kind, and row-object shapes.

Result: the semantic route is now strong. All 8 specimens parsed as JSON, preserved raw pointer evidence, preserved the canonical pointer contract, routed uncertainty, and stayed inside the non-authority boundary. Exact-menu cases used `canonical_semantic_pointer = "CREATE ui.menu@v1"` rather than collapsing the value to `ui.menu`.

Remaining failures are mostly artifact-shape discipline:

- 1 mini medium ambiguous specimen shortened `artifact_kind` to `candidate`.
- 2 mini specimens preserved a safe route but drifted `selection_status`.
- 6 specimens used plausible `resident_model_competency_claim_rows[].claim_status` values instead of the canonical `claimed_for_this_artifact`.

GPT-5.4 medium was clean on both medium specimens. GPT-5.4 low preserved the semantic route and only drifted on competency claim status. GPT-5.4-mini preserved the doctrine but still needs mechanical shape enforcement.

Practical read: prompt-only control is now enough for the resident model to obey the loop semantically, but not enough to guarantee strict filing validity. The next step should be a thin harness validator/injector: inject fixed fields, validate closed enums, remand malformed rows, and score route/shape/boundary separately.
