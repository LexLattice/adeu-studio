# Draft ADEU Typed Adjudication Product Wedge v0

Status: support-layer product brainstorm.

Authority layer: support.

This note records a product-facing interpretation of the ARC-series roadmap. It does
not authorize product implementation, schema release, runtime behavior, marketing
claims, or roadmap reordering by itself.

## Product Thesis

The commercially legible product is not "better notes", "AI summary", or generic model
benchmarking. It is typed adjudication as a service for domains where vibe analysis
currently masquerades as judgment.

Core shape:

```text
raw repo / PR / design fork / research artifact / model outputs
  -> typed conceptual audit
  -> ODEU decomposition
  -> evidence and tool-applicability report
  -> authority-risk map
  -> edge / weak-point ledger
  -> implementation-safe next slice
  -> machine-followable report artifact
```

The wedge is that most informal reviews collapse:

- what exists;
- what is claimed;
- what is proven;
- what is allowed;
- what is useful next.

ODEU forces those lanes apart.

## Product Names

Working names:

- `ADEU Eval Forge`
- `ODEU Model Comparator`
- `ADEU Audit Artifact`
- `Typed Adjudication Workbench`

The clearest external phrase is:

```text
Bring your prompt and repo. Get a typed model-output A/B report instead of vibes.
```

## Core Artifact Bundle

Potential product bundle:

- `odeu_conceptual_analysis@1`
- `model_output_comparison_case@1`
- `tool_applicability_report@1`
- `authority_boundary_map@1`
- `edge_seam_register@1`
- `weak_point_ledger@1`
- `next_slice_recommendation@1`
- `synthesis_candidate@1`

The human-readable report tells the operator what happened. The JSON artifacts give the
next agent a typed substrate.

## Use-Case Variants

- repo-refactor audit;
- PR / design-fork conceptual diff;
- architecture-risk audit;
- agent-output adjudication;
- research-paper assimilation audit;
- edge / failure-mode detection;
- benchmark-result authority audit;
- model-output A/B/C comparison on a user's own repo or corpus.

## Resident Adjudicator Roles

A productized evaluation ensemble could expose governed roles:

- cartographer model: maps structure and dependency geometry;
- empiricist model: checks tools, evidence, scripts, and failure modes;
- deontic auditor model: detects authority laundering and boundary violations;
- utility planner model: selects implementation-safe next move;
- synthesis adjudicator model: merges outputs into typed report.

These roles must be treated as bounded evaluators, not sources of native authority.

## Roadmap Integration

The product should not be inserted as an early shortcut before the recursive governance
substrate. It is a `V74`-facing projection that depends on earlier families.

| Family | Product contribution |
|---|---|
| `V68` | knows the target repo/corpus, arc lineage, schema surfaces, branch posture, and evidence locations |
| `V69` | admits prompt, repo/corpus, model outputs, resident role assignments, and internally generated candidate types |
| `V70` | produces ODEU comparison, evidence/tool applicability, authority-risk, weak-point, and edge-seam judgments |
| `V71` | keeps human ratification, model-role settlement, and synthesis acceptance explicit |
| `V72` | turns recommendations into bounded implementation-safe next slices without confusing them with commit/release authority |
| `V73` | records outcome, model/corpus performance, prompt refinements, and recurring weakness patterns |
| `V74` | becomes the operator-facing product workbench: typed audit case view, comparison report, and decision projection |
| `V75` | optionally widens to governed multi-model / multi-agent reruns and refinement loops |

`V43` and `V46` are adjacent but not sufficient:

- `V46` benchmark comparison helps, but public benchmark posture is not enough for
  user-specific repo authority boundaries;
- `V43` external contest participation helps if the product targets external challenge
  worlds, but the product wedge is broader than contests.

## Killer Demo

Input:

```text
same user prompt
  + same repo / corpus substrate
  + two or more plausible strong model outputs
```

Output:

```text
typed ODEU comparison artifact
  + evidence / applicability report
  + authority-risk map
  + contradiction and complementarity map
  + failure-mode ledger
  + synthesis candidate
  + optional rerun prompt generated from discovered weaknesses
```

The demo should show:

- Model A preserved authority boundaries better;
- Model B found more implementation seams;
- Model A overfit conceptual completeness;
- Model B missed epistemic tool applicability;
- the synthesis should import specific contributions from each model;
- the next action is implementation-safe and bounded.

## Boundary

This product cannot claim:

- model truth in general;
- benchmark supremacy;
- autonomous adoption;
- commit/merge/release authority;
- hidden schema promotion;
- proof that a generated audit is complete.

It can claim, once the relevant families exist:

- fixed prompt/task input;
- fixed repo/corpus substrate;
- explicit comparison schema;
- typed ODEU axes;
- recorded evidence;
- reproducible report artifact;
- model/posture provenance;
- downstream recommendation.

## Immediate Use In The Roadmap

This note should inform `V74` planning and the `V68` cartography requirements. The
current support prototype can remain manual and docs-based. A released product surface
should wait until the candidate intake, evidence classification, ratification,
integration, and outcome-review lanes are typed enough to prevent authority laundering.
