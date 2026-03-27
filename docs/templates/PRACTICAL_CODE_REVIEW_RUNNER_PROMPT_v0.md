# Practical Code Review Runner Prompt v0

Use this prompt when you want a resident agent to run the ADEU code-review method over
one frozen review world and return a comparable result.

Pair this prompt with:

- `docs/DRAFT_PRACTICAL_CODE_REVIEW_SIX_LANE_LOOP_v0.md`
- `docs/templates/PRACTICAL_CODE_REVIEW_SIX_LANE_RESULT_TEMPLATE_v0.json`

---

## Runner Prompt

You are running an ADEU practical code review, not a generic summary pass.

Follow the repo-local method in:

- `docs/DRAFT_PRACTICAL_CODE_REVIEW_SIX_LANE_LOOP_v0.md`

And return one filled result shaped exactly like:

- `docs/templates/PRACTICAL_CODE_REVIEW_SIX_LANE_RESULT_TEMPLATE_v0.json`

### Review Target

- review_id: `<fill>`
- task_label: `<fill>`
- target_scope: `<fill>`
- snapshot_stance: `committed_tree` unless explicitly told otherwise

### Frozen Review World

- authoritative intent sources:
  - `<fill>`
- authoritative observed sources:
  - `<fill>`
- accepted support docs:
  - `<fill>`
- explicit exclusions:
  - `<fill>`

### Hard Rules

- Do not use ambient intuition as authority.
- Do not silently blend intended and observed lanes.
- Do not infer intent from code in the observed lane.
- Do not import implementation accidents into architecture doctrine.
- Do not turn missing evidence, bounded search, or absent local proof into
  impossibility.
- Any significant second-order claim about necessity, impossibility, repo-wide
  doctrine, or architecture implication must either inherit explicit entitlement or
  re-enter the six-lane loop.
- Prefer blocked honesty over counterfeit certainty.

### Required Method

Execute the full six-lane review loop:

1. Frozen Repo World
2. Settlement / Entitlement
3. Intended Lane
4. Observed Lane
5. Alignment Lane
6. Final Answer

### Required Outputs

Return exactly two artifacts:

1. A concise human-readable review with these sections, in order:
   - Findings
   - Frozen Repo World
   - Settlement / Entitlement
   - Intended Interpretation
   - Observed Facts
   - Alignment Findings
   - Final Answer
   - Open Clarifications / Unblocking Artifacts

2. A fully filled JSON object conforming to:
   - `docs/templates/PRACTICAL_CODE_REVIEW_SIX_LANE_RESULT_TEMPLATE_v0.json`

### Findings Rules

- Order findings by severity.
- Each finding must include:
  - mismatch class
  - entitlement level
  - typed support refs
  - file/line refs when applicable
- No finding may be supported only by prose.
- Allowed final verdicts:
  - `aligned`
  - `misaligned`
  - `conditionally_aligned`
  - `intent_under_specified`
  - `implementation_evidence_under_specified`
  - `blocked`

### Comparison Goal

The goal is not to sound thorough.

The goal is to determine whether the implementation is aligned with the authoritative
intent under an explicitly settled interpretation, while preserving ambiguity,
blocking posture, and entitlement honestly.

---

## Suggested Invocation Pattern

Use the same frozen review world across models.

Only vary:

- `review_id`
- `model_id`

Keep constant:

- authoritative intent sources
- authoritative observed sources
- accepted support docs
- exclusions
- snapshot stance

That is what makes multi-model comparison meaningful.

---

## Ready-To-Paste Invocation: `v23` / Released `V41` Repo Review

Paste the block below directly to a resident model when you want a comparable review
run against the current released `V41` practical-analysis baseline on `main`.

```text
You are running an ADEU practical code review over the released V41 practical-analysis baseline on main.

Follow exactly:
- docs/DRAFT_PRACTICAL_CODE_REVIEW_SIX_LANE_LOOP_v0.md

Return one filled result shaped exactly like:
- docs/templates/PRACTICAL_CODE_REVIEW_SIX_LANE_RESULT_TEMPLATE_v0.json

Write exactly two output files under:
- artifacts/practical_code_review/v23/

Self-identification and file rules:
1. First choose your own short reviewer slug in lowercase snake_case or kebab-case.
2. Prefix all outputs with that slug.
3. Default output paths are:
   - artifacts/practical_code_review/v23/<reviewer_slug>__review.md
   - artifacts/practical_code_review/v23/<reviewer_slug>__result.json
4. If either of those files already exists, do not modify the existing files.
5. Instead choose a new unique prefix by modifying your slug, for example:
   - <reviewer_slug>_2
   - <reviewer_slug>_3
   - <reviewer_slug>_alt
6. Keep changing the prefix until both target files do not exist, then write only to the new pair.
7. The first line of your visible response in chat/terminal must be:
   - Reviewer: <final_output_prefix>
8. The first line of the markdown review must be:
   - Reviewer: <final_output_prefix>
9. In the JSON result, fill:
   - review_metadata.review_id = <final_output_prefix>__v23_review
   - review_metadata.model_id = your self-reported model name
   - review_metadata.task_label = v23_repo_alignment_review
   - review_metadata.target_scope = released_V41_practical_analysis_baseline_on_main
   - review_metadata.snapshot_stance = committed_tree

Frozen review world:
- authoritative intent sources:
  - docs/DRAFT_NEXT_ARC_OPTIONS_v23.md
  - docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md
  - docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md
- authoritative observed sources:
  - packages/adeu_architecture_ir/
  - packages/adeu_architecture_compiler/
  - apps/api/fixtures/architecture/
- accepted support docs:
  - docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md
  - docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md
- explicit exclusions:
  - artifacts/practical_code_review/
  - .git/
  - .venv/
  - node_modules/
  - external services, web lookups, Aristotle, and any non-repo oracle

Hard rules:
- Do not use ambient intuition as authority.
- Do not silently blend intended and observed lanes.
- Do not infer intent from code in the observed lane.
- Do not import implementation accidents into architecture doctrine.
- Do not treat tests as proof of global intent unless explicitly entitled.
- Do not turn missing evidence, bounded search, or absent local proof into impossibility.
- Any significant second-order claim about necessity, impossibility, repo-wide doctrine, or architecture implication must either inherit explicit entitlement or re-enter the six-lane loop.
- Prefer blocked honesty over counterfeit certainty.

Execute the full six-lane review loop:
1. Frozen Repo World
2. Settlement / Entitlement
3. Intended Lane
4. Observed Lane
5. Alignment Lane
6. Final Answer

Required markdown sections, in order:
1. Findings
2. Frozen Repo World
3. Settlement / Entitlement
4. Intended Interpretation
5. Observed Facts
6. Alignment Findings
7. Final Answer
8. Open Clarifications / Unblocking Artifacts

Findings rules:
- Order findings by severity.
- Each finding must include:
  - mismatch class
  - entitlement level
  - typed support refs
  - file/line refs when applicable
- No finding may be supported only by prose.

Allowed final verdicts:
- aligned
- misaligned
- conditionally_aligned
- intent_under_specified
- implementation_evidence_under_specified
- blocked

The goal is to determine whether the current implementation is aligned with the authoritative released V41 intent under an explicitly settled interpretation, while preserving ambiguity, blocking posture, and entitlement honestly.
```
