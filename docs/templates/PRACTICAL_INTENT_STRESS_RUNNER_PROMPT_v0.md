# Practical Intent Stress Runner Prompt v0

Use this prompt when you want a resident agent to run the ADEU intent-stress method
over one frozen intent world and return a comparable result.

Pair this prompt with:

- `docs/DRAFT_PRACTICAL_INTENT_STRESS_SIX_LANE_LOOP_v0.md`
- `docs/templates/PRACTICAL_INTENT_STRESS_SIX_LANE_RESULT_TEMPLATE_v0.json`

---

## Runner Prompt

You are running an ADEU practical intent stress review, not a generic doc summary pass.

Follow the repo-local method in:

- `docs/DRAFT_PRACTICAL_INTENT_STRESS_SIX_LANE_LOOP_v0.md`

And return one filled result shaped exactly like:

- `docs/templates/PRACTICAL_INTENT_STRESS_SIX_LANE_RESULT_TEMPLATE_v0.json`

### Review Target

- review_id: `<fill>`
- task_label: `<fill>`
- target_scope: `<fill>`
- snapshot_stance: `committed_tree` unless explicitly told otherwise

### Frozen Intent World

- authoritative intent sources:
  - `<fill>`
- accepted support docs:
  - `<fill>`
- explicit exclusions:
  - `<fill>`

### Hard Rules

- Do not use ambient intuition as authority.
- Do not silently import implementation reality as proof of intent unless the frozen
  world explicitly allows that.
- Do not silently narrow broad terms into stricter doctrine.
- Do not turn silence into prohibition.
- Do not turn bounded search or absent local proof into impossibility.
- Any significant second-order doctrine claim about necessity, exclusivity,
  impossibility, future widening, or repo-wide implication must either inherit
  explicit entitlement or re-enter the six-lane loop.
- Prefer blocked honesty over counterfeit doctrinal completeness.

### Required Method

Execute the full six-lane intent-stress loop:

1. Frozen Intent World
2. Settlement / Entitlement
3. Stated Doctrine Lane
4. Alternative Paths / Hidden Branches Lane
5. Pressure / Blindspot Lane
6. Final Answer

### Required Outputs

Return exactly two artifacts:

1. A concise human-readable review with these sections, in order:
   - Findings
   - Frozen Intent World
   - Settlement / Entitlement
   - Stated Doctrine
   - Alternative Paths / Hidden Branches
   - Pressure / Blindspot Findings
   - Final Answer
   - Open Clarifications / Doctrine Notes

2. A fully filled JSON object conforming to:
   - `docs/templates/PRACTICAL_INTENT_STRESS_SIX_LANE_RESULT_TEMPLATE_v0.json`

### Findings Rules

- Order findings by severity.
- Each finding must include:
  - finding class
  - entitlement level
  - typed support refs
  - file/line refs when applicable
- No finding may be supported only by prose.
- Allowed final verdicts:
  - `conceptually_well_bounded`
  - `blindspots_present`
  - `conditionally_well_bounded`
  - `intent_under_specified`
  - `blocked`

### Comparison Goal

The goal is not to sound comprehensive.

The goal is to surface implicit transitions, hidden assumptions, silent exclusions, and
unconsidered expansions that would otherwise escape implicit reasoning.

---

## Suggested Invocation Pattern

Use the same frozen intent world across models.

Only vary:

- `review_id`
- `model_id`

Keep constant:

- authoritative intent sources
- accepted support docs
- exclusions
- snapshot stance

That is what makes multi-model comparison meaningful.

---

## Ready-To-Paste Invocation: `v23` / Released `V41` Intent Stress Audit

Paste the block below directly to a resident model when you want a comparable
conceptual/logical stress review against the current released `V41` intent surface on
`main`.

```text
You are running an ADEU practical intent stress review over the released V41 intent surface on main.

Follow exactly:
- docs/DRAFT_PRACTICAL_INTENT_STRESS_SIX_LANE_LOOP_v0.md

Return one filled result shaped exactly like:
- docs/templates/PRACTICAL_INTENT_STRESS_SIX_LANE_RESULT_TEMPLATE_v0.json

Write exactly two output files under:
- artifacts/practical_intent_stress/v23/

Self-identification and file rules:
1. First choose your own short reviewer slug in lowercase snake_case or kebab-case.
2. Prefix all outputs with that slug.
3. Default output paths are:
   - artifacts/practical_intent_stress/v23/<reviewer_slug>__review.md
   - artifacts/practical_intent_stress/v23/<reviewer_slug>__result.json
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
   - review_metadata.review_id = <final_output_prefix>__v23_intent_stress
   - review_metadata.model_id = your self-reported model name
   - review_metadata.task_label = v23_intent_stress_review
   - review_metadata.target_scope = released_V41_intent_surface_on_main
   - review_metadata.snapshot_stance = committed_tree

Frozen intent world:
- authoritative intent sources:
  - docs/DRAFT_NEXT_ARC_OPTIONS_v23.md
  - docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md
  - docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md
- accepted support docs:
  - docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md
  - docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md
- explicit exclusions:
  - packages/
  - apps/api/fixtures/
  - artifacts/practical_intent_stress/
  - artifacts/practical_code_review/
  - .git/
  - .venv/
  - node_modules/
  - external services, web lookups, Aristotle, and any non-repo oracle

Hard rules:
- Do not use ambient intuition as authority.
- Do not silently import implementation reality as proof of intent.
- Do not silently narrow broad terms into stricter doctrine.
- Do not turn silence into prohibition.
- Do not turn bounded search, absent local proof, or absent explicit exclusion into impossibility.
- Any significant second-order doctrine claim about necessity, exclusivity, impossibility, future widening, or repo-wide implication must either inherit explicit entitlement or re-enter the six-lane loop.
- Prefer blocked honesty over counterfeit doctrinal completeness.

Execute the full six-lane intent-stress loop:
1. Frozen Intent World
2. Settlement / Entitlement
3. Stated Doctrine Lane
4. Alternative Paths / Hidden Branches Lane
5. Pressure / Blindspot Lane
6. Final Answer

Required markdown sections, in order:
1. Findings
2. Frozen Intent World
3. Settlement / Entitlement
4. Stated Doctrine
5. Alternative Paths / Hidden Branches
6. Pressure / Blindspot Findings
7. Final Answer
8. Open Clarifications / Doctrine Notes

Findings rules:
- Order findings by severity.
- Each finding must include:
  - finding class
  - entitlement level
  - typed support refs
  - file/line refs when applicable
- No finding may be supported only by prose.

Allowed final verdicts:
- conceptually_well_bounded
- blindspots_present
- conditionally_well_bounded
- intent_under_specified
- blocked

The goal is to surface implicit transitions, hidden assumptions, silent exclusions, and unconsidered expansions that would otherwise escape implicit reasoning.
```
