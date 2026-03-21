# DRAFT Synthetic Structure Drift v0

## Purpose

This note turns the colloquial observation of an "AI accent" in code into a
repo-native ADEU object.

The raw phrase is useful as intake language, but it is not precise enough to become
policy. The repo should not govern against "AI-ness." It should govern against
specific structural drifts that degrade correctness, maintainability, reviewability,
or truthful communication.

The canonical object proposed here is:

- `synthetic_structure_drift`

This object is a bounded family of structurally detectable patterns that often appear
when code is over-produced, over-explained, over-defended, or mechanically normalized
without enough pressure from the actual problem.

## Intake Principle

Treat the raw symptom list as:

- a useful corpus of candidate smells;
- not a frozen truth set;
- not a style war;
- not an authorship detector.

The governing question is not:

- "does this look AI-generated?"

The governing question is:

- "does this introduce unjustified structure, fake safety, semantic blur, or
  communication without load?"

## Canonical Drift Families

### 1. Pseudo-Safety Inflation

Patterns:

- edge-case handling for states that cannot occur
- `nil`/`None` checks on values that cannot be absent
- `try/catch` or equivalent around code that cannot throw
- empty-list preguards before loops that already handle emptiness
- validating the same invariant multiple times in the same call path

Risk:

- fake robustness;
- obscured true trust boundaries;
- inflated control flow;
- harder review of the actual failure model.

### 2. Error-Opacity Drift

Patterns:

- catch blocks swallowing errors silently
- error messages that describe the code instead of the violated condition or problem

Risk:

- degraded observability;
- poor failure triage;
- false success posture.

### 3. Abstraction Without Pressure

Patterns:

- breaking trivial inline logic into helpers that will not be reused
- boolean conditionals that return `true`/`false` explicitly instead of the condition
- enumerating when direct indexing or direct iteration shape is the real operation

Risk:

- lower semantic density;
- fragmented reasoning;
- ceremony without reuse.

### 4. Mechanical Regularity Drift

Patterns:

- branches that mirror each other too perfectly in length and phrasing
- code that enforces one sterile style in all contexts rather than adapting to local
  problem shape

Risk:

- unnatural control-flow shaping;
- reduced locality;
- suspiciously generic transformations that do not fit domain pressure.

### 5. Naming Semantics Drift

Patterns:

- embedding type information in the variable name itself
- abstractly generic names that erase domain role

Risk:

- lower domain legibility;
- naming that follows template convention rather than real semantic role.

### 6. Communication Without Load

Patterns:

- comments that narrate what obvious code already shows
- bullet recaps in prose of what was just done
- hedging language in comments without corresponding epistemic uncertainty
- changelog-style commit messages that enumerate touched files rather than intent

Risk:

- more text with less semantic value;
- review surface inflation;
- lowered signal-to-noise ratio.

## ODEU Abstraction

### O: Ontology

Each detected pattern should be modeled as one of:

- `pseudo_safety_inflation`
- `error_opacity_drift`
- `abstraction_without_pressure`
- `mechanical_regularity_drift`
- `naming_semantics_drift`
- `communication_without_load`

The governed object is not "AI code." The governed object is a typed drift family.

### E: Epistemics

Evidence modes should be explicit:

- `ast_shape`
- `control_flow_shape`
- `exception_flow_shape`
- `nullability_or_presence_inference`
- `duplicate_invariant_path`
- `lexical_naming_pattern`
- `comment_text_pattern`
- `error_text_pattern`
- `commit_text_pattern`
- `review_only_human_judgment`

Each rule should carry:

- `evidence_mode`
- `false_positive_risk`
- `required_context_scope`
- `counterexample_policy`

### D: Deontics

Rules should not all have the same force.

Allowed policy grades:

- `forbid`
- `discourage`
- `allow_with_justification`
- `review_only`
- `safe_autofix`

### U: Utility

The point of the module is:

- less fake safety
- less redundant structure
- higher semantic density
- cleaner trust boundaries
- lower reviewer load
- more truthful code and commit communication

## Automation Tiers

### Tier 1: Safe Autofix

Examples:

- boolean-return ceremony
- some trivial empty-list preguards
- some narration-only comments

Rule:

- allowed only when behavior preservation is near-certain.

### Tier 2: Deterministic Warning

Examples:

- impossible `None` checks where type and call-path evidence are strong
- duplicate invariant validation on one call path
- dead `try/catch`
- swallowed errors

Rule:

- emit structured findings;
- fail only for a bounded high-confidence subset.

### Tier 3: Heuristic Review

Examples:

- generic naming
- mirrored branch symmetry
- sterile over-regular style
- hedging comments
- prose recap bullets

Rule:

- advisory only;
- never auto-fix blindly.

### Tier 4: Human-Only

Examples:

- "personality" or idiom judgments
- context-specific stylistic exceptions

Rule:

- preserve as human review space.

## Proposed Meta-Module

The proposed bounded module family is:

- `synthetic_structure_conformance`

Planned artifacts:

- `synthetic_structure_rule_registry@1`
- `synthetic_structure_observation_packet@1`
- `synthetic_structure_conformance_report@1`
- `synthetic_structure_fix_plan@1`

Recommended registry fields:

- `rule_id`
- `drift_family`
- `raw_pattern_examples`
- `evidence_mode`
- `automation_tier`
- `policy_grade`
- `false_positive_risk`
- `expected_utility_gain`
- `safe_autofix_available`
- `counterexample_notes`
- `forward_agent_policy`
- `post_optimizer_policy`

Recommended report fields:

- `subject_ref`
- `subject_kind`
- `observation_count`
- `findings`
- `safe_autofix_candidates`
- `high_confidence_blockers`
- `review_only_findings`
- `overall_drift_posture`

## Embedding In Practice

### A. Forward Coding Agent

The forward coding agent should adopt preventive rules:

- do not add guards without a reachable failure model
- do not duplicate invariant checks inside one call path without a boundary reason
- do not extract helpers unless reuse or real complexity reduction exists
- do not narrate obvious code in comments
- do not encode type where domain role should carry the name
- do not swallow errors
- make error messages describe the actual problem and subject
- use commit messages for intent, not touched-file recaps

### B. Post-Code Optimizer Agent

The post-code optimizer should adopt corrective rules:

- auto-fix Tier 1 only
- emit deterministic findings for Tier 2
- keep Tier 3 as advisory review findings
- preserve behavior over cleanliness
- treat swallowed errors and false trust-boundary guards as highest priority
- emit a fix plan rather than a blind rewrite when confidence is mixed

## Relation To V39-A

`V39-A` already established a retrospective external-contribution conformance lane.

This draft is a natural follow-on because it generalizes one layer of that work:

- from "is this imported PR aligned to repo structure?"
- toward "what typed structural drifts should any module or diff be checked against?"

The first bounded use should remain narrow:

- use the existing poetry utility reference as one seed example,
- but do not let the new module collapse into a generic all-style lint engine.

## Recommended Slice Sequence

- `V39-B`: rule taxonomy and canonical registry
- `V39-C`: observation packet, deterministic detectors, and conformance report
- `V39-D`: forward-agent and post-optimizer policy projection, plus bounded autofix
  planning

This keeps the family inside the broader `V39` module-conformance terrain instead of
spawning a disconnected arc for every adjacent structural-governance concern.
