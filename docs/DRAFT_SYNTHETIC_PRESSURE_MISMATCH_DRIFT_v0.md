# DRAFT Synthetic Pressure-Mismatch Drift v0

## Purpose

This note turns the colloquial observation of an "AI accent" in code into a
repo-native ADEU object.

The raw phrase is useful as intake language, but it is not precise enough to become
policy. The repo should not govern against "AI-ness." It should govern against
specific structural drifts that degrade correctness, maintainability, reviewability,
or truthful communication.

The strongest commonality behind the symptom list is not authorship. It is pressure
mismatch: the artifact is shaped as if more caution, more abstraction, more
communication, or more completion were required than the local problem actually
pressures.

The canonical object proposed here is:

- `synthetic_pressure_mismatch_drift`

Retired alias:

- `synthetic_structure_drift` should now be treated as a planning-history alias only,
  not the preferred canonical name.

## Intake Principle

Treat the raw symptom list as:

- a symptom corpus;
- not a frozen truth set;
- not a style war;
- not an authorship detector.

The governing question is not:

- "does this look AI-generated?"

The governing question is:

- "does this introduce unjustified structure, fake safety, failure-model blur,
  communication without load, or meta-artifact residue relative to the local problem
  pressure?"

## Hidden Commonality

The relevant defects here are often not:

- invalid syntax;
- broken typing;
- obviously wrong semantics.

The relevant defects are often higher-order:

- semantically admissible but poorly pressured structure;
- inflated or distorted local state models;
- linguistic fluency with low semantic load;
- artifact regularity that does not arise from the problem itself.

This is why the module should not be framed as anti-AI aesthetics. It should be
framed as anti-noise, anti-fake-safety, anti-unpressured ceremony, and anti-residue
communication.

## Canonical Drift Families

### 1. State-Model Drift

Definition:

- the code behaves as if the reachable state space or failure space is different from
  the one actually justified by the local call path, boundary, or type contract.

Common submodes:

- state-model inflation:
  - impossible edge-case handling;
  - `nil`/`None` checks on values that cannot be absent;
  - `try/catch` or equivalent around code that cannot throw;
  - empty-list preguards before loops that already handle emptiness;
  - repeated invariant validation in the same path without a boundary reason.
- failure-state suppression:
  - catch blocks swallowing errors silently;
  - code paths that degrade real failure into fake success.

Risk:

- fake robustness;
- silent-failure posture;
- obscured trust boundaries;
- inflated control flow around impossible or already-handled states.

### 2. Abstraction-Pressure Drift

Definition:

- the code introduces abstraction, decomposition, or ceremony without enough local
  complexity pressure to justify the shape.

Patterns:

- extracting helpers for trivial logic that will not be reused;
- boolean conditionals that return `true`/`false` instead of the condition itself;
- enumerating when direct indexing or direct iteration shape is the real operation;
- generic names that fail to bind to domain role and instead preserve template-like
  vagueness.

Risk:

- lower semantic density;
- fragmented reasoning;
- abstraction cost without offsetting reuse or clarity.

### 3. Semantic-Communication Drift

Definition:

- language is produced, but not enough meaning is added.

Patterns:

- comments that narrate what obvious code already shows;
- bullet recaps in prose of what was just done;
- hedging language in comments without corresponding epistemic uncertainty;
- error messages that describe code shape instead of the violated condition or user
  problem.

Risk:

- more text with less semantic value;
- degraded error usefulness;
- review surface inflation;
- lower signal-to-noise ratio.

### 4. Shape-Regularity Drift

Definition:

- the code surface becomes suspiciously even, mirrored, or stylistically uniform in a
  way that is not clearly demanded by the problem.

Patterns:

- branches that mirror each other too perfectly in length and phrasing;
- one sterile style applied across all contexts;
- regularity that looks mechanically normalized rather than locally shaped.

Risk:

- control flow shaped by template pressure instead of problem pressure;
- reduced locality;
- weaker confidence that the structure reflects real constraints.

Note:

- this family is usually weaker epistemically than state-model or failure-signal
  findings and should therefore rarely drive direct enforcement by itself.

### 5. Meta-Intent Failure

Definition:

- surrounding repo artifacts describe process residue or touched surfaces rather than
  intent, decision, or user-facing effect.

Patterns:

- changelog-style commit messages that enumerate files rather than intent;
- commentary that reports what was touched without stating why;
- recap artifacts whose prose density is high but whose decision density is low.

Risk:

- reduced maintainership clarity;
- weaker auditability of why a change exists;
- process traces that consume review time without preserving intent.

## Signal Kinds And Harm Kinds

These patterns should not be governed as one flat smell bucket.

Each rule should distinguish:

- `signal_kind`
  - `state_model_drift`
  - `abstraction_pressure_drift`
  - `semantic_communication_drift`
  - `shape_regularity_drift`
  - `meta_intent_failure`
- `harm_kind`
  - `correctness_risk`
  - `failure_signal_loss`
  - `trust_boundary_blur`
  - `maintainability_drag`
  - `semantic_density_loss`
  - `reviewer_load_inflation`
  - `intent_opacity`

This separation matters because some weak signals can still carry serious harm in a
particular context, while some visually strong signals are only advisory.

## ODEU Abstraction

### O: Ontology

The governed object is not "AI code." The governed object is a typed family of
pressure-mismatch drifts in code and repo communication artifacts.

Each finding should minimally bind:

- `signal_kind`
- `subpattern`
- `subject_kind`
- `subject_ref`

Recommended subject kinds:

- `code_span`
- `diff_hunk`
- `function_or_method`
- `test_case_or_fixture`
- `comment_block`
- `error_message`
- `commit_message`
- `review_note`
- `recap_artifact`

### E: Epistemics

Evidence should be modeled explicitly, because the important split is not only
severity. It is the kind of evidence supporting the finding.

Recommended evidence modes:

- `ast_shape`
- `control_flow_shape`
- `exception_flow_shape`
- `nullability_or_presence_inference`
- `duplicate_invariant_path`
- `lexical_naming_pattern`
- `comment_text_pattern`
- `error_text_pattern`
- `commit_text_pattern`
- `diff_shape_heuristic`
- `review_only_human_judgment`

Recommended evidence regimes:

- `deterministic_local`
  - the local code structure is sufficient to prove the issue with high confidence.
- `static_contextual`
  - local structure suggests the issue strongly, but contextual information still
    matters.
- `semantic_ambiguous`
  - the observation is real, but the drift claim depends on human or synthetic
    judgment over meaning, style, or local intent.
- `meta_governance`
  - the subject is a commit, report, review note, or other surrounding artifact rather
    than executable code.

Each rule should carry:

- `evidence_mode`
- `evidence_regime`
- `false_positive_risk`
- `required_context_scope`
- `counterexample_policy`

### D: Deontics

The deontic layer should not flatten all findings into one "bad smell" judgment.

Recommended allowed actions:

- `safe_autofix`
- `deterministic_finding`
- `review_only_finding`
- `forbid`
- `discourage`
- `allow_with_justification`
- `meta_artifact_correction`

Deontic force should be derived from:

- signal kind;
- harm kind;
- evidence regime;
- rewrite risk.

Recommended resolution routes:

- `deterministic_only`
- `oracle_assisted`
- `human_only`

This route is separate from allowed action. A finding may still be `review_only` while
being resolved by an oracle-assisted checkpoint, and a deterministic finding may still
route to humans if the current harness policy forbids model assistance.

### U: Utility

The point of the module is not aesthetic normalization.

The point is:

- less fake safety;
- less failure-signal suppression;
- less abstraction without pressure;
- higher semantic density in comments and errors;
- lower reviewer load;
- more truthful commit and change communication;
- better confidence that code shape reflects actual problem pressure.

## Evidence And Action Regimes

### A. Deterministically Provable Local Drift

Examples:

- boolean-return ceremony;
- trivial empty-list preguards before loops;
- some duplicate invariant checks on the same path;
- some impossible nullability guards;
- some swallowed exceptions.

Typical action:

- `safe_autofix` for the narrow behavior-preserving subset;
- otherwise `deterministic_finding`.

### B. Statically Suggestive But Context-Sensitive Drift

Examples:

- trivial helper extraction;
- dead `try/catch`;
- generic naming that looks template-shaped rather than domain-shaped;
- some mirrored branches;
- some over-descriptive error strings.

Typical action:

- `deterministic_finding` or `discourage`;
- never broad blind autofix by default.

### C. Semantically Ambiguous Drift

Examples:

- narrating comments;
- hedging language in comments;
- sterile regularity judgments;
- whether a helper is truly unjustified in a specific local module.

Typical action:

- `review_only_finding`;
- optionally `allow_with_justification` if the style or pedagogical context is
  intentional.

### D. Meta-Governance Drift

Examples:

- changelog-style commit messages;
- recap artifacts that list touched surfaces without intent;
- review commentary that reports process residue without decision content.

Typical action:

- `meta_artifact_correction` or `discourage`;
- do not collapse this lane into executable-code smell enforcement.

## Derived Automation Posture

Automation tier should be treated as derived output, not the first conceptual split.

Recommended interpretation:

- high-confidence deterministic local drift plus low rewrite risk:
  - `safe_autofix`
- high-confidence deterministic local drift plus mixed rewrite risk:
  - `deterministic_finding`
- contextual drift:
  - `deterministic_finding` or `review_only_finding`
- ambiguous semantic drift:
  - `review_only_finding`
- meta-governance drift:
  - `meta_artifact_correction` or `discourage`

## Hybrid Execution Architecture

The longer-term target is not a monolithic lint rule pack. It is a hybrid
deterministic-plus-synthetic harness in which the deterministic meta-tool remains the
authority while the resident coding agent is invoked only at typed checkpoints that
require interpretation.

This is a reversal of ordinary tool calling:

- not only "agent calls tool";
- also "deterministic tool invokes a typed oracle checkpoint against the resident
  agent."

The checkpoint classifier should minimally distinguish:

- `deterministic_pass`
- `deterministic_fail`
- `oracle_needed`
- `human_needed`

Required hybrid artifacts:

- `synthetic_pressure_mismatch_oracle_request@1`
- `synthetic_pressure_mismatch_oracle_resolution@1`
- `synthetic_pressure_mismatch_checkpoint_trace@1`

Hybrid execution invariants:

- the deterministic harness classifies checkpoints and owns adjudication;
- the resident agent advises, interprets, or proposes local resolution;
- oracle output is never itself authoritative repo mutation;
- oracle output may only feed deterministic adjudication, report materialization, or a
  fix-plan artifact under current harness policy;
- oracle requests must be replayable through pinned input, policy source, model id,
  and model version metadata;
- caching is allowed only when the request packet and evaluation policy identity
  match;
- escalation depth must be fixed and bounded;
- unstable or contradictory oracle outputs must fail closed into `human_needed`;
- live network state must not become canonical evaluation evidence.

## Proposed Meta-Module

The proposed bounded module family is:

- `synthetic_pressure_mismatch_conformance`

Implementation note:

- package placement remains open at planning stage;
- the first implementation can reasonably live in `adeu_core_ir` because `V39-A`
  already established neighboring conformance substrate there;
- if this family expands into a broader reusable conformance territory, a dedicated
  package such as `adeu_conformance_ir` may become justified later.

Planned artifacts:

- core artifacts:
  - `synthetic_pressure_mismatch_rule_registry@1`
  - `synthetic_pressure_mismatch_observation_packet@1`
  - `synthetic_pressure_mismatch_conformance_report@1`
  - `synthetic_pressure_mismatch_fix_plan@1`
- hybrid artifacts:
  - `synthetic_pressure_mismatch_oracle_request@1`
  - `synthetic_pressure_mismatch_oracle_resolution@1`
  - `synthetic_pressure_mismatch_checkpoint_trace@1`

Registry note:

- the rule registry governs admissible rule law only;
- it does not materialize concrete finding instances, concrete subject references, or
  observed conformance outcomes.

Recommended registry fields:

- `rule_id`
- `signal_kind`
- `subpattern`
- `harm_kind`
- `evidence_mode`
- `evidence_regime`
- `allowed_action`
- `applicable_subject_kinds`
- `false_positive_risk`
- `required_context_scope`
- `expected_utility_gains`
- `rewrite_risk`
- `counterexample_policy`
- `resolution_route`
- `forward_agent_policy`
- `post_optimizer_policy`

Recommended registry law:

- `applicable_subject_kinds` should be a non-empty bounded array;
- `expected_utility_gains` should be a non-empty bounded array;
- if `allowed_action = safe_autofix`, require:
  - `evidence_regime = deterministic_local`
  - `resolution_route = deterministic_only`;
- `counterexample_policy` should declare:
  - when the rule does not apply,
  - what evidence defeats the inference,
  - whether exemption requires review.

Planning note:

- `expected_utility_gain` should freeze to a bounded vocabulary in `V39-B` rather
  than remain free prose in the first locked schema.

Recommended report fields:

- `subject_ref`
- `subject_kind`
- `observation_count`
- `findings`
- `findings_by_evidence_regime`
- `findings_by_allowed_action`
- `safe_autofix_candidates`
- `high_confidence_blockers`
- `review_only_findings`
- `meta_governance_findings`
- `overall_pressure_mismatch_posture`

Constraint:

- `overall_pressure_mismatch_posture` is a convenience label only;
- it must not become a hidden scalar score or primary decision source.

Glossary note:

- `V39-B` should decide whether the pressure-mismatch vocabulary remains local to the
  rule registry or is exported as a dedicated glossary artifact;
- it should not silently overload the `V36-A` same-context reachability glossary,
  which serves a different domain.

## Embedding In Practice

### A. Forward Coding Agent

The forward coding agent should adopt preventive rules:

- do not add guards without a reachable failure model;
- do not duplicate invariant checks inside one call path without a boundary reason;
- do not extract helpers unless reuse or real complexity reduction exists;
- do not narrate obvious code in comments;
- do not use generic names where a domain role should carry the meaning;
- do not swallow errors;
- make error messages describe the actual problem and subject;
- use commit messages for intent, not touched-file recaps.

### B. Post-Code Optimizer Agent

The post-code optimizer should adopt corrective rules:

- auto-fix only the narrow deterministic-local subset;
- emit deterministic findings for high-confidence local drift;
- keep semantic ambiguity and regularity judgments advisory;
- preserve behavior over cleanliness;
- treat swallowed errors and false trust-boundary guards as highest priority;
- emit a fix plan rather than a blind rewrite when confidence is mixed.

## Relation To V39-A

`V39-A` already established a retrospective external-contribution conformance lane.

This draft is a natural follow-on because it generalizes one layer of that work:

- from "is this imported PR aligned to repo structure?"
- toward "what typed pressure-mismatch drifts should any module, diff, or surrounding
  repo artifact be checked against?"

The first bounded use should remain narrow:

- use the existing poetry utility reference as one seed example;
- keep the module about structural drift governance rather than a generic style
  marketplace;
- preserve the separation between code alignment, process alignment, and meta-artifact
  hygiene.

## Recommended Slice Sequence

- `V39-B`: rule taxonomy and canonical registry
- `V39-C`: observation packet, deterministic detectors, and conformance report
- `V39-D`: forward-agent and post-optimizer policy projection, plus bounded autofix
  planning
- `V39-E`: hybrid checkpoint classifier, oracle request and resolution artifacts,
  deterministic adjudicator, replay and cache pinning, and bounded human escalation

This keeps the work inside the broader `V39` module-conformance terrain instead of
spawning a disconnected family for every adjacent structural-governance concern.
