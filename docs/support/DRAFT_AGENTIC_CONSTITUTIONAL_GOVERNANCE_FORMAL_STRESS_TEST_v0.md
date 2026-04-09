# Draft Agentic Constitutional Governance Formal Stress Test v0

Status: working draft support companion (April 8, 2026 UTC).

Authority layer: support.

This document consolidates the two parallel support drafts:

- `docs/support/DRAFT_AGENTIC_CONSTITUTIONAL_GOVERNANCE_FORMAL_STRESS_TEST_PARALLEL_v1.md`
- `docs/support/DRAFT_AGENTIC_CONSTITUTIONAL_GOVERNANCE_FORMAL_STRESS_TEST_PARALLEL_v2.md`

using:

- `docs/support/DRAFT_AGENTIC_CONSTITUTIONAL_GOVERNANCE_FORMAL_STRESS_TEST_MERGE_GUIDE_v0.md`

It is the formal stress-test companion only.

It does not, by itself, revise the underlying doctrine note, authorize runtime behavior,
release schema families, or settle the implementation architecture.

## Purpose

- preserve the strongest adversarial pressure from the second parallel draft;
- restore the best synthesis pieces that the first draft carried more clearly;
- keep the local conflict kernel explicit instead of disappearing into a broader hybrid;
- produce one support-layer companion that can later guide a separate doctrine rewrite or
  a stand-alone moduleization pass.

## Reading Stance

Hold ODEU fixed at the meta-axiom level.

Under that reading, the note under assessment is treated as an implementation-governing
candidate for constitutional governance of agentic systems, not as the meta-axiom layer
itself.

The merged readout is:

- strongest on mutation law, inheritance law, and the four-layer split;
- weakest on lawful-specialization proof theory, local defeat semantics, and operational
  guarantees under compaction, spawn, and model swap.

## irreducible_commitments

The note commits to the following claims strongly enough that any acceptable formal
implementation must preserve them.

1. There are four semantically distinct layers:
   - constitutional as law
   - role as posture
   - task as assignment
   - runtime as state
2. Each layer has its own mutation and persistence law rather than just a different
   scope.
3. Lower layers may narrow upper layers but may not rewrite or widen them.
4. Conflict handling is interpretive but asymmetric:
   - prefer a reading that preserves lawful specialization;
   - only impossible specialization is a true conflict.
5. Runtime is presumptively factual rather than normative and must not silently create
   permission.
6. Spawn, resume, compaction, and model swap are legality-sensitive transitions with
   layer-specific persistence rules.
7. Compaction preserves continuity of execution, not continuity of law; constitutional
   and role must not be re-authored as lossy recap.
8. Generic exploratory posture placed too high can create a real hierarchy bug rather
   than a mere worker-compliance bug.
9. Constitutional change is reserved for an explicit maintenance phase and is illegal as
   a side effect of normal execution.
10. The runtime interpretation anchor is repo-shaped:
    - constitutional maps to `base_instructions`
    - role maps to collaboration or developer posture
    - task maps to spawned worker packet or local contract
    - runtime maps to current history, bridge artifacts, live tools, and current facts

## hidden_assumptions

As written, the note is not yet a formal theory. Its strongest terms still lack witness
conditions.

1. The slogan "lower layers narrow upper layers" is doing the work of several different
   relations across heterogeneous objects.
2. "Lawful specialization" has no non-circular legality test yet.
3. The note presumes a bounded parsing model for admissible readings but does not define
   one.
4. Posture is being treated as defeasible in the anchor case without being explicitly
   typed that way.
5. The task layer is secretly split between charter and residual, but the split is not
   formalized.
6. Runtime is not actually cleanly factual in the note's own wording because blockers,
   accepted decisions, and obligations can exert norm-adjacent force.
7. Validation order is being conflated with control order.
8. There is no explicit scheduler semantics for choosing among multiple legal traces.
9. Conflict detection lacks a witness surface such as:
   - refinement proof failure
   - unsatisfiable active stack
   - missing concretization witness
10. Stable source, stable reference, and exact carry-over are being treated as though
    they were equivalent.
11. The whitelist assumption is stronger than it looks because exported "facts" can still
    shape behavior materially.
12. Model-family bias and adapter instructions do not yet have a clean formal home.
13. Nominal role labels are assumed not to exist, but nothing yet forbids them.
14. Collaboration mode and autonomy overlays are assumed to fit inside role semantics
    without proof.
15. Maintenance phase is assumed to be isolatable and enforceable without a formal
    procedure.
16. The distinction between hierarchy bug and worker bug is assumed to be diagnostically
    meaningful before a falsifiable test exists.

## meta_edge_ledger

Across candidates, the same failure classes recur.

1. No proof object for lawful specialization.
2. Posture lacks normative-force typing.
3. Law versus posture is not just precedence.
4. Runtime is under-typed between fact, feasibility, admissibility, and permission.
5. Fact-to-permission laundering remains the most dangerous contamination path.
6. Carry-over artifacts are heterogeneous rather than one ontological kind.
7. Phenomenology is banned directionally but not yet typed.
8. Spawn packet synthesis is itself a constitutional risk surface.
9. Compaction needs exact external identity for law.
10. Model-swap invariance is weaker than behavior invariance.
11. Role may remain nominal even when a role label exists.
12. Source-channel projection into semantic layers remains unresolved.
13. Maintenance is still a word, not yet a governance procedure.
14. U-lane pressure can launder itself upward as pseudo-law.
15. Narrative prompts are weaker than the guarantees being claimed.

## candidate_family

The merged family separates:

- primary candidates that belong in the strongest final hybrid;
- secondary pressure candidates that are still useful probes but should not be treated as
  the main architecture.

### Primary candidates

#### C1. Monotone Specialization Calculus (MSC)

- `formal_style`: order-theoretic or constraint-based refinement calculus
- `core_idea`: each upper layer denotes an admissible set, and lower layers are legal
  only when they shrink rather than widen that set
- `main_strength`: cleanest simple meaning of monotone narrowing
- `main_failure_risk`: underfits ordered obligations, defaults, and posture semantics

MSC remains useful because it gives the cleanest intuition for non-widening, but it is
not sufficient alone.

#### C2. Prioritized Defeasible Layer Logic (PDLL)

- `formal_style`: layered defeasible logic over rule bases plus a separate fact base
- `core_idea`: constitutional rules are hard, role rules are defaults, task rules are
  more specific and may lawfully defeat role defaults without rewriting constitutional
  law
- `formal_primitives`:
  - rule bases `RC`, `RR`, `RT`
  - fact base `BF`
  - strict rules, defaults, defeaters, bridge rules
  - priority relation by force and specificity
  - proof trees
- `main_strength`: best local semantics for the anchor bug where `checkpoint first`
  should defeat inherited `explore/document first`
- `main_failure_risk`: poor lifecycle machine and weak mutation semantics unless paired
  with an operational shell

PDLL is restored here as a first-class candidate, not a side note.

#### C3. Temporal-Deontic Trace Logic (TDTL)

- `formal_style`: temporal or deontic trace logic over execution traces
- `core_idea`: legality is partly a property of ordered traces, not just static packet
  compatibility
- `main_strength`: best expression of prefix-sensitive task obligations and lifecycle
  invariants
- `main_failure_risk`: weak on posture typing and conflict adjudication unless paired
  with a defeasible kernel

#### C4. Institution-Style Multi-Level Norm System (IMNS)

- `formal_style`: multi-level institutional governance or constitutive-rule framework
- `core_idea`: constitutional law governs what lower norms are valid, how facts become
  institutionally relevant, and when amendment is legal
- `main_strength`: best conceptual backbone for law/posture/assignment/state as
  different ontological types
- `main_failure_risk`: can become a post hoc counts-as justification machine and still
  underfit procedural order without a temporal layer

#### C5. Typed Hierarchical Abstract Machine Plus (THAM+)

- `formal_style`: typed abstract machine with immutable upper-layer packet references,
  proof-carrying refinement, scoped exports, and adapter checks
- `core_idea`: runtime execution is an explicit legality-checked machine over registers
  for constitutional, role, task, runtime, and adapter or overlay state
- `formal_primitives`:
  - canonical packet ASTs and hashes
  - typed registers
  - refinement proofs
  - adapter certificates
  - task identifiers and scoped exports
  - privileged transition operators
- `main_strength`: strongest operational shell for spawn, compaction, resume, model
  swap, and auditability
- `main_failure_risk`: only as good as the compiler, ontology, and adapter proofs that
  feed it

This is the merged THAM shape:

- keep the human-readable THAM frame from the first draft;
- upgrade it with the stronger C6 machinery from the second draft.

### Secondary pressure candidates

#### C6. Typed Environment LTS

Useful for testing whether frame typing alone is enough.

Main weakness:

- type separation does not guarantee semantic separation.

#### C7. Dynamic Inheritance/Update Logic

Useful for pressure-testing conservative update claims and compaction semantics.

Main weakness:

- it can preserve theory while still losing behavior.

## countermodels

These are the most important failure probes for the merged family.

### C1. MSC

1. Ordered-obligation underfit.
   If `explore before edit` and `checkpoint before edit` are both represented only as set
   restrictions, the system still admits `explore; checkpoint; edit` even when the
   architecture needs `checkpoint` to come first.
2. Hidden widening by ontology loss.
   If a risky tool is typed only as generic `tool_use`, a lower-layer update can appear
   narrowing while still reintroducing forbidden effects.
3. Compaction paraphrase drift.
   If upper predicates are preserved only by recap rather than exact identity, monotone
   narrowing can still drift in practice.

### C2. PDLL

1. Role default hardens into law.
   If `explore/document first` is encoded as a hard rule rather than a defeasible role
   default, the anchor bug becomes an ordinary contradiction instead of a hierarchy bug.
2. Temporal underfit.
   If PDLL only captures defeat and specificity but not prefix order, it can conclude
   that checkpointing is obligatory without guaranteeing that it happens first.
3. Obligation leakage through baton state.
   If parent-side residual obligations are reintroduced as child task rules without scope
   checks, lawful defeat becomes covert inheritance laundering.

### C3. TDTL

1. Posture typing collapse.
   Temporal order alone cannot tell whether `explore first` is hard law, default
   posture, or advisory heuristic.
2. Runtime fact becomes permission.
   Availability plus temporal obligation can create de facto permission unless fact to
   norm bridges remain explicit.
3. Model-swap invariance gap.
   The same formulas can evaluate under different executors with materially different
   next-action behavior.

### C4. IMNS

1. Counts-as opportunism.
   If both exploration and checkpointing can be ratified as diligence under different
   constitutive rules, lawful specialization becomes a justification game instead of a
   constraint.
2. Constitutive backdoor from facts to permission.
   If `available(toolX)` can count as `permitted(use toolX)`, brute facts launder
   themselves into norms.
3. Procedural underfit.
   Institutional validity alone does not force prefix order.

### C5. THAM+

1. Compiler smuggling.
   If the compiler misclassifies role posture as constitutional law, the machine can
   enforce the wrong hierarchy perfectly.
2. Adapter proof too weak.
   If swap certificates preserve clauses but not constitutionally relevant next-action
   behavior, model swap still drifts in practice.
3. Scoped obligation leak.
   If exported residual obligations are not checked against child-task scope, packet
   legality can still carry irrelevant normative momentum downward.

### C6. Typed Environment LTS

1. Nominal-role collapse.
   A non-empty role label without a substantive role packet still looks well-formed until
   behavior falls through to priors.
2. Overlay escape.
   If autonomy or collaboration overlays sit outside the four-layer frame stack, the
   architecture cannot localize the actual control surface.

### C7. Dynamic Inheritance/Update Logic

1. Vocabulary-extension widening.
   Lower updates can preserve upper truths in the old vocabulary while quietly widening
   what becomes justifiable in the new one.
2. Bisimulation without strategy preservation.
   Compaction can preserve formulas while changing next-step behavior.

## attack_matrix

Legend:

- `strong`: native traction
- `partial`: workable only with additional machinery
- `weak`: fragile or incomplete
- `cannot represent cleanly`: outside the candidate's natural semantics

| candidate | hierarchy bug detection | inheritance bug detection | compaction-law drift | nominal-role collapse | false narrowing / hidden widening | runtime-to-law contamination | model-swap discontinuity | prose ambiguity tolerance |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| C1 MSC | partial | partial | partial | weak | partial | partial | cannot represent cleanly | weak |
| C2 PDLL | strong | partial | partial | weak | partial | strong | weak | partial |
| C3 TDTL | strong | partial | partial | weak | partial | partial | weak | weak |
| C4 IMNS | partial | partial | partial | strong | partial | strong | cannot represent cleanly | partial |
| C5 THAM+ | strong | strong | strong | strong | strong | strong | partial | cannot represent cleanly |
| C6 Typed Environment LTS | partial | strong | strong | strong | partial | strong | weak | partial |
| C7 Dynamic Inheritance/Update Logic | partial | partial | strong | weak | partial | partial | partial | weak |

The merged pattern remains harsh:

- no single candidate is strongest on both normative validity and behavioral continuity;
- the hybrid remains the most credible answer.

## minimum_repairs

Without at least the following, the architecture remains a disciplined memo rather than a
runtime-governing constitutional calculus.

1. Replace the single slogan `lawful specialization` with typed relations such as:
   - `role_refines(C,R)`
   - `task_refines(C,R,T)`
   - `state_instantiates(C,R,T,S)`
2. Require material packets, not labels, for constitutional, role, and task layers.
3. Split task into:
   - `TaskCharter`
   - `TaskResidual`
4. Separate validation order from action-selection order:
   - validation may remain `C -> R -> T -> S`
   - action selection must let determinate task obligations outrank role defaults
5. Formalize a runtime contamination firewall over at least:
   - descriptive facts
   - scoped residual obligations
   - banned or separately typed salience carriers
6. Make upper-layer identity exact across compaction, resume, and swap.
7. Define an explicit inheritance and refresh algebra for spawn, compaction, resume, and
   swap.
8. Add conflict-witness conditions and a bug classifier so `hierarchy_bug` becomes
   testable rather than rhetorical.
9. Introduce an explicit adapter or overlay formalism.
10. Formalize maintenance phase as a privileged meta-transition with authorization and
    provenance.
11. Constrain the action and effect ontology so hidden widening through tool abstraction
    becomes detectable.
12. Compile prose into schema, packet ASTs, or other canonical machine-checkable forms,
    or do not ratify the doctrine as runtime-governing.
13. Add normative-force typing at minimum:
    - `hard`
    - `default`
    - `advisory`
    - `factual`
14. Treat U-lane exploration and completeness heuristics as suspect by default rather
    than allowing them to float upward as pseudo-law.

## best_backbone_vs_best_runtime_model

### Best conceptual backbone

`IMNS`.

Why:

- it best captures multi-level normative validity;
- it best separates brute facts from normative authority;
- it makes the law/posture/assignment/state distinction ontological rather than merely
  rank-based.

### Best local conflict kernel

`PDLL`.

Why:

- it is the clearest local answer to the motivating bug;
- it can represent task-local ordered obligations lawfully defeating broader role
  defaults without rewriting constitutional law.

### Best temporal and lifecycle layer

`TDTL`.

Why:

- it is best for prefix order, ordered obligations, and lifecycle invariants over spawn,
  compaction, resume, and maintenance events.

### Best runtime-operational shell

`THAM+`.

Why:

- it is strongest for packet identity preservation, scoped exports, audit events,
  legality-sensitive transitions, and adapter checks.

### Cleanest simple narrowing intuition

`MSC`.

Why:

- it keeps the non-widening idea crisp even though it cannot carry the final design
  alone.

### Merged recommendation

The least fragile stack is:

- `IMNS` as conceptual backbone
- `PDLL` as local conflict and defeat kernel
- `TDTL` as temporal and lifecycle monitor
- `THAM+` as runtime shell
- `MSC` as explanatory refinement intuition

The secondary candidates remain useful probes, but they should not be treated as the
center of the final hybrid.

## what_would_falsify_this_architecture

The architecture would be seriously undermined by any of the following.

1. No non-circular refinement relation can be defined.
2. Role and law cannot be behaviorally separated in live systems.
3. Compaction cannot preserve upper law except by paraphrase.
4. Fact-only child inheritance is either impossible or non-functional in practice.
5. Runtime facts repeatedly become de facto permission despite formal bans.
6. Model swap produces constitutionally relevant drift that no acceptable adapter or test
   regime can bound.
7. Moving exploratory heuristics out of constitutional packets into role packets does not
   materially reduce the anchor failure rate.
8. The four-layer story collapses once adapters, overlays, or task residuals are made
   explicit.
9. Refinement checking becomes intractable on the packet language needed for real runs.
10. Preserving canonical law identity still does not preserve constitutionally relevant
    behavior within any acceptable tolerance.

## open_questions

1. What exactly is a role packet:
   - defaults
   - search policy
   - narrative tone
   - second-order norm bundle
   - or some typed mixture
2. Should `TaskResidual` be a task sublayer or a distinct execution-state artifact with
   norm-bearing semantics?
3. What is the minimal action and effect ontology required to detect hidden widening?
4. What equivalence notion should compaction preserve:
   - formula truth
   - scheduler state
   - policy distribution
   - bounded behavioral tolerance
5. Can model-family adapters be certified intensionally, or do they require empirical
   regression suites?
6. Are collaboration mode and autonomy overlays genuinely roles, or a separate control
   stratum?
7. What evidence threshold should trigger `true_conflict` rather than
   `underdetermined_but_legal`?
8. How constrained must the packet language become for refinement to stay auditable?
9. Can the architecture remain four-layer once adapters, overlays, and task residuals
   are fully formalized?
10. Which failures should count as constitutional violations rather than ordinary
    suboptimal execution?

## Bottom Line

The merged verdict is:

- the note is directionally strong on hierarchy, mutation law, and anti-drift posture;
- it is not yet a hardened constitutional calculus;
- the strongest path is not a single formalism but a disciplined hybrid:
  - `IMNS` for validity
  - `PDLL` for lawful defeat
  - `TDTL` for ordered and lifecycle legality
  - `THAM+` for runtime enforcement

This companion should remain separate from the later revised doctrine note.

That separation is itself part of the governance discipline.
