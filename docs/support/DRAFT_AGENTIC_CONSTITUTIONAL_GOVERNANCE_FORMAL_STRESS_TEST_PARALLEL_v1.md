## 1. `irreducible_commitments`

ODEU is fixed here as the meta-axiom layer. The note below is therefore being read as an implementation target, not as the meta-axiom itself. Under that reading, the document is strongest on mutation/persistence law and weakest on the proof theory of lawful specialization.

1. There are exactly four semantic layers, and they are not interchangeable: constitutional = law, role = posture, task = assignment, runtime = state. Formalization has to preserve these as different kinds of thing, not merely different priorities in one flat stack.

2. Interpretation is top-down: constitutional first, then role, then task, then runtime. Lower layers may narrow/specialize upper layers, but may not rewrite or widen them. Apparent conflict is to be read as lawful specialization if possible; only impossible specialization is a true conflict.

3. Runtime is presumptively factual, not normative. It may provide environment, tools, blockers, bridge facts, history, and current message, but it must not silently redefine good work, widen permission, or smuggle workflow norms upward.

4. Each layer has its own mutation/persistence law: constitutional is immutable during ordinary execution and inherits across spawn/resume/compaction/model swap; role persists until explicit role transition; task is replaced on reassignment and cleared on completion; runtime is rebuilt from current facts each turn with only explicit factual carry-over.

5. Spawn is a legality-sensitive operation: child inherits constitutional law; inherits or changes role depending on spawn type; gets a new task packet; starts with fresh runtime; and may import only whitelisted baton facts/open obligations/environment facts, not the parent’s phenomenology, noise, or accidental normative pressure.

6. Compaction preserves continuity of execution, not continuity of law. It may carry task state, open obligations, blockers, recent accepted decisions, continuation artifacts, and durable factual memory, but it may not rewrite constitutional or role law; those must survive by stable reference, stable source, or exact carry-over, not lossy recap.

7. Resume and model swap preserve the hierarchy while refreshing runtime. Model-specific instructions may be refreshed, and posture shifts may need warning, but model change itself must not rewrite constitutional law.

8. Constitutional change is legal only inside an explicit maintenance/constitutional-review phase, separate from normal task execution. Constitutional mutation as a side effect of summarization, role drift, or task completion is illegal.

9. A hierarchy bug is distinct from a worker bug. In particular, if generic exploratory posture is placed in `base_instructions` and competes with an explicit lower-layer task ordering like “checkpoint first,” the resulting “drift/disobedience” is an architectural failure of layer assignment, not merely worker noncompliance.

10. The current runtime interpretation anchor is repo-specific: constitutional maps to `base_instructions`, role to collaboration/developer instructions, task to spawned worker packet/local contract, and runtime to context/history/`continuation_bridge`/`thread_memory`/live tool state. Any formalization that cannot explain that mapping and its failure mode is missing the actual problem.

---

## 2. `candidate_family`

### Level separation used below

| level                        | meaning                                                                                                                                                         |
| ---------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| meta-axiom level             | ODEU fixes the ontology, witness discipline, legality conditions, and optimization-boundary constraints that any acceptable implementation must respect         |
| formal implementation level  | the candidate calculi/machines below                                                                                                                            |
| runtime interpretation level | what a Codex-like orchestrator/worker stack would do when executing, checking, compacting, spawning, resuming, or swapping models under one of those candidates |

The concrete runtime regression test is the note’s own bug: explicit task ordering `checkpoint first` versus inherited generic `explore/document first` posture masquerading as law.

### Candidate A

* `name`: Monotone Specialization Calculus (MSC)
* `core_idea`: Each non-runtime layer denotes a specification over admissible executions. Lower layers are legal iff they refine the admissible set of upper layers rather than widen it.
* `formal_primitives`: typed layer specs `C, R, T`; factual state `Σ`; refinement relation `⊑`; conflict predicate `⊥`; specialization witness `w`; whitelist operator for carry-over; law identity tokens.
* `main_axioms_or_rules`: `T ⊑ R ⊑ C`; facts in `Σ` can restrict feasibility but cannot themselves generate norms; a conflict claim is admissible only if no refinement witness exists; only authorized operators may replace each layer.
* `how_it_represents_layers`: `C/R/T` are normative specs; `Σ` is a separate factual ledger.
* `how_it_represents_mutation`: layer-specific rewrite operators with guards; illegal if a rewrite breaks refinement or touches a protected layer.
* `how_it_represents_spawn`: child state is `⟨C, R* , T_child, whitelist(Σ_parent)⟩`, where `R*` is inherited or replaced by spawn kind.
* `how_it_represents_compaction`: preserve `id(C)` and `id(R)` exactly; compact only task/runtime artifacts.
* `how_it_represents_resume_or_model_swap`: resume reconstructs `Σ`; model swap changes executor/model metadata but not `C/R/T`.
* `what_counts_as_illegal`: widening, unauthorized mutation, unsatisfied refinement witness, or fact-to-norm promotion.
* `main_strength`: Very crisp about vertical non-widening and upper-layer invariance.
* `main_weakness`: “Lawful specialization” is only as good as the refinement semantics; defaults, sequencing, and posture are not native.

### Candidate B

* `name`: Typed Hierarchical Abstract Machine (THAM)
* `core_idea`: The hierarchy is an explicit machine state with typed registers and legal transition operators.
* `formal_primitives`: machine configuration `⟨C_ref, R_ref, T_pkt, Σ, phase, model_adapter⟩`; typed artifacts for facts, delegated obligations, blockers, decisions, uncertainty tags; guarded transitions.
* `main_axioms_or_rules`: only maintenance may write `C_ref`; only role transition may write `R_ref`; new assignment writes `T_pkt`; runtime refresh writes `Σ`; every structural operation emits an audit event.
* `how_it_represents_layers`: separate registers with schema-level type constraints.
* `how_it_represents_mutation`: explicit operators such as `enter_maintenance`, `set_role`, `set_task`, `refresh_runtime`.
* `how_it_represents_spawn`: `spawn(kind, baton)` allocates fresh runtime, copies upper refs, installs new task, copies only whitelisted baton artifacts.
* `how_it_represents_compaction`: emits a continuation artifact containing task/runtime carry-over only; upper-law refs are preserved by identity/hash.
* `how_it_represents_resume_or_model_swap`: `resume` reconstructs runtime from facts/history; `swap_model` updates model adapter/runtime facts but is forbidden from touching `C/R/T`.
* `what_counts_as_illegal`: forbidden register write, non-whitelisted inheritance, compaction that rewrites law refs, or runtime object with normative type in factual register.
* `main_strength`: Best operational fit for real orchestration, auditing, and deterministic enforcement.
* `main_weakness`: Excellent shell, weak semantics; it can faithfully enforce a badly typed constitution.

### Candidate C

* `name`: Prioritized Defeasible Layer Logic (PDLL)
* `core_idea`: Layer content is represented as strict/default/advisory rules plus specificity and priority relations. Task-specific rules can defeat role defaults without defeating constitutional law.
* `formal_primitives`: rule bases `RC, RR, RT`; fact base `BF`; bridge rules; strict rules, defaults, defeaters; proof trees; priority relation by force and specificity.
* `main_axioms_or_rules`: constitutional hard rules are undefeated unless constitution itself authorizes an exception; role rules are presumptively defaults; task rules are presumptively more specific than role rules; runtime facts may trigger rules but may not be rule heads unless explicitly authorized.
* `how_it_represents_layers`: three rule sets plus a separate factual base.
* `how_it_represents_mutation`: replace the relevant rule base only through authorized operators.
* `how_it_represents_spawn`: child gets `RC`, selected `RR`, new `RT`, fresh facts, and explicit baton/bridge facts; delegated obligations should be encoded as task rules, not leaked state.
* `how_it_represents_compaction`: preserve rule-base identities; carry only undischarged obligations, accepted decisions, and facts as explicit artifacts.
* `how_it_represents_resume_or_model_swap`: same rule bases, refreshed fact base/model facts.
* `what_counts_as_illegal`: unresolved contradiction after defeat calculation, lower-rule widening of higher hard rules, or permission derived from facts without bridge authority.
* `main_strength`: Best at the observed checkpoint-first vs explore-first failure mode.
* `main_weakness`: Good conflict kernel, poor lifecycle machine; mutation/inheritance semantics are bolted on.

### Candidate D

* `name`: Temporal-Deontic Trace Logic (TDTL)
* `core_idea`: Legality is a property of whole execution traces, not just local states. Spawn, compaction, resume, maintenance, and model swap are events constrained by temporal/deontic formulas.
* `formal_primitives`: traces, state propositions, event labels, temporal operators `G/X/U/F`, deontic operators `O/P/F`, violation predicates, trace monitors.
* `main_axioms_or_rules`: `G`-style invariants preserve constitutional/role/task layers across events; maintenance gates constitutional change; spawn and compaction have explicit postconditions; runtime facts are state propositions and may affect feasibility but not norms unless bridged.
* `how_it_represents_layers`: layer-indexed constraints over traces.
* `how_it_represents_mutation`: mutation appears as legal/illegal event transitions in the trace.
* `how_it_represents_spawn`: formulas constrain the next child trace segment to inherit upper law and only whitelisted facts.
* `how_it_represents_compaction`: formulas assert `C` and `R` identity across compaction seams.
* `how_it_represents_resume_or_model_swap`: formulas require `C/R/T` continuity and refreshed runtime after resume/swap.
* `what_counts_as_illegal`: any execution trace violating the temporal/deontic formulas.
* `main_strength`: Strongest for lifecycle invariants and audit of long-running execution.
* `main_weakness`: Static specialization, defeasibility, and posture semantics are not natural; proof burden is high.

### Candidate E

* `name`: Institutional Multi-Level Norm System (IMNS)
* `core_idea`: The constitutional layer is a higher-order institution governing what role and task institutions may validly enact, how facts become institutional facts, and when amendment is legal.
* `formal_primitives`: institutions, offices/roles, norms (`obligation`, `permission`, `prohibition`), constitutive `counts-as` rules, enactment relation, brute facts, institutional facts, amendment procedures.
* `main_axioms_or_rules`: lower-layer norms are valid only if authorized and not ultra vires; runtime facts become normatively relevant only through explicit constitutive rules; ordinary execution cannot amend the constitutional institution.
* `how_it_represents_layers`: `I_C` governs `I_R`, which governs `I_T`; runtime is a brute-fact and institutional-fact ledger.
* `how_it_represents_mutation`: amendment, role transition, task issuance, and fact update are distinct institutional acts.
* `how_it_represents_spawn`: spawning creates a child task institution under inherited constitutional law and selected role institution, with fresh brute facts and whitelisted institutional carry-over.
* `how_it_represents_compaction`: compaction updates institutional memory/state, not the constitutions themselves.
* `how_it_represents_resume_or_model_swap`: same institutions continue; only the executing actor/model changes.
* `what_counts_as_illegal`: ultra vires lower norms, unauthorized fact-to-permission conversion, unauthorized amendment, or carry-over treated as institutional fact without authorization.
* `main_strength`: Best semantic fit for law/posture/assignment/state as distinct kinds, and best on fact/norm separation.
* `main_weakness`: Heavyweight; needs an operational companion for real runtime control.

---

## 3. `adversarial_tests`

Assessment here is about native representational adequacy, not whether an implementation could later bolt on another subsystem.

### Candidate A — MSC

`edge_cases`

| edge case                                                                                                                                        | assessment                  | note                                                                                              |
| ------------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------- | ------------------------------------------------------------------------------------------------- |
| Lower-layer instruction seems to conflict with upper law, but may be lawful narrowing (`checkpoint first` vs inherited `explore/document first`) | Weakly                      | Works only if the refinement relation and normative force of both clauses are already formalized. |
| Generic exploration heuristic masquerading as constitutional law                                                                                 | Handles it well             | If encoded in `C`, task packets fail refinement, exposing the hierarchy bug.                      |
| Child worker inherits parent phenomenology instead of only whitelisted facts                                                                     | Handles it well             | Fresh `Σ` plus whitelist is easy to state.                                                        |
| Compaction silently rewrites constitutional or role law                                                                                          | Handles it well             | Invariance of `id(C)` and `id(R)` can be made explicit.                                           |
| Runtime facts quietly become normative permission                                                                                                | Requires extra machinery    | Bare refinement calculus needs a separate bridge/admissibility discipline.                        |
| Model swap changes effective behavior without explicit constitutional change                                                                     | Handles it weakly           | It can preserve the same law object, but not semantic behavior drift of the executor.             |
| Role packet is nominal only, not materially instantiated                                                                                         | Cannot represent it cleanly | Static refinement does not measure actual conformance of behavior to role.                        |
| Multiple upper layers interact ambiguously                                                                                                       | Requires extra machinery    | Needs a composition law for mixed-source upper content.                                           |
| Maintenance-phase updates leak into normal execution                                                                                             | Handles it weakly           | Can mark maintenance as special update, but not operationally enforce phase discipline by itself. |
| “Lawful specialization” is under-specified and collapses into interpretive vagueness                                                             | Cannot represent it cleanly | This is the candidate’s central failure mode unless witness semantics are independently hardened. |

### Candidate B — THAM

`edge_cases`

| edge case                                                                                                                                        | assessment                  | note                                                                                             |
| ------------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------- | ------------------------------------------------------------------------------------------------ |
| Lower-layer instruction seems to conflict with upper law, but may be lawful narrowing (`checkpoint first` vs inherited `explore/document first`) | Handles it weakly           | The machine can order registers, but the meaning of specialization is external to the machine.   |
| Generic exploration heuristic masquerading as constitutional law                                                                                 | Handles it weakly           | If it is loaded into `C_ref`, the machine will faithfully enforce the mistake.                   |
| Child worker inherits parent phenomenology instead of only whitelisted facts                                                                     | Handles it well             | This is exactly the kind of thing typed baton schemas and guarded spawn operators can block.     |
| Compaction silently rewrites constitutional or role law                                                                                          | Handles it well             | Guarded operators plus content-hash refs make this auditable.                                    |
| Runtime facts quietly become normative permission                                                                                                | Handles it well             | Runtime registers can be kept fact-only at the type level.                                       |
| Model swap changes effective behavior without explicit constitutional change                                                                     | Handles it weakly           | Register invariance is easy; behavioral equivalence of different models is not.                  |
| Role packet is nominal only, not materially instantiated                                                                                         | Handles it weakly           | The packet exists, but the machine needs external conformance tests to know whether it mattered. |
| Multiple upper layers interact ambiguously                                                                                                       | Handles it weakly           | It can store them, but not interpret mixed semantics without another formal layer.               |
| Maintenance-phase updates leak into normal execution                                                                                             | Handles it well             | Maintenance can be a privileged phase with forbidden writes outside it.                          |
| “Lawful specialization” is under-specified and collapses into interpretive vagueness                                                             | Cannot represent it cleanly | The machine is not itself a conflict/adjudication calculus.                                      |

### Candidate C — PDLL

`edge_cases`

| edge case                                                                                                                                        | assessment               | note                                                                                                            |
| ------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------ | --------------------------------------------------------------------------------------------------------------- |
| Lower-layer instruction seems to conflict with upper law, but may be lawful narrowing (`checkpoint first` vs inherited `explore/document first`) | Handles it well          | Task-specific rule can defeat a role default while still respecting constitutional hard rules.                  |
| Generic exploration heuristic masquerading as constitutional law                                                                                 | Handles it well          | Exactly the kind of mis-typed strict/default confusion this logic exposes.                                      |
| Child worker inherits parent phenomenology instead of only whitelisted facts                                                                     | Requires extra machinery | The logic needs a separate state artifact model for phenomenology and baton control.                            |
| Compaction silently rewrites constitutional or role law                                                                                          | Handles it weakly        | Rule-base identity can be required, but lossy recap drift is not natural to the logic.                          |
| Runtime facts quietly become normative permission                                                                                                | Handles it well          | Facts may trigger rules, but cannot become permissions without explicit bridge rules.                           |
| Model swap changes effective behavior without explicit constitutional change                                                                     | Handles it weakly        | Same rule base, different executor behavior remains mostly outside the logic.                                   |
| Role packet is nominal only, not materially instantiated                                                                                         | Handles it weakly        | The logic derives what should follow from a role, not whether the model actually internalized it.               |
| Multiple upper layers interact ambiguously                                                                                                       | Requires extra machinery | Priority relations can handle some cases, but mixed-source ambiguity quickly becomes ad hoc.                    |
| Maintenance-phase updates leak into normal execution                                                                                             | Requires extra machinery | Needs dynamic update semantics around amendment scope and suspension.                                           |
| “Lawful specialization” is under-specified and collapses into interpretive vagueness                                                             | Handles it weakly        | Better than prose because specificity/priority are explicit, but still depends on a well-designed defeat order. |

### Candidate D — TDTL

`edge_cases`

| edge case                                                                                                                                        | assessment               | note                                                                                                    |
| ------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------ | ------------------------------------------------------------------------------------------------------- |
| Lower-layer instruction seems to conflict with upper law, but may be lawful narrowing (`checkpoint first` vs inherited `explore/document first`) | Handles it weakly        | Temporal ordering helps, but defeasible priority between posture and task still needs extra structure.  |
| Generic exploration heuristic masquerading as constitutional law                                                                                 | Handles it weakly        | It can show a trace conflict, but not natively diagnose the category error of putting posture into law. |
| Child worker inherits parent phenomenology instead of only whitelisted facts                                                                     | Handles it well          | Spawn events and child-trace postconditions are natural.                                                |
| Compaction silently rewrites constitutional or role law                                                                                          | Handles it well          | Compaction invariants over traces are a strong fit.                                                     |
| Runtime facts quietly become normative permission                                                                                                | Handles it well          | Facts stay propositional unless explicit bridge formulas authorize normative effect.                    |
| Model swap changes effective behavior without explicit constitutional change                                                                     | Handles it weakly        | Can specify swap invariants, but behavioral equivalence across models is a hard additional problem.     |
| Role packet is nominal only, not materially instantiated                                                                                         | Handles it weakly        | Requires a nontrivial observational semantics mapping role to trace patterns.                           |
| Multiple upper layers interact ambiguously                                                                                                       | Requires extra machinery | The formulas become verbose and brittle without a separate composition discipline.                      |
| Maintenance-phase updates leak into normal execution                                                                                             | Handles it well          | Phase-gated temporal constraints are straightforward.                                                   |
| “Lawful specialization” is under-specified and collapses into interpretive vagueness                                                             | Requires extra machinery | Pure trace logic needs a refinement or non-monotonic layer on top.                                      |

### Candidate E — IMNS

`edge_cases`

| edge case                                                                                                                                        | assessment        | note                                                                                                             |
| ------------------------------------------------------------------------------------------------------------------------------------------------ | ----------------- | ---------------------------------------------------------------------------------------------------------------- |
| Lower-layer instruction seems to conflict with upper law, but may be lawful narrowing (`checkpoint first` vs inherited `explore/document first`) | Handles it well   | Lower task norms can be valid specializations if authorized and contextually narrower than role defaults.        |
| Generic exploration heuristic masquerading as constitutional law                                                                                 | Handles it well   | If ontology forbids posture-type norms in constitution, this becomes a category error or ultra vires enactment.  |
| Child worker inherits parent phenomenology instead of only whitelisted facts                                                                     | Handles it well   | Parent phenomenology has no institutional standing unless an explicit constitutive rule grants it one.           |
| Compaction silently rewrites constitutional or role law                                                                                          | Handles it well   | Compaction updates institutional state, not the constitutions themselves.                                        |
| Runtime facts quietly become normative permission                                                                                                | Handles it well   | Explicit `counts-as` rules make fact-to-norm conversion visible and challengeable.                               |
| Model swap changes effective behavior without explicit constitutional change                                                                     | Handles it weakly | Institutional validity is preserved, but executor/model drift is external.                                       |
| Role packet is nominal only, not materially instantiated                                                                                         | Handles it weakly | Occupying an office is representable; actual behavioral uptake still needs monitoring.                           |
| Multiple upper layers interact ambiguously                                                                                                       | Handles it well   | Multi-level governance relations are exactly what the framework was built for.                                   |
| Maintenance-phase updates leak into normal execution                                                                                             | Handles it well   | Amendment procedure is distinct from ordinary institutional operation.                                           |
| “Lawful specialization” is under-specified and collapses into interpretive vagueness                                                             | Handles it weakly | Authority is clearer, but you still need a substantive criterion for valid specialization versus covert new law. |

---

## 4. `meta_edge_ledger`

Across candidates, the same deep faults keep reappearing.

1. **No proof object for lawful specialization.**
   The note says to prefer the interpretation that makes lower content a lawful specialization. That is an interpretive canon, not yet a legality test. Without a witness discipline, every hard case becomes hermeneutics.

2. **Posture lacks normative-force typing.**
   If posture is hard law, task packets will constantly “conflict.” If posture is mere style, it becomes decorative. The architecture needs at least a strict/default/advisory distinction or “role” collapses either into “constitution-lite” or into theater.

3. **Law vs posture is not just precedence.**
   If the only difference is rank, then the design has not really separated constitutional law from role posture; it has just built a priority stack. A real constitution needs kind distinctions, not only stronger/weaker instructions.

4. **Runtime state is under-typed between feasibility, admissibility, and permission.**
   “Currently admissible state” is not yet precise. A missing tool can make an action impossible, blocked, or merely delayed. None of those is the same as prohibited. If that distinction is not formalized, runtime will leak into normativity.

5. **Fact-to-permission conversion is still the most dangerous laundering path.**
   The note correctly forbids runtime facts from silently becoming permission. But without explicit bridge or `counts-as` rules, the system will either cheat informally or freeze impotently.

6. **Carry-over artifacts are not a single kind.**
   “Open obligations,” “accepted decisions,” “durable factual memory,” “continuation bridge,” “blockers,” and “environment facts” are different ontological classes. Until each has type, authority, uncertainty status, and inheritance law, spawn/compaction remain prose.

7. **Phenomenology is banned, but not formally defined.**
   “Do not inherit the parent’s phenomenology” is directionally right and formally incomplete. If phenomenology is not typed, nothing stops it from reappearing as summary tone, implied urgency, or covert defaults in child packets.

8. **Spawn packet synthesis is itself a constitutional risk surface.**
   The parent/orchestrator that prepares a child packet can illegally rewrite law or posture while “summarizing.” The violation occurs before the child even starts. Packet construction therefore needs legality proofs, not trust.

9. **Compaction needs external identity for law.**
   The note is right that law must survive by stable reference/source or exact carry-over. That implies canonical artifacts, hashes, or signed IDs. Otherwise every summarizer becomes an untracked constitutional editor.

10. **Model swap invariance is weaker than behavior invariance.**
    Keeping `C/R/T` textually unchanged across a model swap does not preserve effective policy. Adapter instructions, context-window differences, and decoding priors can create de facto constitutional drift without textual amendment.

11. **Role may remain nominal.**
    A role packet can exist while behavior continues to be dominated by generic training priors or inherited exploration bias. The architecture lacks a conformance layer distinguishing role under-instantiation from worker disobedience.

12. **The source-channel / semantic-layer projection is unresolved.**
    `base_instructions`, developer instructions, collaboration mode, worker packets, history, and bridge artifacts may each contain mixed law/posture/task/state content. Unless the projection into the four-layer ontology is formalized, the model is aspirational, not enforceable.

13. **Maintenance is a word, not yet a governance procedure.**
    Who can enter maintenance? Is amendment local to a thread or global to a policy profile? What happens to active tasks on amendment? Without amendment procedure, “immutable during execution” is weaker than it looks.

14. **The architecture under-models U-lane pressure.**
    The concrete observed bug already shows it: generic exploration heuristics can launder themselves upward because they are instrumentally attractive. Any candidate that ignores optimization pressure will eventually re-import it as pseudo-law.

15. **Narrative prompts are insufficient for the guarantees the note wants.**
    The note wants mutation law, inheritance law, non-widening, and compaction integrity. Those are not reliably enforceable with prose alone. They need typed, canonical, hashable artifacts and machine-checkable transitions.

---

## 5. `comparison_matrix`

Relative scores, `1 = weak`, `5 = strong`.

| dimension                                            | MSC | THAM | PDLL | TDTL | IMNS |
| ---------------------------------------------------- | --: | ---: | ---: | ---: | ---: |
| clarity                                              |   4 |    4 |    3 |    2 |    3 |
| expressiveness                                       |   3 |    3 |    4 |    5 |    5 |
| ease of implementation                               |   4 |    5 |    4 |    2 |    2 |
| auditability                                         |   4 |    5 |    3 |    3 |    4 |
| ability to represent hierarchy bugs                  |   4 |    3 |    5 |    4 |    5 |
| ability to represent inheritance/refresh law         |   3 |    5 |    2 |    4 |    4 |
| resistance to prose drift                            |   3 |    4 |    3 |    4 |    4 |
| suitability for Codex-like runtime orchestration     |   4 |    5 |    4 |    3 |    3 |
| suitability for future deterministic enforcement     |   4 |    5 |    4 |    3 |    3 |
| fit to ODEU decomposition                            |   3 |    3 |    4 |    4 |    5 |
| handling of the checkpoint-first / explore-first bug |   3 |    2 |    5 |    4 |    4 |

Readout:

* **THAM** is the best operational shell.
* **PDLL** is the best local conflict/adjudication kernel.
* **IMNS** is the best standalone semantic fit for the constitutional ambition.
* **TDTL** is the best lifecycle auditor.
* **MSC** is the cleanest simple refinement story, but it breaks precisely where the design is most under-specified.

---

## 6. `recommended_direction`

The note’s refactor direction is directionally correct: make `base_instructions` genuinely constitutional, move exploration/work-mode defaults into role, make worker task packets explicit and phase-ordered, keep bridge/memory factual, and stop compaction from paraphrasing upper law. But that is still not enough to harden the architecture unless the system also acquires a witness-bearing specialization calculus and typed mutation operators.

* `best_single_candidate`: **Institutional Multi-Level Norm System (IMNS)**

* `best_hybrid_candidate`: **Thin IMNS governance layer + Typed Hierarchical Abstract Machine (THAM) + Prioritized Defeasible Layer Logic (PDLL), with a small set of TDTL-style lifecycle monitors**

* `why`:

  **Why IMNS is the best single candidate:**
  It is the only standalone candidate here that naturally treats the constitutional layer as higher-order law about interpretation, enactment, amendment, inheritance, and fact-to-norm conversion. That matters because the note’s constitution is not just a bag of prohibitions; it also contains conflict-resolution rules and mutation law. IMNS preserves the distinction between law, posture, assignment, and state as different ontological types rather than merely different priorities.

  **Why the hybrid is better overall:**
  The architecture is really three problems, not one.

  1. **Who may create/modify/inherit norms?**
     That is an IMNS problem.

  2. **What machine transitions are legal?**
     That is a THAM problem.

  3. **How does a task-specific directive lawfully defeat a broader role default without violating constitution?**
     That is a PDLL problem.

  A minimal operational stack would therefore look like this:

  * **IMNS** defines validity: what counts as constitutional content, role content, task content, factual content, and authorized fact-to-norm bridges.
  * **THAM** defines execution: legal `spawn`, `compact`, `resume`, `swap_model`, `enter_maintenance`, `set_role`, `set_task`, `refresh_runtime`.
  * **PDLL** defines adjudication: strict/default/advisory force, specificity, and defeat, so that `checkpoint first` can legally override `explore/document first` when the latter is a role default rather than pseudo-constitutional law.
  * **TDTL-style monitors** should be used narrowly for invariants like “compaction never changes `C/R`” and “model swap never mutates constitution.”

  This hybrid is the only option here that cleanly explains the observed bug and also gives a plausible path to deterministic enforcement.

* `what_would_need_to_be_fixed_before_adoption`:

  1. **Define a witness for lawful specialization.**
     Do not ship “prefer the lawful-specialization reading” without a proof object. Require either a refinement witness, a valid enactment chain, or a defeasible-proof tree.

  2. **Add normative-force typing.**
     At minimum: `hard`, `default`, `advisory`, and `factual`. Without this, posture/law/task collapse.

  3. **Define a typed carry-over ontology.**
     Separate `fact`, `uncertain_fact`, `decision`, `blocker`, `delegated_obligation`, `environment_fact`, and `continuation_bridge` as different artifact classes.

  4. **Give law and role external identity.**
     Constitutional and role artifacts should survive by canonical reference/hash, not narrative paraphrase.

  5. **Make spawn and compaction packet construction legality-checked.**
     The packet builder must not be an ungoverned constitutional editor.

  6. **Define explicit fact-to-norm bridge rules.**
     Runtime facts may affect feasibility/admissibility, but only authorized bridge rules may create permissions or obligations.

  7. **Add a violation taxonomy.**
     Distinguish at least: `hierarchy_bug`, `worker_bug`, `inheritance_bug`, `role_under_instantiation`, `model_drift`, and `illegal_amendment`.

  8. **Constrain model-adapter instructions.**
     On swap, model-specific adapter text must itself be typed and audited so it does not function as covert constitutional rewrite.

  9. **Formalize the projection from mixed-source prompts into semantic layers.**
     Existing system/developer/collaboration/task/history artifacts are mixed. The projection rule must be explicit.

  10. **Treat U-lane heuristics as suspect by default.**
      Generic exploration/completeness/helpfulness biases should be presumed role-level defaults unless explicitly justified as constitutional law.

The blunt version: as written, the note is a good doctrine, not yet a hardened constitution.

---

## 7. `open_questions`

1. What exactly is a valid witness that `task_packet T` lawfully specializes `role R` rather than covertly overriding it?

2. Is `posture` fundamentally deontic, procedural, teleological, or heuristic? Until that is fixed, role semantics remain unstable.

3. Where do `open obligations` live: task layer, runtime baton, or a separate delegated-obligation artifact class?

4. What uncertainty taxonomy is required for bridge/memory artifacts so that compaction does not promote hypotheses into durable facts?

5. How should the system distinguish `impossible`, `inadmissible`, `prohibited`, `unassigned`, and `deferred` actions?

6. What is the canonical identity of constitutional/role artifacts across compaction and model swap: content hash, signed URI, versioned policy object, or something else?

7. How are mixed-source prompt channels projected into pure semantic layers when a single source artifact contains both law and posture?

8. Can a thread have multiple simultaneous tasks or nested tasks, or is the task layer strictly single-assignment?

9. What runtime evidence will let the orchestrator distinguish worker disobedience from role under-instantiation and from hierarchy miscomposition?

10. Who is authorized to open maintenance phase, and how are constitutional amendments versioned, rolled back, and made compatible with active executions?
