## irreducible_commitments

Holding ODEU fixed at the meta-axiom level, the note commits to a specific formal implementation thesis, not just a mnemonic stack.

1. There are four semantically distinct layers: constitutional as law, role as posture, task as assignment, and runtime as state.
2. Each layer has its own mutation/persistence law rather than mere scope: constitutional is immutable during ordinary execution, role changes only on role transition, task changes on assignment, and runtime is recomputed from current facts.
3. Lower layers are legal only as lawful specializations of upper layers; they may narrow but not rewrite.
4. Conflict handling is interpretive but asymmetric: prefer a reading that preserves specialization, and only declare true conflict when specialization is impossible.
5. Runtime is supposed to contribute mostly facts, not norms, and must not silently create permission.
6. Spawn, resume, compaction, and model swap are legality-sensitive transitions with layer-specific persistence rules: constitutional survives all of them; role survives ordinary execution and compaction; task is reassigned; runtime is refreshed from current facts plus explicit carry-over artifacts.
7. Compaction preserves continuity of execution, not continuity of law; constitutional and role are not to be re-authored as lossy recap.
8. The architecture claims a real bug class called hierarchy bug: e.g. generic exploratory heuristics placed too high can make a child worker inherit exploration pressure as if it were law, producing the “checkpoint first” versus “explore/document first” failure.
9. Constitutional change is reserved for an explicit maintenance phase and is illegal as an incidental byproduct of normal execution, compaction, or task completion.

Those are the non-optional commitments. Any candidate formalism that does not preserve them is not formalizing this note.

## hidden_assumptions

As written, the note is not yet a formal theory. Its critical terms do real work, but the witness conditions are absent. The text uses “lawful specialization,” “posture,” “runtime mostly facts,” “preserve hierarchy,” and “hierarchy bug” as if they were already semantically fixed. They are not.

1. **One slogan is standing in for several different relations.**
   “Lower layers narrow upper layers” sounds singular, but the layer objects are heterogeneous. Law, posture, task, and facts are not the same kind of thing. At minimum, the architecture needs different relations for normative refinement, procedural concretization, and factual instantiation.

2. **“Lawful specialization” has no non-circular definition.**
   The note assumes we can tell when specialization is possible, but gives no criterion. Candidates below show at least four incompatible readings: set inclusion, temporal strengthening, conservative update, and governance witness.

3. **There is an unstated parsing model.**
   “Prefer the reading that makes the lower layer a lawful specialization” presumes there is a bounded set of admissible readings. Without a canonical packet schema or compiler, this invites retrospective rationalization.

4. **Posture is assumed to be defeasible, but not marked as such.**
   The anchor case only counts as a hierarchy bug if “explore/document first” is a defeasible role heuristic rather than a coequal obligation. The note relies on that, but does not formalize it.

5. **The task layer is secretly two things.**
   The note says task is replaced on assignment, yet compaction carries “current task state” and “open obligations.” That implies a split between task charter and task residual. Without that split, compaction either mutates task law or smuggles norms into runtime.

6. **Runtime is not cleanly factual in the note’s own wording.**
   “Current facts” is one thing. “Currently admissible state,” “accepted recent decisions,” and “open obligations” are another. Those are already norm-adjacent. The note forbids runtime-to-law contamination while simultaneously relying on runtime artifacts that can exert normative force.

7. **Interpretation order is being mistaken for control order.**
   The note says normal execution resolves constitutional, then role, then task, then runtime. But the motivating case requires task order to dominate generic role heuristics. Therefore the note is assuming, without saying, that semantic validation order is not the same as action-selection order.

8. **There is no selection semantics among multiple legal traces.**
   Even if C, R, T, and S are jointly consistent, many actions may remain legal. What picks one? Without an explicit scheduler semantics, model priors and overlays do the picking, and the hierarchy becomes post hoc interpretation rather than prediction.

9. **Conflict detection lacks a witness surface.**
   To classify “true conflict” versus “lawful specialization,” the system needs evidence: unsatisfiable trace set, missing refinement proof, unmatched counts-as witness, or equivalent. The note asserts the distinction without operational criteria.

10. **Stable source, stable reference, and exact carry-over are not equivalent.**
    Stable source text reinterpreted by a different model is not stable law; it is stable prose. The note treats several preservation modes as if they were interchangeable. They are not.

11. **The whitelist assumption is stronger than it looks.**
    The note assumes parent runtime phenomenology can be removed while preserving only factual baton state. But many “facts” are behavior-shaping: blockers, recent focus, unresolved questions, accepted decisions.

12. **Model-family bias is externalized without a formal home.**
    The note admits model swap may require model-specific instructions and warnings, but does not say whether those are law, role, task, runtime, or a separate adapter artifact. That is a hidden fifth object.

13. **Nominal role labels are assumed not to exist.**
    The theory requires a real role packet. If “researcher” is just a label with no substantive packet, then the role layer is decorative, and the base/model prior fills the vacuum.

14. **Collaboration mode and autonomy overlays are assumed to fit inside role.**
    The current mapping places collaboration-mode instructions in role. That may be false. An autonomy overlay can cross-cut task dispatch, salience, and stopping behavior without behaving like posture.

15. **Maintenance phase is assumed to be enforceable and isolatable.**
    The note relies on a distinct constitutional-review mode. It does not say how phase boundaries are represented, authorized, or prevented from leaking into normal execution.

16. **Hierarchy bug versus worker bug is assumed to be diagnostically meaningful.**
    That requires a falsifiable test. If the classification cannot be made before looking at the output, the distinction is interpretive rhetoric, not runtime doctrine.

## candidate_family

These are competing formal implementation candidates. Their differences expose the note’s hidden assumptions.

### C1. Monotone Specialization Calculus

* `name`: Monotone Specialization Calculus
* `formal_style`: Order-theoretic constraint calculus over execution traces.
* `core_idea`: Each layer denotes a set of admissible traces; lower layers are legal iff they only shrink that set.
* `formal_primitives`: Action alphabet `A`; traces `τ ∈ A*`; predicates `φ` over traces; specialization order `φ1 ⪯ φ2` iff `Tr(φ1) ⊆ Tr(φ2)`.
* `judgment_forms`: `τ ⊨ φ`; `φ1 ⪯ φ2`; `legal(C,R,T,S)`.
* `main_axioms_or_transition_rules`: `R ⪯ C`; `T ⪯ (C ∧ R)`; `Facts(S)` may only eliminate traces; legality requires `Tr(C ∧ R ∧ T ∧ Facts(S)) ≠ ∅`.
* `how_layers_are_represented`: Constitutional, role, and task are trace predicates; runtime is a factual filter on those traces.
* `how_narrowing_is_represented`: Set inclusion on admissible traces.
* `how_inheritance_refresh_is_represented`: Runtime is rebuilt each turn from environment/history/whitelist while C/R/T persist unless explicitly replaced.
* `how_spawn_is_represented`: Child config `<C, R' or R, T_child, whitelist(S_parent)>`.
* `how_compaction_is_represented`: C and R preserved by reference; T and S replaced by residual predicates over the remaining suffix.
* `how_resume_model_swap_is_represented`: Same predicates, refreshed factual filter, optionally new evaluator.
* `what_counts_as_illegal`: Any lower-layer predicate that enlarges admissible traces or any compaction that rewrites C/R.
* `what_counts_as_unrepresentable`: Soft heuristics, salience, model priors, and rhetorical posture not reducible to predicates.
* `main_strength`: Cleanest possible formal meaning of “narrowing.”
* `main_failure_risk`: Too coarse for ordered obligations and too idealized for real runtime behavior.

### C2. Temporal-Deontic Trace System

* `name`: Temporal-Deontic Trace System
* `formal_style`: Temporal/deontic logic over action traces.
* `core_idea`: Layers contribute obligations, prohibitions, permissions, and defaults over time-indexed traces.
* `formal_primitives`: Time points; actions; traces; `Oφ`, `Fφ`, `Pφ`; conditional norms `ψ ⇒ Oφ`; temporal operators like `before`, `next`, `until`, `prefix`.
* `judgment_forms`: `τ,t ⊨ n`; `Active(C,R,T,S)`; `conflict(N)`; `supports(n_low, n_high)`.
* `main_axioms_or_transition_rules`: Constitutional norms are hard; role norms are posture defaults; task norms are local ordered obligations; runtime facts instantiate conditions but do not author norms.
* `how_layers_are_represented`: C/R/T are tagged norm sets; S is a fact set that activates conditional norms.
* `how_narrowing_is_represented`: Deadline tightening, condition instantiation, and temporal concretization without adding unsupported permissions.
* `how_inheritance_refresh_is_represented`: Recompute active norms each turn by re-instantiating conditionals from refreshed runtime facts.
* `how_spawn_is_represented`: Inherit C; inherit/replace R; install new T; start new trace with whitelisted facts and exportable residual obligations.
* `how_compaction_is_represented`: Convert past-satisfied obligations into residual norms over the future suffix.
* `how_resume_model_swap_is_represented`: Reconstruct trace prefix and re-evaluate active norms under refreshed runtime.
* `what_counts_as_illegal`: Unsupported permission, unresolved hard conflict, or runtime fact directly introducing a norm.
* `what_counts_as_unrepresentable`: Nominal role labels, latent model priors, and untyped overlays.
* `main_strength`: Best native account of the anchor case, because “checkpoint first” is a prefix obligation and “explore first” can be represented as a defeasible posture default.
* `main_failure_risk`: Extremely fragile unless the architecture explicitly separates hard norms, defaults, and permissions.

### C3. Typed Environment LTS

* `name`: Typed Environment LTS
* `formal_style`: Labeled transition system with typed environment frames.
* `core_idea`: The runtime is a machine over typed frames `C,R,T,S`; legality comes from what each frame type is allowed to contain and how the scheduler consults them.
* `formal_primitives`: Frame types; slot schemas; actions; store; scheduler; whitelist relation; effect annotations.
* `judgment_forms`: `wf(C,R,T,S)`; `step(cfg,a,cfg')`; `typed(x:k)`; `exportable(s)`.
* `main_axioms_or_transition_rules`: Only C may hold hard execution guards; R may hold heuristics/defaults; T may hold ordered obligations and stop conditions; S may hold only approved fact kinds.
* `how_layers_are_represented`: Four explicit frames with typed slots.
* `how_narrowing_is_represented`: Downward-compatible slot filling plus dispatch precedence constraints.
* `how_inheritance_refresh_is_represented`: S is rebuilt each turn from live environment and approved carry-over after type-checking.
* `how_spawn_is_represented`: Create new frame stack with inherited C, inherited/replaced R, fresh T, fresh S plus whitelisted exported facts.
* `how_compaction_is_represented`: Preserve C/R by stable identity; serialize residual T and S into typed artifacts.
* `how_resume_model_swap_is_represented`: Deserialize frames under same C/R/T identities; install refreshed runtime store and optional model adapter field.
* `what_counts_as_illegal`: Normative token in S, missing required packet, or disallowed frame mutation.
* `what_counts_as_unrepresentable`: Semantic equivalence of paraphrases, hidden priors not surfaced in slots.
* `main_strength`: Operationally close to a real runtime stack.
* `main_failure_risk`: Type separation alone does not guarantee semantic separation.

### C4. Dynamic Inheritance/Update Logic

* `name`: Dynamic Inheritance/Update Logic
* `formal_style`: Modal/dynamic logic with nested updates.
* `core_idea`: Layers are context updates on a model of possible execution worlds; narrowing is world restriction that preserves upper truths.
* `formal_primitives`: Kripke model `M`; worlds `W`; valuations; update operators; accessibility relations per layer.
* `judgment_forms`: `M,w ⊨ φ`; `legal_update(U,Θ)`; `preserves_upper(U,Θ)`.
* `main_axioms_or_transition_rules`: Lower-layer update is legal iff it only restricts worlds and does not falsify upper-layer truths in shared vocabulary.
* `how_layers_are_represented`: Constitutional, role, task, and runtime are nested update modalities or nested context restrictions.
* `how_narrowing_is_represented`: Conservative world restriction.
* `how_inheritance_refresh_is_represented`: Refresh runtime by updating the state submodel while leaving upper modalities fixed.
* `how_spawn_is_represented`: Child is a copied submodel with inherited upper contexts, replaced task context, and fresh runtime context.
* `how_compaction_is_represented`: Quotient the state/history model by an equivalence relation intended to preserve relevant truths.
* `how_resume_model_swap_is_represented`: Re-evaluate same layer formulas under a translated evaluator or updated submodel.
* `what_counts_as_illegal`: Any update that expands accessible worlds, changes upper truths, or lets runtime updates alter upper modalities.
* `what_counts_as_unrepresentable`: Behavioral salience not encoded in the language, hidden search policies, tool-effect semantics outside the vocabulary.
* `main_strength`: Very sharp on “do not rewrite upper law.”
* `main_failure_risk`: Can preserve theory while losing behavior.

### C5. Institution-Style Multi-Level Norm System

* `name`: Institution-Style Multi-Level Norm System
* `formal_style`: Multi-level governance / institution theory.
* `core_idea`: Constitutional norms govern the validity of lower-layer norms via constitutive and counts-as rules.
* `formal_primitives`: Brute facts; institutional facts; norms; counts-as relation; governance relation; enactment validity.
* `judgment_forms`: `valid_norm(n,level,ctx)`; `counts_as(x,y)`; `violates(agent,n)`.
* `main_axioms_or_transition_rules`: A role norm is valid only if chartered by constitutional governance; a task norm is valid only if enacted under a valid role/constitutional charter; runtime facts may create institutional facts but not new norms except through pre-authorized constitutive rules.
* `how_layers_are_represented`: C/R/T are nested institutions or charters; S is brute-fact context plus derived institutional facts.
* `how_narrowing_is_represented`: Concrete lower norms are lawful only when witnessed as concretizations of higher norms.
* `how_inheritance_refresh_is_represented`: Recompute institutional facts each turn from current brute facts and surviving charters.
* `how_spawn_is_represented`: Spawn creates a subsidiary institutional instance inheriting governors and receiving a new mandate.
* `how_compaction_is_represented`: Preserve governing charters by reference; compact only brute and institutional state.
* `how_resume_model_swap_is_represented`: Reinterpret brute facts under the same governing institutions, with optional translation of institutional vocabulary.
* `what_counts_as_illegal`: Lower-level norm without a governance witness, brute fact directly authoring permission, or missing charter for a claimed role.
* `what_counts_as_unrepresentable`: Fine-grained ordered execution and low-level scheduling without additional temporal machinery.
* `main_strength`: Best separation of facts, institutional facts, and norm validity.
* `main_failure_risk`: Counts-as can become a post hoc justification machine.

### C6. Register Abstract Machine with Verified Adapters

* `name`: Register Abstract Machine with Verified Adapters
* `formal_style`: Small-step abstract machine with proof-carrying packets and adapter checks.
* `core_idea`: The runtime has explicit registers for C, R, T, S, and adapter/overlay state; sensitive transitions require proof obligations.
* `formal_primitives`: Packet ASTs; hashes; registers; proofs of refinement; adapter certificates; task IDs; scoped exports.
* `judgment_forms`: `wf(cfg)`; `Π ⊢ R ⪯ C`; `Π ⊢ T ⪯ (R,C)`; `step_ok(cfg,a)`; `adapter_ok(α)`.
* `main_axioms_or_transition_rules`: Ordinary execution cannot mutate C; spawn/compaction/resume/model-swap are explicit instructions with legality side conditions; only maintenance mode can update C.
* `how_layers_are_represented`: Immutable packet references in registers plus typed runtime store and adapter register.
* `how_narrowing_is_represented`: Proof-carrying refinement between compiled packets.
* `how_inheritance_refresh_is_represented`: Rebuild S from canonical fact logs and approved exports while C/R/T hashes persist.
* `how_spawn_is_represented`: `spawn` installs inherited C, inherited/replaced R, new T, fresh S, and only scoped whitelisted exports.
* `how_compaction_is_represented`: `compact` may serialize task residuals and facts; C/R packet identities must remain unchanged.
* `how_resume_model_swap_is_represented`: `resume` reloads packet identities; `swap` requires adapter proof or emits an explicit degraded-trust state.
* `what_counts_as_illegal`: Missing refinement proof, packet-hash mutation outside maintenance, untyped overlay, or scoped export violation.
* `what_counts_as_unrepresentable`: Free prose without a compiler, uncertified human interpretations, and latent model behavior not surfaced in the adapter contract.
* `main_strength`: Strongest operational enforcement story.
* `main_failure_risk`: It only works if the compiler, ontology, and adapter proofs are themselves trustworthy.

## countermodels

Common anchor symbols:

* `C0`: constitution includes safety boundaries, epistemic discipline, and a requirement not to silently widen permission.
* `Rexp`: generic role posture says to explore/document before acting.
* `Tchk`: child task says checkpoint first, then inspect.
* `Smap`: runtime includes available tools and parent-side repo-mapping context.
* `M1/M2`: two model families with different default salience or policy under ambiguity.

This anchor is directly lifted from the note’s own motivating failure.

### C1. Monotone Specialization Calculus

1. **Ordered-obligation underfit.**
   Config: encode `Rexp` as “explore before edit” and `Tchk` as “checkpoint before edit.” The intersection still admits both `explore; checkpoint; edit` and `checkpoint; explore; edit`.
   Why it breaks: the anchor requires checkpoint to be first, not merely before edit.
   Severity: local but central; it misses the motivating bug.
   Repair: add prefix/temporal obligation operators or a separate scheduler semantics.

2. **Hidden widening by ontology loss.**
   Config: constitutional law forbids network side effects; task says “use any available evidence tool”; runtime marks `sync_docs` merely as `tool_use`.
   Why it breaks: the lower layer appears narrowing, but the abstraction hides the forbidden effect.
   Severity: fatal unless action/effect ontology is explicit.
   Repair: effect typing for tools plus constitutional predicates over effects, not tool names.

3. **Compaction paraphrase drift.**
   Config: compaction carries forward a paraphrase of C/R rather than exact compiled predicates.
   Why it breaks: the formal system only protects what is preserved as the predicate; paraphrase can widen admissible traces while still sounding faithful.
   Severity: fatal for the note’s anti-drift claim.
   Repair: preserve upper-layer identity by canonical object reference, not summary text.

### C2. Temporal-Deontic Trace System

1. **Role default hardens into law.**
   Config: `Rexp` is encoded as hard `O(explore_first)` instead of defeasible default; `Tchk` is hard `O(checkpoint_first)`.
   Why it breaks: the anchor becomes an ordinary norm clash or a worker violation, not a hierarchy bug caused by mislayering.
   Severity: fatal unless posture is typed as defeasible.
   Repair: stratify norms into hard law, role defaults, and task-ordered obligations.

2. **Runtime fact becomes permission.**
   Config: C forbids risky tool use unless approved; R says “when evidence is needed, use available tools”; S says evidence is needed and tool `sync_docs` is available.
   Why it breaks: availability plus obligation can induce de facto permission even though no approval fact exists.
   Severity: fatal for the fact/norm barrier.
   Repair: forbid permission introduction from feasibility alone; permissions must come from explicit upper-layer authorization.

3. **Model swap changes behavior while theory stays fixed.**
   Config: same C/R/T formulas under `M1` and `M2`; `M2` treats role-default violations as costlier and explores before checkpoint.
   Why it breaks: the formalism assumes an ideal evaluator, so the behavioral drift is invisible.
   Severity: fatal for operational adequacy, though not for pure logic.
   Repair: add a first-class execution policy or verified model adapter semantics.

### C3. Typed Environment LTS

1. **Nominal-role collapse.**
   Config: `R.label = researcher`, but the role packet is empty or missing substantive slots.
   Why it breaks: the system says a role exists, but behavior falls through to base instructions or model prior.
   Severity: fatal.
   Repair: role existence must require a validated non-empty packet, not a label.

2. **Overlay escape.**
   Config: `overlay.autonomy = high` lives outside C/R/T/S and the scheduler consults it before task obligations.
   Why it breaks: the four-layer theory cannot localize the cause even though behavior is systematically changed.
   Severity: fatal to the completeness of the layer model.
   Repair: formalize overlays as typed packets subject to the same refinement rules, or prohibit them.

3. **Phenomenology leak through factual salience.**
   Config: parent exports `recent_focus = map_repo` and `unknown_topology = true` as facts; child task is still `Tchk`.
   Why it breaks: those facts bias the child toward exploration before checkpoint even without explicit norms.
   Severity: fatal to a naive factual whitelist.
   Repair: split descriptive facts from planner-salience carriers and strip or scope the latter.

### C4. Dynamic Inheritance/Update Logic

1. **Vocabulary-extension widening.**
   Config: task update introduces a new predicate `productive_prep` and restricts worlds to those where exploration counts as productive.
   Why it breaks: the update preserves upper truths in the old vocabulary while covertly expanding what the lower layer can justify.
   Severity: fatal unless vocabulary extension is controlled.
   Repair: require definitional extension proofs or a closed vocabulary.

2. **Bisimulation preserves theory, not action.**
   Config: compaction quotients two histories that are modally equivalent on all law formulas but differ in next-step salience.
   Why it breaks: the compacted state is logically equivalent but operationally different; the agent explores instead of checkpointing.
   Severity: fatal for the “continuity of execution” promise.
   Repair: use strategy-preserving equivalence, not mere formula-preserving equivalence.

3. **Maintenance-history leak.**
   Config: a constitutional maintenance update occurs, and the resume evaluator conditions on the recent maintenance event.
   Why it breaks: phase history changes ordinary execution despite no further law change.
   Severity: local if erasable, fatal if systemic.
   Repair: separate maintenance meta-history from ordinary runtime interpretation.

### C5. Institution-Style Multi-Level Norm System

1. **Counts-as opportunism.**
   Config: constitutional norm is abstract diligence; role charter says exploring counts as diligence; task charter says checkpointing counts as diligence under risk.
   Why it breaks: both actions become equally ratifiable as “lawful specialization.”
   Severity: fatal unless concretization witnesses are constrained.
   Repair: require typed, uniqueness-sensitive concretization schemas with precedence rules.

2. **Constitutive backdoor from facts to permission.**
   Config: `available(toolX)` counts as `permitted(use toolX)` through an institutional rule.
   Why it breaks: the formal separation between brute facts and norms is defeated from inside the theory.
   Severity: fatal.
   Repair: brute facts may activate pre-existing permissions, not author new ones; constitutive rules to permission require constitutional warrant.

3. **Procedural underfit.**
   Config: the task charter says “checkpoint first, then explore,” but the institution only validates that both obligations exist.
   Why it breaks: the formalism validates the mandate but does not force the prefix order that matters in runtime.
   Severity: local but central.
   Repair: combine the institution layer with a temporal task semantics.

### C6. Register Abstract Machine with Verified Adapters

1. **Compiler smuggling.**
   Config: the prose compiler misclassifies “explore/document first” as constitutional rather than role-local.
   Why it breaks: the machine can prove legality relative to the wrong packet hierarchy.
   Severity: fatal.
   Repair: the compiler itself must be typed, constrained, and auditable, ideally with round-trip source witnesses.

2. **Adapter proof too weak.**
   Config: model swap adapter proves packet-clause preservation but not next-action preservation under ambiguity.
   Why it breaks: the new model still explores before checkpoint, yet the swap is certified.
   Severity: fatal for the note’s model-swap claim.
   Repair: adapter obligations must target observational or policy equivalence, not mere clause preservation.

3. **Scoped obligation leak.**
   Config: parent exports `open_obligation(map_repo)` tagged as exportable, child task is a new checkpoint task.
   Why it breaks: proof-carrying export still leaks irrelevant normative momentum into the child.
   Severity: local but common.
   Repair: every exported obligation needs scope tags and subsumption checks against the child task.

## attack_matrix

Legend: `strong` = native traction; `partial` = workable only with extra machinery; `weak` = fragile or incomplete; `cannot represent cleanly` = outside the candidate’s natural semantics.

| candidate                                           | hierarchy bug detection | inheritance bug detection | compaction-law drift | nominal-role collapse | false narrowing / hidden widening | runtime-to-law contamination | model-swap discontinuity | prose ambiguity tolerance |
| --------------------------------------------------- | ----------------------- | ------------------------- | -------------------- | --------------------- | --------------------------------- | ---------------------------- | ------------------------ | ------------------------- |
| C1 Monotone Specialization Calculus                 | partial                 | partial                   | partial              | weak                  | partial                           | partial                      | cannot represent cleanly | weak                      |
| C2 Temporal-Deontic Trace System                    | strong                  | partial                   | partial              | weak                  | partial                           | partial                      | weak                     | weak                      |
| C3 Typed Environment LTS                            | partial                 | strong                    | strong               | strong                | partial                           | strong                       | weak                     | partial                   |
| C4 Dynamic Inheritance/Update Logic                 | partial                 | partial                   | strong               | weak                  | partial                           | partial                      | partial                  | weak                      |
| C5 Institution-Style Multi-Level Norm System        | partial                 | partial                   | partial              | strong                | partial                           | strong                       | cannot represent cleanly | partial                   |
| C6 Register Abstract Machine with Verified Adapters | strong                  | strong                    | strong               | strong                | strong                            | strong                       | partial                  | cannot represent cleanly  |

The pattern is harsh: no single candidate is strong on both normative validity and behavioral continuity across model change. The note is strongest where the architecture talks about mutation law and weakest where it needs a predictive execution semantics.

## minimum_repairs

Without at least the following, this architecture is not formally serious enough to govern runtime. It is a disciplined memo, not yet a constitutional calculus.

1. **Replace the single slogan “lawful specialization” with typed refinement relations.**
   You need at least:

   * `role_refines(C,R)`
   * `task_refines(C,R,T)`
   * `state_instantiates(C,R,T,S)`
     These are not the same relation.

2. **Require material packets, not labels.**
   Constitutional, role, and task must exist as typed artifacts with stable identities. A role label without a packet is illegal, not merely weak.

3. **Split task into charter and residual.**
   The note already relies on this. `TaskCharter` is the assignment; `TaskResidual` carries open obligations, progress, and pending checkpoints. Otherwise compaction either mutates law or smuggles norms into runtime.

4. **Define validation order separately from action-selection order.**
   Validation can be `C → R → T → S`. Action selection cannot naively be that order. Task-ordered obligations must control the next step whenever they are determinate; role posture should only fill underdetermined choices.

5. **Formalize a runtime contamination firewall.**
   Runtime store needs at least three types:

   * descriptive facts
   * scoped residual obligations
   * banned or separately-typed salience/phenomenology carriers
     “Facts only” is too weak; many facts are action-shaping.

6. **Make upper-layer identity exact across compaction, resume, and swap.**
   Constitutional and role must survive by canonical object identity or canonical AST/hash, not by prose recap and not by “stable source text” alone.

7. **Define an inheritance/refresh algebra.**
   Spawn, resume, compaction, and model swap need explicit operators over packets and stores, including whitelist types, task-id scoping, and subsumption tests for exported obligations.

8. **Add conflict-witness conditions and a bug classifier.**
   A hierarchy bug should mean something testable: missing refinement proof, ambiguous concretization witness, illegal packet content, or unsatisfiable active stack. Without that, “hierarchy bug” is retrospective storytelling.

9. **Introduce an explicit adapter/overlay formalism.**
   Model-family instructions, collaboration mode, and autonomy overlays cannot remain informal residue. Either absorb them into typed role packets with refinement proofs, or admit an explicit fifth artifact class.

10. **Formalize maintenance phase as a privileged meta-transition.**
    Constitutional changes need authorization, provenance, and isolation from ordinary execution. Otherwise “immutable during execution” is performative.

11. **Constrain the action/effect ontology.**
    Hidden widening is impossible to police if the tool/action vocabulary is open-ended or effect-oblivious.

12. **Compile prose into schema, or do not ratify the doctrine.**
    The note’s current prose is too elastic. If you do not accept schema, packet ASTs, and a constrained compiler, almost every conflict can be rationalized after the fact.

The shortest honest verdict is this: the current design does not survive as a stand-alone formal doctrine. It survives only as a direction that needs typed refinement, scoped transition laws, and an explicit contamination barrier.

## best_backbone_vs_best_runtime_model

**Best conceptual backbone:** C5, the Institution-Style Multi-Level Norm System.

Why: it best captures the note’s central constitutional claim that lower-layer norms are valid only under higher-layer governance, and it is the cleanest way to separate brute facts from normative authority. It also makes the note’s diagnosis of role-colored base instructions intelligible: that is a governance error, not just output drift.

**Best runtime-operational model:** C6, the Register Abstract Machine with Verified Adapters.

Why: only a machine with explicit packet identities, scoped exports, immutable upper registers, and guarded transition instructions can actually enforce the mutation contract around spawn, compaction, resume, and model swap.

**Best local semantics for the motivating anchor case:** C2, the Temporal-Deontic Trace System.

Why: “checkpoint first” is inherently temporal. Any runtime model that cannot express prefix obligations will misclassify the anchor or underdetermine it.

**Is the best answer a hybrid?** Yes, and likely unavoidably.

The least fragile stack is:

* C5 for norm validity and fact/norm separation,
* C2 for ordered task obligations,
* C6 (with C3’s typed-frame flavor) for actual runtime execution and mutation enforcement.

A pure single-formalism answer is weaker than the note requires. The theory is doing three jobs at once: validating lower-layer authority, sequencing obligations, and enforcing transition legality. Different candidates are best at different jobs.

## what_would_falsify_this_architecture

The architecture itself would be seriously undermined by any of the following.

1. **No non-circular refinement relation can be defined.**
   If “lawful specialization” cannot be stated except by appealing back to intuitive judgment, the architecture has no legality core.

2. **Role and law cannot be behaviorally separated in live systems.**
   If generic role heuristics placed in constitutional packets behave indistinguishably from true law, and there is no reliable test to separate them, the layer distinction is not operationally real.

3. **Compaction cannot preserve law without paraphrase.**
   If upper layers must be reconstructed as recap rather than preserved by canonical identity, then compaction-law drift is structural, not accidental.

4. **Fact-only child inheritance is either impossible or non-functional.**
   If effective child execution always depends on inherited salience, local momentum, or implicit policy traces, then “fresh runtime plus whitelisted facts” is false as a runtime doctrine.

5. **Runtime facts inevitably become permission in practice.**
   If tool availability, blockers, or continuation artifacts repeatedly function as de facto authorization despite formal bans, the runtime/law boundary is not robust.

6. **Model swap causes persistent behavior drift that no adapter can bound.**
   If two models given identical C/R/T/S artifacts still show constitutionally relevant divergence and no practical adapter/test regime predicts it, then “preserve hierarchy across model swap” is mostly ceremonial.

7. **Hierarchy bug versus worker bug has no predictive value.**
   A concrete falsification test exists: move exploratory heuristics out of constitutional artifacts into role packets, keep task packets explicit, and see whether the anchor failure rate drops materially. If it does not, the architecture is misdiagnosing the phenomenon.

8. **The four-layer story collapses into more layers.**
   If task residuals, model adapters, and autonomy overlays all need separate formal treatment, and cannot be cleanly housed in the existing four without contamination, then the architecture as stated is incomplete.

9. **Refinement checking is intractable on the allowed packet language.**
   If the only expressive packet language that captures real prompts makes legality checking undecidable or too costly to use, the architecture cannot function as runtime doctrine without much stronger restriction.

10. **Behavioral equivalence cannot be tied to law identity.**
    If preserving canonical law objects across compaction and resume still does not preserve constitutionally relevant behavior within any acceptable tolerance, then the layer model is not the main causal structure.

## open_questions

1. What exactly is a role packet: defaults, search policy, narrative tone, second-order norm bundle, or some mixture?
2. Should `TaskResidual` be a sublayer of task or a separate execution-state artifact with norm-bearing semantics?
3. What is the minimal action/effect ontology needed to detect hidden widening through tools and environment features?
4. What equivalence notion should compaction preserve: formula truth, scheduler state, policy distribution, or bounded behavioral tolerance?
5. Can model-family adapters be certified intensionally, or do they need empirical regression suites over constitutionally sensitive traces?
6. Are collaboration mode and autonomy overlays genuinely roles, or are they a distinct control stratum?
7. What evidence threshold should trigger “true conflict” rather than “underdetermined but legal”?
8. How constrained must the packet language be to keep refinement auditable?
9. Can the architecture remain four-layer once adapters, overlays, and task residuals are made explicit?
10. Which failures should count as constitutional violations versus ordinary suboptimal execution once the stack is fully typed?
