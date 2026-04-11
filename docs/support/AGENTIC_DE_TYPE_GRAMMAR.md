Below is a type-level framework for MORPHIC UX in agentic development environments.

The core separation is this:

An agentic DE has an upstream governed semantic grammar.
Its UX is a downstream projection layer.
A resident agent may negotiate projections, but only inside a lawful morphic space.
That morphic space is constrained not only by semantic invariants, but also by user competence invariants: spatial memory, muscle memory, evidence-tracking ability, and action-boundary awareness.

A compact formalization:

* Let `Σ` be the governed semantic state of the agentic DE.
* Let `U` be a user cognitive profile packet.
* Let `M` be a task/mode packet.
* Let `Γ` be governance constraints.
* A UX projection is `Π(Σ, U, M, Γ) -> V`.
* A morph is `μ: V1 -> V2`.

A morph `μ` is lawful only if:

1. It preserves the semantic distinctions in `Σ`, especially authority, evidence, provenance, lineage, handoff, and capability.
2. It preserves critical anchor continuity, or performs explicit migration.
3. It does not materially degrade learned user competence without notice and consent.
4. It satisfies mode- and risk-dependent evidence and boundary visibility constraints.

A useful shorthand:

**The grammar is the type system of interaction.
The UX is the renderer.
Semantic laundering is UI-level type forgery.**

---

## AGENTIC_DE_TYPE_GRAMMAR

### 1. Formal project-type definition

An agentic DE is a governed mixed-initiative project workspace in which a human and a resident agent collaborate over a project artifact graph under explicit capability, evidence, provenance, execution, lineage, and handoff constraints.

It is not primarily a code editor, a chat tool, or a terminal. It is a semantic operating field for:

* orienting within a project,
* expressing typed intent,
* inspecting artifacts,
* proposing and applying changes,
* executing workflows and runtime actions,
* reviewing and adjudicating changes,
* dispatching work across boundaries,
* auditing provenance afterward.

At the type level, the primitive objects are not panes. They are things like:

* workspace scope,
* artifact identity,
* target selection,
* capability state,
* advisory object,
* evidence object,
* candidate change,
* applied change,
* runtime process,
* workflow instance,
* version lineage,
* review packet,
* handoff event,
* environment identity.

And the primitive verbs are not just open/edit/save. They are:

* orient,
* inspect,
* ask,
* propose,
* apply,
* execute,
* compare,
* review,
* approve/reject,
* dispatch,
* audit,
* recover/revert,
* configure.

### 2. Core interaction grammar

The minimal interaction cycle of an agentic DE is:

`orient -> intend -> interpret -> inspect/propose -> evidence -> gate -> act -> observe -> trace`

That cycle branches into distinct typed subcycles.

A query cycle:

`intent(query) -> retrieval/interpretation -> advisory return -> evidence attachment`

A proposal cycle:

`intent(change) -> candidate change -> diff/provenance -> authority gate -> apply or reject -> lineage update`

An execution cycle:

`intent(run) -> harness/provider/config bind -> capability check -> execution -> runtime stream -> result -> provenance update`

A review cycle:

`target selection -> evidence + recommendation -> adjudication -> approval/rejection -> review state update`

A dispatch cycle:

`target packaging -> handoff boundary disclosure -> send/route -> receipt/trace`

An audit cycle:

`select event/change/run -> provenance walk -> evidence traversal -> reconstruction`

This grammar is the upstream stabilizer that makes morphic UX possible. Once these types and transitions are fixed, multiple lawful UX schemas can project them differently.

### 3. Semantic roles of the required surfaces

The required surfaces are not interchangeable panes. Each one exists because the grammar demands a semantic role.

**Transcript / conversation lane**
This is the temporal ledger of interpretation, advice, proposals, user decisions, and references into artifacts or evidence. It preserves alignment history and deictic continuity. It is not the sole source of truth for project state; it is the coordination ledger.

**Composer / command entry**
This is the typed intent-entry locus. Its job is not merely text capture. It binds user intent to an interpreter and an operation class. In an agentic DE, that binding may target the resident agent, a workflow engine, a search system, a shell, or a review action. Therefore the composer has a semantic obligation: target clarity. Ambiguous composer targeting is a major laundering risk.

**Project / workspace context**
This is the referential frame against which deictic inputs like “fix this,” “run tests,” or “review these changes” become meaningful. Workspace context is broader than an open folder. It includes active scope, selected targets, branch or lineage position, environment identity, and available capabilities.

**File/context explorer**
This is a navigation projection over the artifact and context graph. It changes focus and scope. It should not itself redefine the meaning of the selected object. In agentic DEs, “context explorer” is broader than a file tree; it may include symbols, runs, failures, traces, generated artifacts, or review packets.

**Artifact readers**
These materialize selected artifacts into inspectable form. They can be read loci, edit loci, compare loci, or annotation loci. Their semantic responsibility is object identity preservation. When a file, diff, log, config, or generated artifact is shown in different forms, the user must still be able to tell that it is the same object.

**Diff / provenance surfaces**
These disclose deltas and causality. In agentic DEs, diff alone is insufficient. A change also needs provenance: where it came from, which instruction or workflow produced it, which evidence supported it, what tests or runs relate to it, and what authority allowed it.

**Terminal / runtime surfaces**
These are authoritative process-output surfaces bound to concrete execution substrate. Agent summaries of runtime are advisory. Terminal output, run state, error streams, and process identity are primary runtime evidence and must remain inspectable as such.

**Git / version surfaces**
These expose lineage and reversibility. They distinguish workspace state from staged state, committed lineage, branch position, merge relations, and recovery points. Transcript time and version time are not the same thing; both must remain legible.

**Review dispatch surfaces**
These package candidate work for other humans, agents, or downstream systems. Their semantic job is handoff disclosure: what is being sent, to whom or where, from what state, with what evidence, under what authority.

**Workflow launch surfaces**
These instantiate repeatable procedures. They are not just “buttons.” They are procedure binders: they bind parameters, scope, provider/harness, capability, and expected outputs to a concrete workflow instance.

**Harness / provider / config / build identity surfaces**
These reveal the interpretive substrate. Output meaning depends on them. A run result, generation, or advisory cannot be understood correctly if the user cannot tell which harness, provider, config, or build identity produced it.

**Explicit capability boundaries such as writes enabled**
This is the deontic control plane. It communicates what is currently permitted: read, propose, write, execute, commit, dispatch, configure. “Writes enabled” is only one visible slice of a larger capability vector.

**Evidence and advisory-return surfaces**
These carry basis-for-trust. They include citations, raw logs, diff links, provenance chains, assumptions, uncertainty disclosures, trace links, and rationale. In low-risk modes, they may be less prominent. In review, audit, and high-risk modes, they become near-primary.

### 4. Stable semantic component family

The stable semantic family underneath all lawful agentic-DE projections can be stated more compactly as component roles:

1. **Intent Channel** — typed entry of requests, commands, and directives.
2. **Negotiation Ledger** — transcript of mixed-initiative coordination.
3. **Scope Frame** — workspace, target selection, and active referential context.
4. **Artifact Graph Navigator** — traversal of project objects and neighborhoods.
5. **Artifact Materializer** — readers/editors/comparators for project objects.
6. **Delta + Provenance Channel** — change disclosure and causal trace.
7. **Execution Channel** — runtime processes, outputs, failures, and states.
8. **Lineage Channel** — version graph, branch state, staging, recovery.
9. **Review + Handoff Channel** — adjudication and externalization boundaries.
10. **Procedure Channel** — workflow and reusable action graph instantiation.
11. **Identity Channel** — harness/provider/config/build disclosure.
12. **Capability Channel** — deontic status and action permissions.
13. **Evidence + Advisory Channel** — basis-bearing recommendations and inspections.

These are stable because they arise from the grammar, not from one chosen layout.

### 5. Invariant, semi-stable, and morphable components

The most rigorous way to classify movement is not by whole widget, but by **component contract**.

Each semantic component has three contracts:

* **Semantic contract** — what it means.
* **Retrieval contract** — how the user finds it.
* **Rendering contract** — how it is visually projected.

For agentic DEs:

**Semantic contract is invariant.**
The meaning of capability, evidence, runtime output, applied state, diff, review decision, or handoff cannot be rewritten by layout.

**Retrieval contract is usually semi-stable.**
The user should be able to rely on stable home zones, stable invocations, or stable summon paths. This is where spatial and motor memory live.

**Rendering contract is morphable.**
Size, salience, docking, peeking, grouping, spacing, density, and inline vs sidecar placement can change.

Examples:

* The **composer** is semantically invariant; its target clarity is invariant; its home zone is semi-stable; its width, compactness, and surrounding chrome are morphable.
* The **diff/provenance function** is semantically invariant; access to it is invariant; whether it appears inline, sidecar, docked, or fullscreen is morphable.
* The **capability boundary** is semantically invariant and action-adjacency-constrained; its badge size and visual emphasis are morphable.
* The **terminal/runtime channel** is semantically invariant when active; its persistence is semi-stable; its height and prominence are morphable.
* The **transcript ledger** is semantically invariant; its prominence is semi-stable; its density and collapse behavior are morphable.

So the sharp distinction is:

* **Invariant components** are invariant in semantic contract, and often in anchor obligation.
* **Semi-stable components** have stable retrieval obligations but mode-sensitive prominence or persistence.
* **Morphable components** are rendering-level degrees of freedom.

The mistake is to treat “component” as equivalent to “pane.” In a lawful morphic agentic DE, components remain semantically stable while their projection varies.

---

## USER_COGNITIVE_PROFILE_TAXONOMY

A user cognitive profile is not a personality sketch. It is a packet of interaction-relevant tolerances, dependencies, and costs that influence projection fit.

It should be treated as:

* dynamic rather than permanent,
* probabilistic rather than absolute,
* mode-sensitive rather than universal,
* inferable by behavior as well as stated preference.

A useful decomposition follows.

### 1. Perceptual load regulation

**Density tolerance**
How much concurrently visible semantic material remains workable.

**Visual clutter sensitivity**
How costly non-essential signals are, even when they are informationally accurate.

**Calm-surface preference**
How strongly the user benefits from low-background-arousal surfaces versus high-information control decks.

These are related but not identical. A user can tolerate density when it is tightly organized, while still being highly clutter-sensitive.

### 2. Compression versus explicitness

**Semantic compression tolerance**
How well the user can operate from summaries, abstractions, or compressed representations before inspecting raw materials.

**Evidence appetite**
How much underlying basis the user wants accessible or foregrounded before trust or action.

**Control explicitness preference**
How much the user needs named states, visible toggles, and explicit gates rather than inference and automation.

A user may have high compression tolerance and still have high evidence appetite. That user likes summaries, but not summary-only decision points.

### 3. Orientation and memory dependence

**Spatial-memory reliance**
How much the user depends on stable locations and neighborhoods to retrieve tools and maintain flow.

**Muscle-memory reliance**
How much the user depends on stable hotkeys, motor paths, and repeated action placement.

**Need for stable anchors**
How strongly the user needs fixed landmarks across mode shifts.

**Mode-switch cost sensitivity**
How expensive reorientation is when the interface reconfigures.

These are central in morphic systems. Spatial continuity is not only convenience; it is an operational safety property.

### 4. Working-set management

**Working-memory bandwidth**
How much unresolved context can be held while moving between surfaces.

**Pane simultaneity tolerance**
How comfortably the user can reason across multiple co-visible surfaces.

**Progressive disclosure preference**
How strongly the user prefers staged reveal instead of explicit concurrency.

**Context-retention dependence**
How much the user suffers when supporting context disappears and must be reopened.

A user with low simultaneity tolerance and high evidence appetite does not necessarily want “less evidence.” They often want evidence placed nearer to the decision, with fewer unrelated panes.

### 5. Risk and governance sensitivity

**Action-risk sensitivity**
How much the user wants warnings, gates, and confirmations around effectful operations.

**Action-boundary awareness dependence**
How strongly the user benefits from explicit cues that a boundary is being crossed: preview to apply, local to external, advice to execution.

**Trust-notice reliance**
How much uncertainty, capability, and identity disclosures need to be visible for comfortable action.

**Provenance-check tendency**
How often the user wants to inspect where a recommendation or change came from.

### 6. Interruption and negotiation style

**Interruption tolerance**
How much unsolicited projection proposal or agent guidance the user can absorb without losing flow.

**Abstract preference articulation ability**
How well the user can specify desired UX in advance.

This last variable matters because many users cannot tell you “I need a lower mode-switch cost and higher evidence adjacency.” They can, however, recognize a better projection when it is shown to them.

### 7. Important non-equivalences

Several dimensions should not be collapsed:

* Density tolerance is not evidence appetite.
* Clutter sensitivity is not calmness preference.
* Spatial-memory reliance is not muscle-memory reliance.
* Progressive disclosure preference is not low working-memory bandwidth.
* Control explicitness preference is not low trust in automation.

These distinctions matter because different lawful morphs solve different problems.

---

## TASK_MODE_PROFILE_SCHEMA

User profile and task mode are orthogonal.

A user profile describes **how the user handles interaction**.
A task mode describes **what semantic working set and deontic structure dominate the episode**.

The same user may need radically different projections across modes.

A useful task-mode decomposition for agentic DEs follows.

### 1. Exploration

Goal: orient in an unfamiliar project, dependency region, or problem space.

Projection demands: strong context frame, lightweight explorer, rapid artifact peeking, low-risk advisory guidance, stable anchors.

Dominant planes: context, artifact, negotiation.
Risk: low.
Failure mode: disorientation through excessive concurrency or hidden scope.

### 2. Drafting

Goal: create new code, text, config, or structure from partial intent.

Projection demands: composer and artifact surface near each other, enough source context nearby, low-friction advisory insertion, low review overhead until maturation.

Dominant planes: negotiation, artifact, context.
Risk: medium.
Failure mode: summary-heavy guidance that obscures actual artifact formation.

### 3. Code reading

Goal: understand existing artifacts.

Projection demands: artifact identity continuity, stable navigation, easy access to definitions/context, restrained mutation controls.

Dominant planes: artifact, context.
Risk: low.
Failure mode: chat or workflow surfaces stealing salience from the reading object.

### 4. Code editing

Goal: mutate existing artifacts with high local precision.

Projection demands: artifact centrality, local diff visibility, stable motor paths, write-boundary awareness, rapid recovery path.

Dominant planes: artifact, change, capability.
Risk: medium to high.
Failure mode: unstable layout or ambiguous apply behavior that breaks motor memory.

### 5. Debugging

Goal: explain failure and reach corrective action.

Projection demands: runtime output, error state, harness/build identity, relevant artifacts, recent diffs, and evidence concurrency.

Dominant planes: execution, artifact, change, identity.
Risk: medium to high.
Failure mode: fragmented evidence, especially logs detached from config or recent change context.

### 6. Review / adjudication

Goal: decide whether a candidate change should be accepted, rejected, or revised.

Projection demands: diff, provenance, evidence, authorship, recommendation, and action boundary tightly coupled.

Dominant planes: change, evidence, lineage, capability, handoff.
Risk: high.
Failure mode: accepting or rejecting without basis in immediate reach.

### 7. Workflow orchestration

Goal: launch, monitor, parameterize, or sequence repeatable procedures.

Projection demands: workflow identity, provider/harness/config/build visibility, capability state, queue/run status, clear target scope.

Dominant planes: procedure, execution, identity, capability.
Risk: high.
Failure mode: procedure launch looking like casual chat rather than bounded execution.

### 8. Evidence inspection

Goal: inspect why the system said or did something.

Projection demands: provenance graph, raw evidence, trace linkages, source-to-summary walkability.

Dominant planes: evidence, change, execution, lineage.
Risk: variable but often high.
Failure mode: advisory summaries without drill-down.

### 9. High-risk action execution

Goal: perform an effectful operation with meaningful downside.

Projection demands: explicit scope, capability state, boundary cue, evidence adjacency, reversibility disclosure, trust notices.

Dominant planes: capability, evidence, identity, handoff.
Risk: critical.
Failure mode: calm minimalism that hides consequence-bearing semantics.

### 10. Post-run audit / provenance tracing

Goal: reconstruct what happened after an agentic or procedural run.

Projection demands: timeline, changed artifacts, lineage, raw outputs, approvals, scope, and environment identity.

Dominant planes: lineage, evidence, execution, handoff.
Risk: high.
Failure mode: only seeing a summary of what allegedly happened.

### 11. Same user, different lawful projection

A clutter-sensitive user may prefer a sparse, anchored projection in exploration and code reading. That same user may need a denser debugging projection, because the smallest semantically sufficient debugging working set may include logs, config identity, recent diffs, and the affected artifact simultaneously.

Likewise, a dense-interface power user may still need a trace-audit projection in high-risk review, because governance and evidence adjacency override raw density preference.

So projection choice is not “personalization first.” The order is:

**semantic law -> governance constraints -> task mode -> user cognitive fit**

---

## MORPHIC_UX_LAW_FOR_AGENTIC_DE

### 1. Definition of lawful morphic space

The lawful morphic space of an agentic DE is the set of UX transformations that alter projection without altering semantic law.

Formally:

`L = { μ | preserve(semantic invariants) and preserve(anchor continuity or migrate explicitly) and preserve human competence and satisfy governance + mode constraints }`

A lawful view can change what is foregrounded.
It cannot change what is true.

### 2. Core morphic laws

**Semantic Primacy Law**
ODEU grammar is upstream. UX schemas are downstream. No projection change may redefine object meaning or verb class.

**Command Target Clarity Law**
If the composer can address multiple interpreters or action classes, the current target must be explicit. Silent retargeting is forbidden.

**Advisory vs Authoritative Rendering Law**
Advice, recommendation, preview, proposed change, applied state, and runtime fact must remain visually and procedurally distinguishable.

**Evidence Adjacency Law**
At decision points, especially high-risk ones, relevant evidence must be in immediate reach. A lawful morph may bring evidence closer; it may not make evidence harder to reach where risk is high.

**Capability Boundary Visibility Law**
Read/write/execute/dispatch/configure state must be visible at or near action boundaries. The user must not guess what authority is currently live.

**Identity Disclosure Law**
When output depends on harness, provider, config, or build, that identity must remain visible or one-step obvious.

**Spatial Anchor Law**
Critical anchors retain stable home zones, labels, or invocation paths across morphs.

**Cross-State Invariance Law**
The same semantic object remains recognizable as the same object across different renderings. Inline diff, side diff, and fullscreen diff must not feel like unrelated objects.

**Handoff-Boundary Visibility Law**
Any transition from local to external, advisory to effectful, preview to applied, or internal to dispatched must be explicit in scope, target, and consequence.

**Competence Preservation Law**
Morphism must preserve user-acquired competence: spatial habits, motor habits, evidence-tracking habits, and boundary recognition.

**Stillness and Reversibility Law**
Automatic morphism should be sparse, reversible, and mode-bound. Constant motion is not morphic intelligence; it is interference.

**Explicit Migration Law**
When a change would materially disrupt anchor maps, hotkeys, or action rituals, the system must treat it as migration, not adaptation.

### 3. What may change freely

These can generally change automatically when low-risk, reversible, and anchor-preserving:

* local layout proportions,
* salience weighting,
* density,
* spacing,
* color emphasis,
* inline versus sidecar advisory placement,
* temporary pane peeking,
* collapse/expand of secondary surfaces,
* artifact prominence,
* transient evidence promotion,
* docked versus peek rendering for noncritical surfaces,
* ordering within a stable zone.

Important constraint: color emphasis may assist deontic distinction, but may not be the sole carrier of it.

### 4. What may change slowly

These should change only from stable evidence of fit, repeated manual behavior, or explicit user preference, usually on a per-mode basis:

* default pane grouping,
* transcript baseline prominence,
* explorer persistence,
* terminal persistence,
* default evidence pinning,
* default sidecar versus inline evidence strategy,
* promotion of frequently needed affordances into anchors,
* default concurrency level for a mode.

“Slowly” means: not on single incidents, not during active critical flow, and not without a clear path back.

### 5. What may change only with explicit migration

These changes materially affect spatial or motor memory and therefore require notice, preview, and rollback:

* moving the composer to a new home zone,
* moving capability state to a different retrieval locus,
* changing hotkeys or gesture grammar,
* changing the primary workbench topology,
* relocating review or execute controls,
* changing the meaning of Enter or similar primary submit rituals,
* changing the default command-target model,
* making previously persistent critical anchors latent.

Explicit migration should reveal the new anchor map, preserve old invocation paths where possible, and provide rollback.

### 6. What may never change without violating semantic law

These are forbidden morphs because they constitute semantic laundering:

* rendering advisory text as if it were applied state,
* rendering a preview as if it were execution,
* rendering an agent summary as if it were authoritative runtime output,
* hiding capability state at effectful boundaries,
* hiding handoff boundaries,
* silently switching provider/harness/config identity,
* silently retargeting the composer from advisory to effectful execution,
* collapsing approval and recommendation into the same control affordance,
* making evidence inaccessible near high-risk decisions,
* conflating workspace state with committed or dispatched state.

### 7. Analysis of the requested morph dimensions

**Layout**
Free within stable macro-zones. Slow across zone families. Migration when anchors move.

**Salience**
Largely free, and should be mode-sensitive.

**Density**
Largely free, but constrained by profile fit and evidence reachability.

**Spacing**
Free, assuming no loss of parseability or boundary legibility.

**Color emphasis**
Free as secondary emphasis. Forbidden as sole semantic discriminator of authority or risk.

**Pane grouping**
Slow. Grouping affects spatial memory and working-set habits.

**Docked vs peek rendering**
Free for secondary surfaces. Slow for recurrently used supports. Not lawful for critical boundaries in critical modes.

**Persistent vs collapsible surfaces**
Same rule. Secondary surfaces may collapse. Critical anchors may not disappear into obscurity.

**Artifact prominence**
Mode-controlled and highly morphable.

**Placement of advisory outputs**
Free across lawful advisory zones, so long as their advisory status remains explicit and their basis remains reachable.

**Placement of evidence near action boundaries**
Not merely allowed but often required as risk rises.

**Placement of trust notices**
Trust notices are semantic disclosures, not decoration. They must intensify near execution, review, dispatch, or configuration boundaries.

### 8. Spatial memory and cross-morphic anchors

Spatial memory in an agentic DE is not a comfort extra. It is part of user safety and recovery.

A **cross-morphic anchor** is a stable retrieval contract for a critical function or state. It can consist of:

* a stable home zone,
* a stable label or token,
* a stable invocation path,
* a stable semantic role.

What matters is topological continuity more than pixel-perfect continuity.

Useful cross-morphic anchor bundles in agentic DEs include:

**Identity rail**
Workspace identity, current scope, branch/version, provider/harness/build identity.

**Intent anchor**
Composer and current interpreter target.

**Evidence anchor**
Diff, provenance, logs, basis, source trace.

**Boundary belt**
Writes enabled, execute/apply/review/dispatch boundaries, reversibility cues.

**Process anchor**
Active run state, failures, background jobs.

**Recovery anchor**
Undo, revert, compare-to-previous, audit trail entry.

Some affordances should be promoted into anchors when they become high-frequency, high-risk, or recovery-critical for a given user or mode. That promotion is usually a slow morph; if it restructures major anchor maps, it becomes migration.

---

## UX_PROFILE_FAMILY_FOR_AGENTIC_DE

These are not style themes or brand skins. They are lawful projection families over the same semantic component set.

### 1. Anchored Progressive

One dominant work surface, strong fixed anchors, secondary surfaces by peek or controlled disclosure.

Best fit: high clutter sensitivity, low pane simultaneity tolerance, high stable-anchor need.
Best modes: exploration, drafting, code reading.
Primary risk: underexposed evidence in review or high-risk execution unless the system force-promotes it.

### 2. Artifact-Central Edit

Artifact surface dominates; transcript and advisory are compressed; local diff and write boundary stay close; runtime is secondary.

Best fit: strong muscle-memory reliance, medium density tolerance, editing-heavy flow.
Best modes: code editing, drafting.
Primary risk: provenance and review semantics can become too latent if reused unchanged for adjudication.

### 3. Concurrent Matrix

Several semantic planes remain co-visible with stable zoning and minimal toggling.

Best fit: high density tolerance, high evidence appetite, low mode-switch tolerance.
Best modes: debugging, review, evidence inspection, orchestration.
Primary risk: overload for clutter-sensitive users and calm-surface seekers.

### 4. Trace Audit

Diff, provenance, evidence, identity, and action boundary are tightly coupled. Recommendations never appear alone.

Best fit: high risk sensitivity, high provenance appetite, high control explicitness preference.
Best modes: review/adjudication, high-risk action execution, post-run audit.
Primary risk: slower creative flow in drafting or free exploration.

### 5. Runtime Diagnostic

Runtime output, errors, harness/build identity, recent change context, and affected artifacts are foregrounded together.

Best fit: users who debug through evidence triangulation and need execution context visible.
Best modes: debugging, workflow failure investigation.
Primary risk: fragmented authoring flow if left active after diagnosis.

### 6. Orchestration Control

Workflow launch, queue state, provider/config identity, capability boundaries, and active run outcomes are foregrounded; artifacts are secondary.

Best fit: procedure-heavy work, multi-run management, operational or build-focused episodes.
Best modes: workflow orchestration, environment operations, automation supervision.
Primary risk: weak support for deep artifact understanding unless paired with strong artifact summon paths.

These families are meant to be composable across modes while preserving the same anchor map wherever possible.

---

## PROJECTION_FIT_CRITERIA

A projection is not “good” because it looks clean or fast in the abstract. It is good only relative to:

* project type,
* user cognitive profile,
* task/mode profile,
* semantic law,
* governance constraints.

### 1. Hard invalidators

A projection is invalid if any of these fail:

**Semantic transparency**
Can the user tell advice from fact, proposal from applied state, local from dispatched state?

**Authority visibility**
Can the user tell what is currently permitted?

**Command-target clarity**
Can the user tell what interpreter or operator class will receive the input?

**Evidence reachability**
Can the user reach the basis for a decision without hunting?

**Handoff visibility**
Can the user tell when the system is crossing a boundary to another system, reviewer, or irreversible action?

**Identity disclosure**
Can the user tell which harness/provider/config/build identity governs the output?

**Anchor continuity**
Can the user still find critical anchors using learned routes?

**Governance conformance**
Does the projection preserve required review, evidence, or boundary obligations?

If any hard invalidator fails, the projection is unlawful regardless of aesthetic quality.

### 2. Scored fit dimensions

Once lawful, a projection can be scored.

**Cognitive fit**
How well the working set matches the user’s bandwidth, simultaneity tolerance, and clutter sensitivity.

**Context retention**
How well the view preserves scope, current focus, branch, identity, and relevant neighboring context across transitions.

**Action-boundary clarity**
How legible the crossing points are: preview/apply, local/external, recommend/approve, shell/advisory.

**Evidence friction**
How many steps, attention shifts, or reorientations are needed to inspect basis.

**Task efficiency under governance**
How efficiently the mode can be completed without bypassing necessary safeguards.

**Recovery ease**
How easy it is to revert, compare, retrace, or reorient after an error or unexpected result.

### 3. Penalty dimensions

A lawful projection can still be poor because of penalties.

**Distortion risk**
Likelihood that the projection causes overtrust, underinspection, or semantic misread.

**Overload risk**
Likelihood that the view exceeds the user’s parsing capacity for the current mode.

**Whiplash risk**
Likelihood that adaptation itself destroys orientation or flow.

### 4. Mode-weighted fit

Different modes weight criteria differently.

* Exploration heavily weights orientation, anchor stability, and low overload.
* Editing heavily weights motor continuity, artifact prominence, and quick recovery.
* Debugging heavily weights evidence concurrency and identity disclosure.
* Review heavily weights evidence adjacency, semantic transparency, and action-boundary clarity.
* High-risk execution heavily weights authority visibility, trust notices, and reversibility cues.
* Post-run audit heavily weights provenance completeness and trace walkability.

So a projection can be excellent for exploration and weak for review without contradiction.

### 5. Practical evaluator shape

A compact formula:

`overall_fit = lawful_gate * weighted_task_score - risk_penalties`

Where:

* `lawful_gate` is binary and fails on hard invalidators,
* `weighted_task_score` depends on mode,
* `risk_penalties` are distortion, overload, and whiplash.

---

## RESIDENT_AGENT_MORPHIC_NEGOTIATION_MODEL

The resident agent is not a stylist.
It is a lawful projection negotiator.

Its role is to infer likely fit, propose lawful alternatives, apply low-risk local adaptations, and preserve semantic law and user competence.

### 1. What the agent may infer

The agent may infer:

* probable current task mode,
* likely cognitive pressure points,
* likely evidence appetite,
* likely clutter sensitivity,
* likely anchor dependence,
* likely mode-switch cost,
* whether current view is causing friction.

It should infer these probabilistically, not as fixed personality truths.

### 2. What evidence the agent should use

The agent should use grounded interaction evidence such as:

* repeated manual opening of the same secondary surface,
* repeated collapsing of the same noisy surface,
* oscillation between transcript and diff,
* long dwell before effectful controls,
* repeated search for hidden anchors,
* repeated viewing of provenance before approval,
* immediate undo or revert after action,
* recurrent manual resizing or repinning,
* repeated dismissal of unsolicited suggestions,
* transition patterns that clearly signal mode change,
* active failures, runs, reviews, or audits in semantic state.

One-off events should not trigger major morphs. The agent should look for sustained patterns.

### 3. What the agent may propose

The agent may propose:

* alternate lawful view families,
* mode-local salience changes,
* different evidence placements,
* different transcript prominence,
* pinned or unpinned supporting surfaces,
* tighter action-boundary rendering,
* calmer or denser variants within the same anchor map.

The proposal should describe consequences, not just parameters.

Better: “Show logs, diff, and config together while you debug.”
Worse: “Increase pane simultaneity and evidence adjacency.”

### 4. What the agent may adapt automatically

Automatic adaptation is appropriate only for low-risk, reversible, anchor-preserving changes such as:

* peeking terminal on run start,
* promoting diff after candidate change generation,
* opening evidence sidecar in review mode,
* reducing transcript prominence during sustained editing focus,
* preserving a user’s repeated pin/unpin choice within a mode,
* lowering unsolicited interruption when the user repeatedly dismisses it.

These are micro-adaptations, not semantic migrations.

### 5. What the agent must not mutate silently

The agent must not silently mutate:

* composer target semantics,
* hotkeys or motor grammar,
* primary anchor locations,
* capability boundary visibility,
* review/approve/execute control locus,
* provider/harness/build identity disclosure,
* evidence reachability at decision points,
* handoff visibility,
* global default topology.

Those require explicit migration or user approval.

### 6. Recognition over specification

Many users cannot specify good UX in abstract terms. They respond better to curated lawful candidates than to preference elicitation questionnaires.

So the agent should prefer:

* small contrastive sets,
* concrete experiential language,
* reversible previews,
* mode-local choices,
* “what gets easier” framing.

A good candidate set is usually two or three views, not ten.

For example:

* “Keep code central; diff appears beside edits.”
* “Show logs, recent changes, and config together.”
* “Tight review: evidence stays next to approve/reject.”

The user can recognize fit by felt clarity, reduced hunting, and safer action. They do not need a vocabulary of density, simultaneity, or provenance appetite.

### 7. Negotiation loop

A rigorous negotiation loop is:

1. Sense semantic state and interaction traces.
2. Infer mode and provisional profile pressures.
3. Retrieve lawful candidate schemas.
4. Evaluate candidates against invariants and fit criteria.
5. Propose contrastive reversible candidates, or apply only low-risk micro-adaptations.
6. Observe acceptance, rejection, or abandonment.
7. Stabilize once fit is found.

The agent’s job is not to keep changing the UI. Its job is to help the UI settle into a better lawful fit.

### 8. Why this matters

A resident semantic agent makes morphic UX practical because it can mediate among:

* the stable project-type grammar,
* the current semantic state,
* the current task mode,
* the user’s dynamic cognitive profile,
* the governance envelope.

But the agent remains a negotiator inside the law.
It is not allowed to rewrite the law.

---

## Machine-checkable schema blocks

The following are compact contract-level schemas.

### `project_type_grammar@1`

```json
{
  "$id": "project_type_grammar@1",
  "type": "object",
  "required": [
    "project_type",
    "planes",
    "typed_cycles",
    "command_targets",
    "required_surfaces",
    "hard_distinctions",
    "required_anchors"
  ],
  "properties": {
    "project_type": {
      "const": "agentic_de"
    },
    "planes": {
      "type": "array",
      "items": {
        "enum": [
          "negotiation",
          "context",
          "artifact",
          "change",
          "execution",
          "lineage",
          "governance",
          "evidence",
          "handoff"
        ]
      },
      "uniqueItems": true
    },
    "typed_cycles": {
      "type": "array",
      "items": {
        "enum": [
          "query",
          "proposal",
          "execution",
          "review",
          "dispatch",
          "audit",
          "recovery"
        ]
      },
      "uniqueItems": true
    },
    "command_targets": {
      "type": "array",
      "items": {
        "enum": [
          "agent",
          "shell",
          "workflow_engine",
          "review_router",
          "version_control",
          "search"
        ]
      },
      "uniqueItems": true
    },
    "required_surfaces": {
      "type": "array",
      "items": {
        "enum": [
          "transcript_lane",
          "composer",
          "workspace_context",
          "context_explorer",
          "artifact_reader",
          "diff_provenance",
          "terminal_runtime",
          "git_version",
          "review_dispatch",
          "workflow_launch",
          "environment_identity",
          "capability_boundary",
          "evidence_advisory"
        ]
      },
      "uniqueItems": true
    },
    "hard_distinctions": {
      "type": "array",
      "items": {
        "enum": [
          "advisory_vs_authoritative",
          "proposal_vs_applied_state",
          "preview_vs_execute",
          "local_vs_dispatched",
          "runtime_output_vs_agent_summary",
          "workspace_state_vs_version_state",
          "agent_command_vs_shell_command",
          "human_approval_vs_agent_recommendation"
        ]
      },
      "uniqueItems": true
    },
    "required_anchors": {
      "type": "array",
      "items": {
        "enum": [
          "composer",
          "workspace_identity",
          "current_scope",
          "capability_state",
          "version_identity",
          "evidence_access",
          "diff_access",
          "active_run_status",
          "current_focus_identity",
          "undo_or_revert"
        ]
      },
      "uniqueItems": true
    }
  },
  "additionalProperties": false
}
```

### `cognitive_profile_packet@1`

```json
{
  "$id": "cognitive_profile_packet@1",
  "type": "object",
  "required": [
    "dimensions"
  ],
  "properties": {
    "profile_id": {
      "type": "string"
    },
    "dimensions": {
      "type": "object",
      "required": [
        "density_tolerance",
        "visual_clutter_sensitivity",
        "semantic_compression_tolerance",
        "spatial_memory_reliance",
        "muscle_memory_reliance",
        "working_memory_bandwidth",
        "pane_simultaneity_tolerance",
        "progressive_disclosure_preference",
        "context_retention_dependence",
        "evidence_appetite",
        "control_explicitness_preference",
        "mode_switch_cost_sensitivity",
        "action_risk_sensitivity",
        "action_boundary_awareness_dependence",
        "stable_anchor_need",
        "calm_surface_preference",
        "interruption_tolerance",
        "abstract_preference_articulation"
      ],
      "properties": {
        "density_tolerance": { "type": "integer", "minimum": 1, "maximum": 5 },
        "visual_clutter_sensitivity": { "type": "integer", "minimum": 1, "maximum": 5 },
        "semantic_compression_tolerance": { "type": "integer", "minimum": 1, "maximum": 5 },
        "spatial_memory_reliance": { "type": "integer", "minimum": 1, "maximum": 5 },
        "muscle_memory_reliance": { "type": "integer", "minimum": 1, "maximum": 5 },
        "working_memory_bandwidth": { "type": "integer", "minimum": 1, "maximum": 5 },
        "pane_simultaneity_tolerance": { "type": "integer", "minimum": 1, "maximum": 5 },
        "progressive_disclosure_preference": { "type": "integer", "minimum": 1, "maximum": 5 },
        "context_retention_dependence": { "type": "integer", "minimum": 1, "maximum": 5 },
        "evidence_appetite": { "type": "integer", "minimum": 1, "maximum": 5 },
        "control_explicitness_preference": { "type": "integer", "minimum": 1, "maximum": 5 },
        "mode_switch_cost_sensitivity": { "type": "integer", "minimum": 1, "maximum": 5 },
        "action_risk_sensitivity": { "type": "integer", "minimum": 1, "maximum": 5 },
        "action_boundary_awareness_dependence": { "type": "integer", "minimum": 1, "maximum": 5 },
        "stable_anchor_need": { "type": "integer", "minimum": 1, "maximum": 5 },
        "calm_surface_preference": { "type": "integer", "minimum": 1, "maximum": 5 },
        "interruption_tolerance": { "type": "integer", "minimum": 1, "maximum": 5 },
        "abstract_preference_articulation": { "type": "integer", "minimum": 1, "maximum": 5 }
      },
      "additionalProperties": false
    },
    "state_modifiers": {
      "type": "object",
      "properties": {
        "familiarity": {
          "enum": ["low", "medium", "high"]
        },
        "fatigue": {
          "enum": ["low", "medium", "high"]
        },
        "urgency": {
          "enum": ["low", "medium", "high"]
        }
      },
      "additionalProperties": false
    },
    "confidence": {
      "type": "number",
      "minimum": 0,
      "maximum": 1
    }
  },
  "additionalProperties": false
}
```

### `task_mode_packet@1`

```json
{
  "$id": "task_mode_packet@1",
  "type": "object",
  "required": [
    "mode",
    "risk_tier",
    "foreground_planes",
    "protected_anchors"
  ],
  "properties": {
    "mode": {
      "enum": [
        "exploration",
        "drafting",
        "code_reading",
        "code_editing",
        "debugging",
        "review_adjudication",
        "workflow_orchestration",
        "evidence_inspection",
        "high_risk_action_execution",
        "post_run_audit"
      ]
    },
    "risk_tier": {
      "enum": ["low", "medium", "high", "critical"]
    },
    "dominant_operations": {
      "type": "array",
      "items": {
        "enum": [
          "orient",
          "inspect",
          "ask",
          "draft",
          "edit",
          "run",
          "compare",
          "review",
          "approve",
          "reject",
          "dispatch",
          "audit",
          "configure",
          "recover"
        ]
      },
      "uniqueItems": true
    },
    "foreground_planes": {
      "type": "array",
      "items": {
        "enum": [
          "negotiation",
          "context",
          "artifact",
          "change",
          "execution",
          "lineage",
          "governance",
          "evidence",
          "handoff"
        ]
      },
      "uniqueItems": true
    },
    "supporting_planes": {
      "type": "array",
      "items": {
        "enum": [
          "negotiation",
          "context",
          "artifact",
          "change",
          "execution",
          "lineage",
          "governance",
          "evidence",
          "handoff"
        ]
      },
      "uniqueItems": true
    },
    "protected_anchors": {
      "type": "array",
      "items": {
        "enum": [
          "composer",
          "workspace_identity",
          "current_scope",
          "capability_state",
          "version_identity",
          "evidence_access",
          "diff_access",
          "active_run_status",
          "current_focus_identity",
          "undo_or_revert"
        ]
      },
      "uniqueItems": true
    },
    "mandatory_adjacencies": {
      "type": "array",
      "items": {
        "type": "string"
      }
    },
    "evidence_intensity": {
      "type": "integer",
      "minimum": 1,
      "maximum": 5
    },
    "concurrency_need": {
      "type": "integer",
      "minimum": 1,
      "maximum": 5
    },
    "mutation_class": {
      "enum": ["none", "propose", "apply", "execute", "dispatch"]
    }
  },
  "additionalProperties": false
}
```

### `ux_profile_schema@1`

```json
{
  "$id": "ux_profile_schema@1",
  "type": "object",
  "required": [
    "ux_profile_id",
    "selection_posture",
    "concurrency_level",
    "density_level",
    "anchor_rigidity",
    "artifact_prominence",
    "transcript_prominence",
    "evidence_adjacency",
    "boundary_emphasis",
    "runtime_prominence",
    "explorer_persistence",
    "secondary_surface_policy",
    "best_for_modes"
  ],
  "properties": {
    "ux_profile_id": {
      "enum": [
        "anchored_progressive",
        "artifact_central_edit",
        "concurrent_matrix",
        "trace_audit",
        "runtime_diagnostic",
        "orchestration_control"
      ]
    },
    "selection_posture": {
      "enum": [
        "manual",
        "recognition_led",
        "agent_suggested"
      ]
    },
    "concurrency_level": {
      "type": "integer",
      "minimum": 1,
      "maximum": 5
    },
    "density_level": {
      "type": "integer",
      "minimum": 1,
      "maximum": 5
    },
    "anchor_rigidity": {
      "type": "integer",
      "minimum": 1,
      "maximum": 5
    },
    "artifact_prominence": {
      "type": "integer",
      "minimum": 1,
      "maximum": 5
    },
    "transcript_prominence": {
      "type": "integer",
      "minimum": 1,
      "maximum": 5
    },
    "evidence_adjacency": {
      "type": "integer",
      "minimum": 1,
      "maximum": 5
    },
    "boundary_emphasis": {
      "type": "integer",
      "minimum": 1,
      "maximum": 5
    },
    "runtime_prominence": {
      "type": "integer",
      "minimum": 1,
      "maximum": 5
    },
    "explorer_persistence": {
      "enum": ["pinned", "summoned", "peek", "mixed"]
    },
    "secondary_surface_policy": {
      "enum": ["docked", "collapsible", "peek", "mixed"]
    },
    "best_for_modes": {
      "type": "array",
      "items": {
        "enum": [
          "exploration",
          "drafting",
          "code_reading",
          "code_editing",
          "debugging",
          "review_adjudication",
          "workflow_orchestration",
          "evidence_inspection",
          "high_risk_action_execution",
          "post_run_audit"
        ]
      },
      "uniqueItems": true
    }
  },
  "additionalProperties": false
}
```

### `morphic_invariant_set@1`

```json
{
  "$id": "morphic_invariant_set@1",
  "type": "object",
  "required": [
    "semantic_invariants",
    "anchor_invariants",
    "boundary_invariants",
    "identity_invariants",
    "competence_invariants"
  ],
  "properties": {
    "semantic_invariants": {
      "type": "array",
      "items": {
        "enum": [
          "advisory_authoritative_separation",
          "proposal_applied_separation",
          "preview_execute_separation",
          "runtime_summary_raw_separation",
          "version_workspace_separation",
          "command_target_clarity",
          "local_dispatched_separation"
        ]
      },
      "uniqueItems": true
    },
    "anchor_invariants": {
      "type": "array",
      "items": {
        "enum": [
          "composer_anchor",
          "workspace_identity_anchor",
          "capability_anchor",
          "evidence_anchor",
          "diff_anchor",
          "active_run_anchor",
          "current_focus_anchor",
          "recovery_anchor"
        ]
      },
      "uniqueItems": true
    },
    "boundary_invariants": {
      "type": "array",
      "items": {
        "enum": [
          "write_boundary_visibility",
          "execute_boundary_visibility",
          "dispatch_boundary_visibility",
          "approval_boundary_visibility",
          "scope_visibility",
          "reversibility_visibility"
        ]
      },
      "uniqueItems": true
    },
    "identity_invariants": {
      "type": "array",
      "items": {
        "enum": [
          "workspace_identity_visibility",
          "version_identity_visibility",
          "provider_identity_visibility",
          "harness_identity_visibility",
          "build_identity_visibility"
        ]
      },
      "uniqueItems": true
    },
    "competence_invariants": {
      "type": "array",
      "items": {
        "enum": [
          "spatial_memory_preservation",
          "motor_memory_preservation",
          "evidence_tracking_preservation",
          "action_boundary_awareness_preservation"
        ]
      },
      "uniqueItems": true
    }
  },
  "additionalProperties": false
}
```

### `morphic_operation_law@1`

```json
{
  "$id": "morphic_operation_law@1",
  "type": "object",
  "required": [
    "free_ops",
    "slow_ops",
    "migration_ops",
    "forbidden_ops",
    "auto_adapt_guardrails"
  ],
  "properties": {
    "free_ops": {
      "type": "array",
      "items": {
        "enum": [
          "resize_surface",
          "reweight_salience",
          "change_density",
          "change_spacing",
          "recolor_emphasis",
          "collapse_secondary_surface",
          "peek_secondary_surface",
          "pin_secondary_surface",
          "reorder_within_zone",
          "inline_evidence",
          "inline_advisory",
          "promote_artifact",
          "demote_artifact"
        ]
      },
      "uniqueItems": true
    },
    "slow_ops": {
      "type": "array",
      "items": {
        "enum": [
          "change_default_grouping",
          "change_transcript_baseline",
          "change_explorer_persistence",
          "change_terminal_persistence",
          "change_default_evidence_pinning",
          "change_default_concurrency",
          "promote_affordance_to_anchor"
        ]
      },
      "uniqueItems": true
    },
    "migration_ops": {
      "type": "array",
      "items": {
        "enum": [
          "move_composer_anchor",
          "move_capability_anchor",
          "remap_hotkeys",
          "change_primary_zone_topology",
          "move_action_control_locus",
          "change_submit_ritual",
          "change_command_target_model"
        ]
      },
      "uniqueItems": true
    },
    "forbidden_ops": {
      "type": "array",
      "items": {
        "enum": [
          "blur_advisory_authoritative",
          "blur_preview_execute",
          "render_agent_summary_as_runtime_fact",
          "hide_capability_state",
          "hide_evidence_at_decision",
          "hide_handoff_boundary",
          "silently_switch_provider_identity",
          "silently_retarget_composer",
          "conflate_recommendation_with_approval",
          "conflate_workspace_state_with_dispatched_state"
        ]
      },
      "uniqueItems": true
    },
    "auto_adapt_guardrails": {
      "type": "array",
      "items": {
        "enum": [
          "reversible",
          "anchor_preserving",
          "mode_bound",
          "low_semantic_cost",
          "not_critical_risk",
          "governance_safe",
          "respect_layout_freeze"
        ]
      },
      "uniqueItems": true
    }
  },
  "additionalProperties": false
}
```

### `projection_fit_evaluator@1`

```json
{
  "$id": "projection_fit_evaluator@1",
  "type": "object",
  "required": [
    "evaluation_context",
    "hard_gate_results",
    "criterion_scores",
    "penalty_scores",
    "overall_fit"
  ],
  "properties": {
    "evaluation_context": {
      "type": "object",
      "required": ["mode"],
      "properties": {
        "mode": {
          "enum": [
            "exploration",
            "drafting",
            "code_reading",
            "code_editing",
            "debugging",
            "review_adjudication",
            "workflow_orchestration",
            "evidence_inspection",
            "high_risk_action_execution",
            "post_run_audit"
          ]
        },
        "ux_profile_id": {
          "enum": [
            "anchored_progressive",
            "artifact_central_edit",
            "concurrent_matrix",
            "trace_audit",
            "runtime_diagnostic",
            "orchestration_control"
          ]
        }
      },
      "additionalProperties": false
    },
    "hard_gate_results": {
      "type": "object",
      "required": [
        "semantic_transparency",
        "authority_visibility",
        "command_target_clarity",
        "evidence_reachability",
        "handoff_visibility",
        "identity_disclosure",
        "anchor_continuity",
        "governance_conformance"
      ],
      "properties": {
        "semantic_transparency": { "type": "boolean" },
        "authority_visibility": { "type": "boolean" },
        "command_target_clarity": { "type": "boolean" },
        "evidence_reachability": { "type": "boolean" },
        "handoff_visibility": { "type": "boolean" },
        "identity_disclosure": { "type": "boolean" },
        "anchor_continuity": { "type": "boolean" },
        "governance_conformance": { "type": "boolean" }
      },
      "additionalProperties": false
    },
    "criterion_scores": {
      "type": "object",
      "required": [
        "cognitive_fit",
        "context_retention",
        "action_boundary_clarity",
        "evidence_friction",
        "task_efficiency_under_governance",
        "recovery_ease"
      ],
      "properties": {
        "cognitive_fit": { "type": "number", "minimum": 0, "maximum": 5 },
        "context_retention": { "type": "number", "minimum": 0, "maximum": 5 },
        "action_boundary_clarity": { "type": "number", "minimum": 0, "maximum": 5 },
        "evidence_friction": { "type": "number", "minimum": 0, "maximum": 5 },
        "task_efficiency_under_governance": { "type": "number", "minimum": 0, "maximum": 5 },
        "recovery_ease": { "type": "number", "minimum": 0, "maximum": 5 }
      },
      "additionalProperties": false
    },
    "penalty_scores": {
      "type": "object",
      "required": [
        "distortion_risk",
        "overload_risk",
        "whiplash_risk"
      ],
      "properties": {
        "distortion_risk": { "type": "number", "minimum": 0, "maximum": 5 },
        "overload_risk": { "type": "number", "minimum": 0, "maximum": 5 },
        "whiplash_risk": { "type": "number", "minimum": 0, "maximum": 5 }
      },
      "additionalProperties": false
    },
    "overall_fit": {
      "type": "number",
      "minimum": 0,
      "maximum": 1
    }
  },
  "additionalProperties": false
}
```

This framework is now strong enough to support later grounded inspection of concrete builds by asking:

* which semantic planes are actually preserved,
* which anchors are stable,
* which user cognitive profiles they fit,
* which task modes they privilege,
* where they launder authority or evidence,
* where they preserve or destroy cross-morphic competence,
* and what a stronger synthesis should keep invariant across future implementations.
