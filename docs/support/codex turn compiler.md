I inspected the attached repo state rather than relying on planning prose alone. In what follows, **observed** means directly grounded in the repo files I read, and **inferred** means the architectural design I recommend on top of that base.

The most relevant observed sources were:

* `README.md`, `REPO_ATLAS.md`
* `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`
* `docs/support/ODEU_MEMBRANE_ARCHITECTURE.md`
* `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_FAMILY_v0.md`
* `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_FAMILY_v0.md`
* `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_PERSISTENT_WORKSPACE_CONTINUITY_FAMILY_v0.md`
* `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
* `docs/support/endogenous grounding. md`
* `packages/adeu_agentic_de/src/adeu_agentic_de/{models.py,checker.py,workspace_continuity.py}`
* `packages/adeu_history_semantics/src/adeu_history_semantics/{models.py,preclassify.py,reconstruct.py}`
* `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`
* `packages/adeu_semantic_compiler/src/adeu_semantic_compiler/compile.py`
* `packages/urm_runtime/src/urm_runtime/orchestration_state.py`

## 1. Executive thesis

The best ADEU-native direction is to add a **turn compiler family** in front of the current runtime:

**surface utterance → typed semantic ingress → governed operator binding/expansion → gated execution packet → ODEU refresh reducer**

That is the core shift:

* from **transcript-centric continuity** to **state-centric typed refresh**
* from **generic prompt interpretation** to **closed-world semantic ingress**
* from **freeform “reasoning about what the user meant”** to **governed operator compilation**
* from **conversation-summary memory** to **ODEU deltas, residual witnesses, and reproposal demands**
* from **implicit carryover** to **explicit stage-to-stage carry law**

In repo terms, I would not replace the existing stacks. I would **compose** them:

* reuse the existing **semantic compiler discipline** for closed-world registries and deterministic passes,
* reuse **agentic_de** for governed action/checkpoint/ticket/handoff/reintegration,
* reuse **URM runtime** for session/orchestration,
* reuse **history semantics** only as a migration/import aid,
* and insert a new **ODEU turn compiler** between user ingress and those existing runtime lanes.

The governing design principle is:

> the user turn itself becomes a typed, fail-closed, stage-gated compiled object, and the end of each turn produces a lawful ODEU state delta rather than a transcript compaction.

## 2. Why this architecture is needed

The architecture is needed because the current failure modes are exactly the ones ADEU’s other families already know how to avoid elsewhere.

First, transcript inheritance causes **semantic drift**. A transcript is a poor continuity substrate because it mixes user intent, assistant hypotheses, tool chatter, failed proposals, and provisional reasoning in one carrier. Once you later compact that carrier, the distinction between source, inference, and failure state blurs.

Second, transcript or summary continuity creates **fake authority**. A past thought or tool trace can start behaving like settled state even though it was never explicitly promoted. The repo already treats docs, checkpoints, tickets, and observation records as typed artifacts. User-turn semantics are still an open seam.

Third, compaction without a carry law enables **laundering**. The repo’s support docs already warn about this in adjacent areas. `docs/support/ODEU_MEMBRANE_ARCHITECTURE.md` frames ODEU as the “last lawful semantic checkpoint,” and `docs/ARCHITECTURE_ADEU_DOMAIN_SUBSTRATE_FAMILY_v0.md` explicitly warns that normalization or projection can launder authority if left implicit. The same danger exists across turns.

Fourth, recurrent workflow instructions are being treated as prompts when they are actually **semantic operators**. Your example is not “write prose in response to an instruction.” It is a bounded workflow with role allocation, sequencing, write policy, review semantics, and postconditions. Interpreting that as a generic prompt invites drift, hidden defaults, and accidental widening.

Fifth, without stage gating, the system releases **reasoning and action surfaces too early**. A classifier guess becomes a plan; a plan becomes an execution intent; an execution intent becomes apparent authorization. The resident-agent governance family already has the right instinct here: advisory until governed gate, no hidden write/execute/dispatch boundary, unresolved states may not be laundered into action.

Sixth, cross-stage pipelines without explicit carry law allow **assumption smuggling**. One stage’s internal, non-emittable reasoning becomes the next stage’s “context.” That is exactly the sort of hidden bridge state the live harness and continuity families are trying to eliminate on the runtime side.

So the architecture is needed not because the repo lacks governance. It is needed because the repo’s governance is strong **after** a task/proposal is already formed, but weak at the earlier seam where a user utterance becomes the thing the runtime thinks it is executing.

## 3. Repo-grounded starting point

### What already exists and can be reused

**Observed: docs-as-authority plus deterministic compilation.**
`README.md` and `REPO_ATLAS.md` both frame the repo as docs-governed, typed-first, deterministic, fail-closed. `packages/adeu_semantic_compiler/src/adeu_semantic_compiler/compile.py` has an explicit fixed pass sequence (`LoadCollection`, `ValidateBlocks`, `RevalidateNormalization`, `BuildIR`, `ResolveRefs`, `TypecheckLocks`). `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md` already defines hard invariants around determinism, no hidden nondeterminism, no semantic drift without surfaced change, and fail-closed operation.

**Observed: a closed-world source-authority pattern already exists.**
`packages/adeu_semantic_source/src/adeu_semantic_source/anm.py` is extremely relevant precedent. It forbids prose inference when no `D@1` blocks are present and fails closed on malformed structure. That is the exact temperament needed for ingress classification and operator registries.

**Observed: the repo already has the right ODEU membrane concept.**
`docs/support/ODEU_MEMBRANE_ARCHITECTURE.md` describes ODEU as a “stateful semantic front-end compiler with selective permeability, residual retention, escalation ports, and a re-entry channel,” with a state tuple `⟨Q_O,Q_E,Q_D,Q_U,R,J,Ξ,N⟩`. That is nearly the right conceptual backbone for the proposed turn compiler and refresh reducer.

**Observed: the repo already has strong runtime governance artifacts.**
`packages/adeu_agentic_de` already defines:

* domain packets,
* morph IR,
* interaction contracts,
* action proposals,
* membrane checkpoints,
* runtime state,
* action tickets,
* live turn admission/handoff/reintegration artifacts,
* workspace continuity admission/occupancy/reintegration artifacts.

The models are strict, content-addressed, and provenance-heavy. The checker enforces blocked/residualized/accepted states with explicit reason codes like `not_evaluable_yet`, `insufficient_evidence`, and `authority_missing`.

**Observed: agentic_de already enforces the right constitutional law for effectful action.**
`docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_FAMILY_v0.md` says:

* inferential search may remain free, but externally effective action may not;
* outputs are advisory until a governed gate entitles stronger effect;
* no hidden write/execute/dispatch boundary;
* unresolved/insufficient-evidence/authority-missing/not-evaluable may not be laundered into action;
* projections may express but may not mint authority.

That is the downstream governance layer the new ingress compiler should target.

**Observed: live harness and workspace continuity already carry origin/dependence tags.**
`packages/adeu_agentic_de/src/adeu_agentic_de/models.py` uses `field_origin_tags`, `field_dependence_tags`, and `root_origin_ids` in handoff, reintegration, occupancy, and continuity records. That is exactly the carry/provenance mechanism a turn compiler should reuse rather than invent anew.

**Observed: history semantics already reconstructs O/E/D/U, but only as advisory.**
`packages/adeu_history_semantics` defines source artifacts, preclassification, ledgers, theme anchors, ODEU reconstruction packets, and workspace snapshots. But its own models explicitly say:

* `source_authority_posture = "normalized_source_text_authoritative"`
* `interpretation_authority_posture = "advisory_overlay_only"`
* `workspace_synthesis_posture = "advisory_reconstruction_only"`

That is an excellent import/migration bridge, not a live continuity state engine.

**Observed: URM runtime already has orchestration/continuation/handoff structure.**
`packages/urm_runtime/src/urm_runtime/orchestration_state.py` defines `ContinuationBridgeRef`, `CompactionSeam`, `RoleHandoffEntry`, `OrchestrationStateSnapshot`, `ExecutionTopologyState`, `WriteLeaseState`. This is useful for live orchestration state, but it is about runtime topology and compaction lineage, not semantic ingress or ODEU carry.

### What is conceptually adjacent but incomplete

**Observed: `adeu_history_semantics` is adjacent but not the target.**
It preclassifies transcript-like history strictly and reconstructs ODEU overlays, but it is fundamentally a history import/reconstruction family. It does not replace a persistent, active, refreshed ODEU state.

**Observed: `agentic_de` starts too late in the pipeline.**
It assumes there is already a task scope, packet, proposal, and action class in play. It does not classify raw user utterances against a closed semantic registry.

**Observed: URM compaction surfaces are continuity of runtime streams, not continuity of typed meaning.**
They are useful, but they do not solve semantic carry law.

### What is missing

**Observed missing: no user-turn semantic ingress compiler.**
I did not find a package or family for closed-world user input classification, adjudication, or typed input-instance emission.

**Observed missing: no governed workflow operator registry.**
I did not find a declarative operator family where recurrent utterances compile into stable operator instances with slot schemas, sequencing law, review semantics, and commit policy.

**Observed missing: no repo-native parameter expansion layer.**
There is no distinct schema family that expands variables like `arc_family`, `artifact_family`, `review_scope`, or `commit_policy` into naming formulas, file locations, obligations, and transition rules.

**Observed missing: no ODEU turn refresh reducer.**
There is no package that updates persistent turn state by emitting typed ODEU deltas and pruning raw turn residue.

**Observed missing: no explicit commit-to-main governance family.**
In the inspected runtime governance surfaces, the exact action classes are bounded to things like `local_write` and `local_reversible_execute`. I did not observe a shipped governed action class for git commit/merge-to-main semantics. That matters for your worked example.

### Natural insertion points

**Inferred:** the insertion point should be a new family between user ingress and current runtime governance. It should compile into:

* typed input instance,
* optionally a bound operator instance,
* optionally an execution packet that then maps into `agentic_de` artifacts,
* and finally a turn-refresh delta that updates persistent ODEU state.

That family should lean on:

* `adeu_semantic_source` / `adeu_semantic_compiler` for registry authoring and pass discipline,
* `adeu_agentic_de` for effect governance,
* `urm_runtime` for session/orchestration,
* `adeu_history_semantics` only for bootstrap/import.

## 4. Semantic ingress architecture

The front-end should be a **turn ingress compiler**, not a prompt interpreter.

The pipeline I recommend is:

1. **Surface utterance capture**
   Bind the exact user text, current ODEU snapshot ref, registry version ref, session/runtime refs, and a normalized text hash. This stage emits a typed surface record and nothing more.

2. **Classifier proposal pass**
   Propose one or more candidate semantic input types from a **closed registry**. The candidate universe is finite and declared ahead of time. The output is a candidate packet, not a decision.

3. **Adjudication pass**
   Apply a declared advancement policy to the candidate packet. This pass may:

   * choose a single input type,
   * carry a bounded ambiguity set,
   * block,
   * route to human review,
   * or fall back to an explicit unmatched/freeform lane.

4. **Typed input instance emission**
   Emit a typed input instance artifact that binds:

   * selected input type,
   * evidence spans / supporting signals,
   * ambiguity posture,
   * active-context dependence,
   * and allowed downstream lanes.

The key law is:

> classification emits a typed claim about the utterance; it does not authorize execution, planning, or hidden operator instantiation.

### Ambiguity handling

Ambiguity should be first-class. The adjudication pass should be able to emit:

* `selected`
* `bounded_ambiguity`
* `blocked`
* `fallback_freeform`
* `escalate_for_disambiguation`

In ADEU terms, ambiguity is not an error to be silently resolved by internal prose. It is a typed residual state.

### Fallback handling

“Freeform” should not mean “open-world.” It should be an explicit registry member, such as `open_conceptual_discussion` or `unmatched_surface_utterance`.

That way, the system can still talk naturally while preserving the law that every ingress route is typed and declared.

## 5. Input type registry

I recommend a closed-world registry with a small, strong top-level algebra.

### Proposed ADEU-native input types

1. **`governed_workflow_operator_invocation`**
   The utterance is invoking a recurrent semantic operator family.

2. **`active_operator_rebinding_or_refinement`**
   The utterance modifies the active operator instance: change a slot, sequencing detail, review scope, or commit policy.

3. **`active_operator_control`**
   Pause, resume, abort, supersede, or branch the active operator.

4. **`artifact_review_or_assessment_request`**
   Review, assess, compare, verify, critique, or inspect a declared artifact scope.

5. **`schema_family_design_request`**
   Create or revise architecture, schema, family decomposition, governance doctrine, or compiler design.

6. **`state_or_continuity_query`**
   Ask what is active, blocked, pending, completed, or carried in the current ODEU/workflow state.

7. **`execution_authorization_or_commit_decision`**
   Explicit authorization, approval, commit/merge instruction, or release decision. This deserves its own type because it opens stronger deontic surfaces.

8. **`evidence_or_correction_declaration`**
   The user is supplying missing evidence, correcting a bound variable, or declaring an authoritative fact for current work.

9. **`open_conceptual_discussion`**
   Legitimate open discussion that should not automatically open operator or execution lanes.

10. **`unmatched_surface_utterance`**
    Explicit unmatched lane. This is the fail-safe, not a hidden escape hatch.

### Boundary rules

`governed_workflow_operator_invocation` is not the same as `execution_authorization_or_commit_decision`.
A user can ask for a workflow shape without authorizing its effectful steps.

`artifact_review_or_assessment_request` is not the same as `schema_family_design_request`.
The former is artifact-bound. The latter is family/control-plane design.

`active_operator_rebinding_or_refinement` is only available if an active operator exists in ODEU state.

### Conflict resolution

When multiple types are plausible, the adjudication law should be conservative:

* prefer **continuation of an active operator** over opening a new operator family, when the utterance clearly targets current work;
* prefer the **weaker semantic surface** when ambiguity would otherwise open stronger authority or execution lanes;
* never silently collapse `execution_authorization_or_commit_decision` into ordinary workflow invocation;
* when unresolved, emit a typed ambiguity packet rather than laundering a guess into state.

## 6. Governed workflow operators

The operator model should be treated as a first-class ADEU artifact family.

A governed operator is not a prompt template. It is a typed semantic function with declared law.

### Operator schema shape

Each operator family should define:

* `operator_family_id`
* `operator_intent_summary`
* `surface_invocation_patterns`
* `slot_schema`
* `required_slots`
* `default_profile`
* `parameter_expansion_profile_refs`
* `preconditions`
* `sequencing_graph`
* `role_allocation_matrix`
* `write_policy`
* `commit_policy`
* `review_policy`
* `expected_artifact_contracts`
* `postconditions`
* `allowed_follow_on_transitions`
* `blocking_reason_vocab`
* `carry_projection_rules`

### Why this is not a prompt

A prompt is open-text instruction plus hidden interpretation.
A governed operator is:

* a stable semantic object,
* with lawful free variables,
* lawful defaults,
* lawful step ordering,
* bounded artifact outputs,
* and explicit deontic semantics.

Natural language becomes only the **surface carrier** by which the operator is invoked or refined.

### Relation to existing repo surfaces

**Observed:** `agentic_de` already knows how to govern packets, proposals, checkpoints, and tickets.
**Inferred:** the new operator family sits **before** that, converting user utterances into the semantic object that later gets lowered into those governance lanes.

That separation matters:

* operator semantics decide **what workflow object this is**,
* runtime governance decides **what effect is allowed now**.

## 7. Parameter expansion architecture

This should be a distinct layer, not mere slot filling.

Binding says: “the utterance refers to `arc_family = X`.”
Expansion says: “given `arc_family = X`, here are the canonical files, artifact families, review obligations, continuity links, and admissible transitions.”

### The expansion problem

Parameters like these are not atomic strings:

* `arc_family`
* `slice_id`
* `artifact_family`
* `review_scope`
* `commit_policy`
* `subagent_profile`

They are repo-native semantic handles.

### Expansion outputs

Each bound parameter should expand into some combination of:

* canonical naming formulas,
* canonical path formulas,
* expected artifact families,
* required supporting artifacts,
* continuity obligations,
* allowed follow-up transitions,
* deontic constraints,
* runtime profile constraints.

### Example expansion classes

**`arc_family`** expands into:

* authoritative family doc(s),
* family-local artifact directories,
* expected closeout and starter families,
* continuity relation to successor arcs,
* default review and stop-gate obligations.

**`slice_id`** expands into:

* exact slice-scoped files or subtrees,
* expected supporting evidence,
* admissible operations on that slice,
* parent/child relation to larger arc family.

**`artifact_family`** expands into:

* expected file formulas,
* canonical locations,
* required companion artifacts,
* allowable statuses like draft/reviewed/committed/released.

**`review_scope`** expands into:

* what counts as a “quick check,” “bounded review,” “closeout assessment,” etc.,
* which checks are mandatory,
* which are advisory,
* what artifact proves completion.

**`commit_policy`** expands into:

* whether a commit/merge is even in-scope,
* what prior gates must be satisfied,
* whether human approval is required,
* whether the output remains uncommitted pending review.

**`subagent_profile`** expands into:

* allowed role,
* runtime profile,
* tool/capability envelope,
* handoff expectations,
* review/harvest obligations.

### How expansion should be implemented

**Inferred:** expansion should read compiled repo-native registries, likely authored in docs and compiled with a semantic-source discipline similar to `D@1`.

It should not infer these structures ad hoc from prose. That would re-open the same laundering seam you are trying to close.

### Current repo grounding

**Observed:** the repo already has the right ingredients for expansion sources:

* architecture/family docs,
* lock/slice/stop-gate compilation patterns,
* package and artifact topology,
* runtime profile surfaces,
* continuity/handoff artifacts.

**Observed missing:** there is no existing general expansion engine for operator parameters.

## 8. Stage-gated reasoning architecture

This is the heart of the design.

The right model is a sequence of **schema-constrained local arenas**. Each arena sees only an allowed candidate space, emits only a typed local result, and passes forward only a declared carry subset.

I would implement the turn compiler as a fixed pass graph.

### Arena 0: Surface normalization

**Candidate space:** raw utterance text plus current ODEU snapshot ref and registry refs.
**Output schema:** `semantic_input_surface_record@1`
**Advancement law:** normalized text hash and source binding must be valid.
**Unlocks:** input-type proposal only.
**What survives:** source text hash, spans, current-state refs. No semantics yet.

### Arena 1: Input-type proposal

**Candidate space:** members of the closed input-type registry only.
**Output schema:** `semantic_input_type_candidate_packet@1`
**Advancement law:** all candidates must be registry members with evidence/support fields.
**Unlocks:** type adjudication.
**What survives:** ranked candidates, support signals, ambiguity profile.

This arena may use any internal proposal machinery, but only the candidate packet crosses the boundary.

### Arena 2: Input-type adjudication

**Candidate space:** the candidate packet from Arena 1 plus declared advancement policy.
**Output schema:** `semantic_input_type_adjudication@1`
**Advancement law:** selected type must either satisfy a declared winner policy, or the output must explicitly carry bounded ambiguity/block/fallback.
**Unlocks:** one downstream lane only:

* operator resolution,
* review lane,
* state query lane,
* authorization lane,
* open discussion lane,
* unmatched lane.
  **What survives:** selected type or ambiguity set, reason codes, allowed next lane.

### Arena 3: Operator family resolution

Only runs when the selected input type is operator-related.

**Candidate space:** members of the closed operator registry only.
**Output schema:** `workflow_operator_candidate_packet@1` or direct adjudication record.
**Advancement law:** family must be registry-declared; no latent operator invention.
**Unlocks:** parameter binding.
**What survives:** selected family ref, competing families if bounded ambiguity is permitted.

### Arena 4: Parameter binding

**Candidate space:** operator slot schema, utterance spans, active ODEU state, and allowed defaults.
**Output schema:** `workflow_operator_binding@1`
**Advancement law:** every required slot must be:

* explicitly bound,
* inherited from active ODEU under declared law,
* defaulted under declared law,
* or marked unresolved.

No silent fill from internal reasoning.

**Unlocks:** parameter expansion or reproposal demand.
**What survives:** partially/fully bound slots, missing-slot register, provenance per slot.

### Arena 5: Parameter expansion

**Candidate space:** expansion profiles, repo-native registries, active ODEU refs, observed repo topology.
**Output schema:** `workflow_operator_expansion_frame@1`
**Advancement law:** required expansions must resolve to declared formulas or emit explicit unresolved/block status.
**Unlocks:** execution packet construction or human-review route.
**What survives:** expanded paths, artifact contracts, role allocations, review obligations, commit posture, unresolved expansions.

### Arena 6: Execution-packet construction

**Candidate space:** bound operator, expansion frame, current ODEU state, runtime capabilities.
**Output schema:** `workflow_execution_packet@1`
**Advancement law:** packet must bind all required upstream artifacts and downstream governance targets. It still does **not** mint live authority.
**Unlocks:** dry-run planning lane, `agentic_de` lowering, or blocked/escalated status.
**What survives:** exact work graph, role/handoff plan, artifact expectations, requested effect classes.

### Arena 7: Governance/effect lowering

**Candidate space:** execution packet plus current runtime/governance context.
**Output schema:** current repo already gives you most of this: domain packet, proposal, checkpoint, runtime state, ticket, admission/handoff/reintegration.
**Advancement law:** existing `agentic_de` laws.
**Unlocks:** actual observed effect or blocked/residual state.
**What survives:** accepted/rejected/residualized artifacts, tickets if any, reason-coded failure states.

### Arena 8: Turn refresh reduction

**Candidate space:** outputs from all prior arenas plus observed effects and active prior ODEU snapshot.
**Output schema:** `odeu_turn_delta@1`, `odeu_state_snapshot@1`, `residual_witness_packet@1`, `carry_prune_manifest@1`
**Advancement law:** only fields declared promotable by carry law may enter persistent state.
**Unlocks:** next turn.
**What survives:** the new ODEU state and retained witnesses. All unpromoted local residue is pruned.

### The disciplined “maze” principle

The crucial point is not “many stages.” It is:

* each stage has a **closed local candidate space**,
* each stage has a **typed output schema**,
* each edge has an **advancement law**,
* and each edge has a **carry allowlist**.

That is the disciplined form of stage-local reasoning descent.

## 9. Advancement policy library

Advancement law should be data, not hidden prose.

I would define a small library of reusable gate policies.

### `exclusive_winner_above_threshold`

Use for strongly mutually exclusive decisions like top-level input type classification.
Opens the next lane only if one candidate wins cleanly.

Risk: false precision theater if thresholds are arbitrary.
Mitigation: store threshold and margin in policy artifacts, and retain runner-up evidence.

### `exclusive_winner_with_margin`

Like above, but requires a lead margin over the next candidate.
Good when the cost of choosing the wrong stronger lane is high.

### `bounded_multi_hypothesis_carry`

Carry the top `k` candidates into the next stage under an explicit ambiguity posture.
Useful when later parameter binding or expansion can resolve the ambiguity lawfully.

Risk: combinatorial sprawl.
Mitigation: low `k`, explicit entropy cap, explicit downstream pruning law.

### `block_until_required_slots_bound`

Use at parameter binding.
Do not advance until required slots are bound/defaulted/inherited under law.

### `defaultable_slots_only`

Advance only if all missing slots belong to a declared defaultable set.
Prevents hidden invention.

### `human_review_required`

Use when ambiguity or deontic impact exceeds a declared ceiling.
Appropriate for authorization/commit decisions or when expansion touches sensitive scopes.

### `fallback_to_freeform_lane`

Use when no registry member wins and the work is not effectful.
Important: fallback is itself typed, not silent open-world escape.

### `authorization_gate_required`

Use when an operator includes effectful steps like write, execute, dispatch, or commit.
This should be separate from operator recognition.

## 10. Carry law and refresh reducer

Between turns, the continuity substrate should be a refreshed ODEU state, not transcript inheritance.

The best structure is to take the membrane formulation in `docs/support/ODEU_MEMBRANE_ARCHITECTURE.md` seriously:

`ODEUState = {Q_O, Q_E, Q_D, Q_U, R, J, Ξ, N}`

Where:

* `Q_O` = observed facts and witness refs
* `Q_E` = entitled/active execution state
* `Q_D` = deontic obligations and gating constraints
* `Q_U` = unresolved ambiguity and underdetermination
* `R` = retained residual witness register
* `J` = rejection/block log
* `Ξ` = escalation queue
* `N` = structured reproposal demand set

### What should survive

**Invariant ODEU memory**

* active arc/family context,
* active operator instance refs,
* durable repo/workspace identity refs,
* durable policy/profile refs.

**Active operator / workflow state**

* operator family id,
* bound parameters,
* current phase,
* outstanding tasks,
* review/commit posture,
* downstream entitlements actually obtained.

**Retained evidence residuals / witnesses**

* artifact ids,
* tickets/checkpoints,
* occupancy/reintegration reports,
* observed effect refs,
* authoritative correction/evidence supplied by user.

**Unresolved forks / blocking tensions**

* ambiguity packets,
* missing-slot demands,
* blocked reason codes,
* pending authorizations,
* escalation requirements.

### What should not survive

* raw chain-of-thought,
* raw tool chatter,
* internal candidate enumeration that was never emitted,
* prose rationalizations,
* transient scratch plans,
* verbose event logs once reduced into typed witnesses,
* any inference that was not promoted into a declared artifact.

### Promotion law

A field may survive only if it is emitted in a declared artifact schema and carries:

* provenance,
* authority posture,
* and dependence refs.

### Retention law

Retain only:

* state still needed for active work,
* evidence needed to justify current state,
* unresolved items still semantically live.

### Demotion law

When a workflow phase closes, demote detailed operator-internal state into:

* postcondition summary,
* artifact refs,
* retained witness refs,
* and maybe a compact completion record.

Do not keep the whole local execution transcript just because it once mattered.

### Pruning law

At end of turn, produce a `carry_prune_manifest@1` listing:

* what was promoted,
* what was retained as witness,
* what was discarded,
* and why discarding is lawful.

### Provenance law

Reuse the existing pattern already visible in `agentic_de`:

* `field_origin_tags`
* `field_dependence_tags`
* `root_origin_ids`

Those tags should become mandatory in ODEU delta and carry artifacts.

## 11. Anti-laundering laws

This section should be explicit because it is the constitutional core.

### 1. Closed-world ingress law

No user utterance may open a semantic lane not declared in the input-type registry.
Unmatched input routes to `unmatched_surface_utterance`, not hidden open-world reinterpretation.

### 2. Boundary emission law

Nothing crosses a stage boundary unless it is emitted in that stage’s declared output schema.
Internal reasoning is not carry.

### 3. Provenance-before-promotion law

No field may become continuity state unless it carries source refs, dependence refs, and authority posture.

### 4. Advisory non-promotion law

Candidate packets, hypotheses, projections, and summaries may inform, but may not become standing state or authority unless separately adjudicated and promoted.

### 5. Negative-state preservation law

`blocked`, `residualized`, `authority_missing`, `insufficient_evidence`, `not_evaluable_yet`, and drift/occupancy negatives are first-class.
They may not be compacted into “continued” or “done.”

### 6. Transcript non-authority law

Prior transcript is context only after explicit preclassification/import.
It is never ambient authority.

### 7. Prior-workspace non-authority law

Prior workspace state is context at most, not standing entitlement.
This is already consistent with the observed workspace continuity family.

### 8. Defaulting discipline law

Defaults may fill only slots explicitly declared defaultable.
A default may never silently stand in for missing authority, missing evidence, or missing semantic identity.

### 9. Summary non-equivalence law

A reasoning summary is not equivalent to state.
A compact description may accompany state, but may not replace the typed state record or its provenance.

### 10. No hidden bridge state law

A later stage may not rely on undeclared carry, hidden caches, or remembered internals from earlier stages.
If it matters, it must be in the carry schema.

### 11. No authority minting by projection law

Projection, expansion, or review may constrain action, but may not mint new authority.
This aligns with the observed `agentic_de` family law that projections may express but may not mint authority.

### 12. Re-entry law

Discarded residue may re-enter only by being reintroduced as explicit source or emitted artifact, not by “remembering” it silently.

## 12. Worked example

Take the utterance:

> “run sub-agent codex 5.3 high to do closeout step. In parallel main agent drafts the next starter bundle. Then does a quick check pass over closeout step. Then it commits closeout to main. And leaves starter bundle uncommitted for review”

I will show the target architecture, while distinguishing current repo limits.

### Step 1: input type classification

**Inferred classification result:**

* winner: `governed_workflow_operator_invocation`
* rejected alternates: `open_conceptual_discussion`, `execution_authorization_or_commit_decision`

Why not the authorization type? Because the utterance contains an operator-shaped workflow with sequencing and commit posture, not merely a naked approval decision.

### Step 2: operator family mapping

**Inferred operator family:**
`adeu_operator_family_arc_closeout_parallel_starter@1`

This family would encode the stable invariant shape:

* one closeout branch,
* one parallel starter-bundle draft branch,
* one bounded main-agent review pass over closeout,
* one closeout commit decision path,
* one starter-bundle review-hold path.

### Step 3: variable extraction

**Bound from utterance:**

* `subagent_profile = codex_5_3_high`
* `primary_work = closeout_step`
* `parallel_secondary_work = starter_bundle_draft`
* `main_agent_review_scope = quick_check_closeout`
* `closeout_commit_target = main`
* `starter_bundle_commit_posture = hold_uncommitted_for_review`

**Possibly inherited from active ODEU state, not said explicitly in the utterance:**

* `arc_family`
* `slice_id`
* `artifact_family`
* current repo/workspace scope
* default review formula
* exact starter-bundle naming formula

This is important: the architecture should **not** pretend the utterance fully determines those.

### Step 4: defaults

**Inferred lawful defaults:**

* review occurs after closeout draft completion,
* starter bundle drafting may run in parallel with closeout,
* quick check is bounded review, not full release assessment,
* starter bundle remains draft-only until separate review/authorization.

### Step 5: parameter expansion

This is where repo-native structure should appear.

If `arc_family` is already active in ODEU state, expansion can unfold it into:

* canonical closeout artifact families,
* canonical starter-bundle artifact families,
* expected doc/update locations,
* continuity obligations,
* allowed transitions after closeout,
* default review and stop-gate requirements.

If `arc_family` is **not** available, the correct result is **not** to guess.
The correct result is:

* residualize the operator binding,
* emit a reproposal demand in `N`,
* and ask for or infer from existing active ODEU state the missing arc identity.

That is a good example of anti-laundering doing its job.

### Step 6: execution packet

Assuming `arc_family` is already known in ODEU state, the compiled execution packet would contain substeps like:

1. `closeout_draft_task`

   * actor: `subagent(codex_5_3_high)`
   * output contract: closeout artifact bundle
   * effect posture: likely artifact-local draft/write only at first

2. `starter_bundle_draft_task`

   * actor: `main_agent`
   * output contract: starter bundle draft
   * effect posture: draft-only, uncommitted

3. `closeout_quick_check_task`

   * actor: `main_agent`
   * input: closeout artifact bundle
   * output: bounded review artifact or pass/fail review record

4. `closeout_commit_task`

   * actor: governed commit lane
   * precondition: quick-check pass
   * requested effect: commit closeout outputs to `main`

5. `starter_bundle_hold_task`

   * actor: carry reducer
   * postcondition: starter bundle left in review-hold state, not committed

### Step 7: current repo-grounded reality check

Here the repo matters.

**Observed:** the current shipped `agentic_de` action taxonomy is centered on exact action classes like `local_write` and `local_reversible_execute`.
**Observed:** I did not find a shipped governed action class for `commit_to_main`.

So in the current repo, a truthful lowering would be:

* closeout drafting and starter drafting may be lowerable into draft/write-oriented lanes,
* review/check artifacts are lowerable,
* but `commit closeout to main` is not yet a directly observed governed runtime action class.

So the compiled operator should currently end in one of two honest states:

* **target architecture state:** `closeout_commit_pending_authorization_family`
* **current repo state:** `blocked/out_of_scope` for the commit substep, while the rest of the workflow remains typed and governed

That distinction is exactly why operator semantics and runtime action semantics should be separate families.

### Step 8: ODEU deltas that survive the turn

Assuming closeout draft and starter draft are produced, and commit remains pending:

**`Q_O`**

* refs to closeout draft artifacts,
* refs to starter bundle draft artifacts,
* review artifact refs,
* observed workspace/runtime refs.

**`Q_E`**

* active operator instance id,
* bound slots,
* current phase = `closeout_reviewed_commit_pending`,
* role allocation state.

**`Q_D`**

* obligation: obtain commit authorization for closeout if desired,
* obligation: review starter bundle,
* any required evidence or stop-gate dependencies.

**`Q_U`**

* unresolved commit authorization if commit family not available or not approved,
* unresolved expansion items if any.

**`R`**

* retained witness bundle: review result, effect refs, operator binding provenance.

**`N`**

* reproposal demand such as `select_commit_lane` or `supply_arc_family`, if missing.

### Step 9: what gets pruned

* the classifier’s rejected candidates,
* the operator alternatives not chosen,
* raw internal planning chatter,
* raw tool traces once reduced into typed observation refs,
* prose reasoning about why the quick check passed,
* any non-promoted review discussion.

That is exactly the type of turn-local residue that should die unless promoted.

## 13. Proposed ADEU-native artifact stack

I would add a compact, coherent artifact stack.

### Ingress artifacts

* `adeu_semantic_input_type_registry@1`
* `adeu_semantic_input_surface_record@1`
* `adeu_semantic_input_type_candidate_packet@1`
* `adeu_semantic_input_type_adjudication@1`

### Operator artifacts

* `adeu_workflow_operator_registry@1`
* `adeu_workflow_operator_schema@1`
* `adeu_workflow_operator_candidate_packet@1`
* `adeu_workflow_operator_binding@1`
* `adeu_workflow_operator_expansion_frame@1`
* `adeu_workflow_execution_packet@1`

### Stage/gate artifacts

* `adeu_stage_arena_contract@1`
* `adeu_stage_arena_result@1`
* `adeu_advancement_policy_registry@1`

### Carry/refresh artifacts

* `adeu_odeu_state_snapshot@1`
* `adeu_odeu_turn_delta@1`
* `adeu_residual_witness_packet@1`
* `adeu_carry_prune_manifest@1`
* `adeu_anti_laundering_conformance_report@1`

### Repo-native authoring posture

**Inferred:** these should be authored the same way the repo increasingly authors other control-plane semantics:

* declarative docs/spec inputs,
* compiled deterministically,
* fail-closed on undeclared fields or invalid references,
* content-addressed where appropriate.

## 14. Recommended module/family decomposition

The cleanest decomposition is **one new umbrella family**, not five unrelated mini-families.

### Recommended new umbrella family

`ARCHITECTURE_ADEU_ODEU_TURN_COMPILER_FAMILY_v0.md`

That family should own three internal submodules:

1. **semantic ingress**
2. **governed operator compilation**
3. **turn refresh / carry reduction**

### Recommended package shape

A single package at first:

`packages/adeu_turn_compiler`

with submodules roughly like:

* `input_registry.py`
* `ingress.py`
* `adjudication.py`
* `operator_registry.py`
* `binding.py`
* `expansion.py`
* `stage_graph.py`
* `refresh.py`
* `models.py`

### What belongs together

Ingress, operator binding, and refresh belong together because they form one constitutional path:

* classify the turn,
* compile the workflow object,
* reduce the turn back into persistent state.

Splitting them too early would recreate the very hidden-boundary problem you are trying to solve.

### What should stay attached to existing families

* effect governance stays in `adeu_agentic_de`
* live session/orchestration stays in `urm_runtime`
* history import stays in `adeu_history_semantics`
* source/registry authoring discipline should reuse `adeu_semantic_source` / `adeu_semantic_compiler`

### What should be deferred

* generalized multi-operator planner
* broad open-world ontology growth
* commit-to-main live governance
* large profile registries for many subagents
* speculative cross-turn heuristic summarizers

### Why this decomposition fits the repo

A support note already says the minimum change set should follow existing seams, not create a second architecture. This recommendation does that:

* one new front-end compiler family,
* adapters into existing governance/runtime families,
* no reinvention of downstream action governance.

## 15. Order of implementation

### Stage 1: write the constitutional docs and schemas

Build the umbrella family doc and the first schema set:

* input type registry,
* operator schema,
* ODEU turn delta.

**Why first:** the repo already treats docs/specs as authority.
**Closure criterion:** registries compile deterministically and fail closed.
**Must be proved:** undeclared types/operators cannot be referenced.
**Do not widen yet:** no runtime execution integration.

### Stage 2: build closed-world ingress adjudication

Implement:

* surface record,
* candidate packet,
* adjudication artifact,
* explicit ambiguity/fallback handling.

**Why second:** everything else depends on correct lane selection.
**Closure criterion:** same utterance + same ODEU snapshot + same registry -> same adjudication artifact.
**Must be proved:** unmatched and ambiguous cases remain explicit.
**Do not widen yet:** no operator execution.

### Stage 3: build one operator family end-to-end

Implement one operator family only, with:

* slot binding,
* defaulting,
* missing-slot reproposal,
* expansion against one small repo-native schema domain.

**Why third:** this proves the architecture on a real recurrent workflow without sprawl.
**Closure criterion:** one utterance family compiles into a bound operator instance lawfully.
**Must be proved:** missing variables residualize rather than being guessed.
**Do not widen yet:** no operator registry explosion.

### Stage 4: build the turn refresh reducer

Implement:

* `odeu_state_snapshot`
* `odeu_turn_delta`
* `residual_witness_packet`
* `carry_prune_manifest`

**Why fourth:** this is the core shift away from transcript-centric continuity.
**Closure criterion:** after a turn, persistent state can be reconstructed from typed carry artifacts alone.
**Must be proved:** raw local reasoning is pruned; blockers and negatives survive explicitly.
**Do not widen yet:** no history import dependence for normal operation.

### Stage 5: lower execution packets into dry-run governed runtime artifacts

Connect operator execution packets to current `agentic_de` packet/proposal/checkpoint surfaces in dry-run or non-entitling mode.

**Why fifth:** runtime governance should remain downstream of typed compilation.
**Closure criterion:** operator compilation does not itself mint authority.
**Must be proved:** same operator packet lowers deterministically to the same governance packet set.
**Do not widen yet:** no live commit semantics.

### Stage 6: integrate one exact live slice using existing shipped action classes

Use one real governed live path only where the repo already has a lawful family, likely around the existing `local_write`-style slices.

**Why sixth:** proves the composition with real runtime without widening action class semantics.
**Closure criterion:** current-turn utterance -> typed ingress -> operator binding -> governance packet lineage -> observed effect -> reintegration -> ODEU delta.
**Must be proved:** no hidden bridge state, no transcript-as-witness.
**Do not widen yet:** no broader write/execute/dispatch classes than the current slice.

### Stage 7: only later, add commit/merge governance

This is separate work.

**Why last:** current repo does not yet show a shipped commit-to-main governance family.
**Closure criterion:** commit semantics are declared as their own governed action class family.
**Must be proved:** commit is not laundered from generic write authority.
**Do not widen yet:** no silent collapse from local write to repo-level commit.

## 16. Risks and failure modes

### Hidden open-world re-entry

A freeform fallback lane can become a smuggling path if later stages quietly treat it as operator input.
Mitigation: freeform lane must not unlock operator or execution surfaces without reclassification.

### Classification ambiguity pathologies

Too-eager exclusive selection can convert mild ambiguity into false certainty.
Mitigation: explicit ambiguity packets, conservative tie-breaking, weaker-lane preference.

### Operator explosion / registry sprawl

Every recurring phrase could become its own operator family.
Mitigation: make operator families coarse-grained and slot-rich; require a demonstrated recurrent invariant shape before new family admission.

### Overfitting to one workflow style

If the first operator family is too specific, the design becomes brittle.
Mitigation: build the operator schema around invariant structure and slot law, not one phrase pattern.

### Continuity artifacts becoming contamination carriers

A bad ODEU delta can become a new laundering surface.
Mitigation: strong promotion law, provenance tags, and anti-laundering conformance checks.

### Repo-coupling brittleness

Parameter expansion tied too tightly to current file names can break as the repo evolves.
Mitigation: expand through declared family registries and formulas, not ad hoc path scraping.

### False determinism theater

Putting thresholds in a registry does not make them inherently correct.
Mitigation: separate policy from evidence; preserve ambiguity and runner-up context where it matters.

### Active-operator overreach

The system might over-prefer “rebind current operator” when the user really meant “start a new workflow.”
Mitigation: active-operator continuation should be strong but rebuttable, with explicit adjudication evidence.

### Default laundering

Defaults can become hidden invention.
Mitigation: defaultability must be declared per slot and must never cover missing authority or identity.

### Premature effect widening

A successful local-write slice may tempt a jump to broader commit or merge semantics.
Mitigation: separate governed action families; no class-level widening from one exemplar path.

## 17. Final recommendation

The single best architectural direction is:

**build an ADEU ODEU turn compiler that treats each user turn as a closed-world compiled object, lowers only typed operator instances into governed runtime packets, and ends each turn with a typed ODEU refresh delta instead of transcript compaction.**

The first high-leverage family/module to build next is:

**one new umbrella family and package for semantic ingress + operator binding + turn refresh**
attached to the existing semantic compiler discipline upstream and to `agentic_de` / `urm_runtime` downstream.

The minimum viable but principled first slice is:

* one closed input-type registry,
* one real operator family for a recurrent workflow,
* one small parameter-expansion profile,
* one `odeu_turn_delta` reducer,
* and one dry-run lowering into current governed runtime artifacts,

while **explicitly not** widening into generic prompt interpretation, generalized operator sprawl, or commit-to-main execution until a distinct governed action family exists for that.

That gives you the core shift you want without breaking ADEU’s existing constitutional posture.
