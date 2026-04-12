Below I treat **ODEU** as **O / E / D / U**, with **E** the evidential-epistemic lane.

The right formal picture is **not** “a new logic with four truth values,” and **not** “probabilistic reasoning versus boolean reasoning.” It is a **typed product architecture**:

* an **entangled semantic field** outside the membrane,
* a **governed semantic compilation membrane** at the boundary,
* four **non-isomorphic lane state spaces** inside,
* **late partial booleanization** only where closure is lawful,
* and a **recursive re-entry loop** that lets failure in typed adjudication trigger renewed decomposition upstream.

The shortest rigorous statement is this:

> **ODEU is the last lawful semantic checkpoint before boolean or bounded downstream adjudication.**
> It does not replace logic. It makes logic locally applicable.

---

## 1. ODEU_MEMBRANE_ARCHITECTURE

### 1.1 Core formal object

Let the raw input domain be a **semantic field** rather than a proposition space:

[
x = \langle \sigma,\omega,\kappa,\alpha,\tau,h \rangle
]

Where:

* (\sigma) = source expressions: utterances, documents, observations, prompts, code comments, institutional text
* (\omega) = world-linked content: referents, states, events, latent hypotheses
* (\kappa) = discourse context and history
* (\alpha) = authority and policy frame
* (\tau) = task horizon and action horizon
* (h) = harvested priors, schemas, and procedures

Let the lane set be:

[
L = {O,E,D,U}
]

Let the upstream stochastic office propose a candidate decomposition:

[
\delta_i = \Sigma^\uparrow(x, r_i, h_i)
]

where (r_i) is any current reproposal request.

Then define the membrane itself as a **stateful, fail-closed partial transducer**:

[
M(x,\delta_i) = \langle Q_O,Q_E,Q_D,Q_U,R,J,\Xi,N \rangle
]

Where:

* (Q_l) = accepted lane packets for lane (l)
* (R) = residual register
* (J) = rejection log
* (\Xi) = escalation queue
* (N) = structured reproposal demand set

Then inside the membrane the lane kernels run:

[
K_l(Q_l) \to S_l
]

and the recomposer forms a settlement record:

[
G_i = C(S_O,S_E,S_D,S_U,R,\Xi)
]

Finally harvesting updates reusable procedure memory:

[
h_{i+1} = H(h_i, x, \delta_i, G_i)
]

### 1.2 What the membrane is

The membrane is best understood as a **governed semantic compilation membrane**.

It is compiler-like because it performs parsing, typing, normalization, and IR emission.
It is membrane-like because not everything crosses.
It is checkpoint-like because every crossing is reason-coded and fail-closed.
It is routing-like because accepted packets are sent to different kernels.

So the exact object is:

> **a stateful semantic front-end compiler with selective permeability, residual retention, escalation ports, and a re-entry channel.**

That is more precise than any single metaphor by itself.

### 1.3 Outside vs inside

**Outside the membrane** is the **semantic possibility field**:

* mixed natural-language content
* ambiguous reference
* under-fixed object boundaries
* mixed fact / norm / preference / scope signals
* candidate interpretations
* open probe plans
* proposal competition

This is not yet lawful adjudication space.

**Inside the membrane** is the **typed adjudication space**:

* lane-addressable packets
* lane-local kernels
* reason-preserving residual states
* escalation states
* bounded terminal alphabets
* settlement records
* harvested procedures and priors

### 1.4 What enters, what splits, what leaves

What enters the membrane is **not just text**. It is:

* the semantic field (x)
* one or more candidate decompositions (\delta_i)

What gets split is **not the token stream as a partition**, but the **semantic commitments** projected from it. A single source span may emit multiple lane packets. One sentence can simultaneously carry O, E, D, and U content.

What leaves the membrane in accepted form is:

* (Q_O): object packets
* (Q_E): evidential packets
* (Q_D): deontic packets
* (Q_U): utility packets

What stays residual is any content that is still meaningful but not yet lawfully closable, such as:

* ambiguous reference
* underdetermined scope
* insufficient evidence
* authority not yet fixed
* incomplete utility model
* cross-lane entanglement not yet cleanly decomposed

What gets rejected immediately is content whose **crossing attempt is illicit by form**, for example:

* a U-claim laundered as D
* an E-claim with no provenance anchor
* an O-claim with erased scope
* an unresolved fragment emitted as boolean
* a proposal that treats “not yet typed” as “false”

What gets escalated is content that **is lane-typed enough to recognize** but cannot be settled within the current authority envelope, such as:

* policy conflict
* missing authorized approver
* external oracle/human needed
* high-stakes unresolved contradiction
* sanctioned evidence source unavailable

What gets recomposed afterward is **not a single truth value**, but a **settlement vector**:

[
G = \langle S_O,S_E,S_D,S_U,R,\Xi,\text{execution posture}\rangle
]

That settlement can be positive, negative, blocked, escalated, deferred, or mixed.

### 1.5 Why ODEU is not “just four categories”

A lane is not merely a label on content. A lane assignment determines:

* which kernel may adjudicate the packet
* what counts as admissible input
* what closure conditions must hold
* what residual states are legal
* what escalation means
* what booleanization, if any, even means there

So ODEU is not a taxonomy of content types. It is a **taxonomy of adjudication regimes**.

### 1.6 Key architectural law

The raw semantic field does **not** admit a total valuation into ({0,1}) that preserves the relevant distinctions. Formally:

[
x \in \text{semantic field} ;\not\Rightarrow; v(x)\in{0,1}
]

because the field mixes at least four non-isomorphic dimensions: reference, warrant, norm, and preference.

The membrane exists precisely because boolean predicates are not yet lawfully formed outside it.

---

## 2. DUAL_OFFICE_STOCHASTIC_MODEL

The same stochastic substrate can appear on both sides of the membrane, but as **different offices with different contracts**.

### 2.1 Upstream stochastic office

Formal role:

[
\Sigma^\uparrow : \text{semantic field} \times \text{reproposal request} \times h \to \text{candidate decomposition}
]

Its job is to operate over **semantic possibility**, not adjudicated truth.

It performs:

* parse
* untangle
* propose decomposition
* infer object boundaries
* infer candidate scope
* detect ambiguity
* generate probes
* prepare candidate O/E/D/U packets
* preserve alternative readings when entitlement is not yet available

Its outputs are **proposals**, never governing decisions.

The upstream office is needed because before membrane crossing there often is **no stable object**, **no fixed scope**, **no admissible evidence relation**, **no settled rule envelope**, and **no lawful option set**. There is nothing yet for boolean logic to close over.

This office is therefore not “sloppy logic.” It is **search over undercompiled semantic structure**.

### 2.2 Downstream stochastic office

Formal role:

[
\Sigma^\downarrow_l : Q_l \times S_l \times h \to A_l
]

where (A_l) are advisory artifacts for lane (l): uncertainty surfaces, repair candidates, rankings, conflict summaries, re-entry triggers.

It performs:

* uncertainty management
* approximate ranking
* conflict balancing
* escalation detection
* evidence insufficiency handling
* non-final recommendation
* candidate repair
* re-entry trigger generation

This office is needed because even after lane typing, many lawful outputs are not immediately boolean:

* E may have conflicting admissible sources
* D may have policy conflicts or missing authority
* U may only admit a partial order or Pareto frontier
* O may still have fuzzy identity/boundary competition among typed candidates

So downstream stochasticity is not a fallback for “failed logic.” It is the machinery for **typed but still non-closed adjudication**.

### 2.3 Why these two offices must not be conflated

They differ in all three of the following:

**Object of operation.**
Upstream operates on entangled semantic material. Downstream operates on already typed packets.

**Question being asked.**
Upstream asks: “What is the right decomposition?”
Downstream asks: “Given this decomposition, what remains uncertain, repairable, rankable, or escalatory?”

**Authority status.**
Upstream proposals are non-authoritative. Downstream outputs are advisory under lane governance. Neither may override the inner office.

If they are conflated, three bad things happen immediately:

* parse ambiguity gets mistaken for evidential uncertainty
* policy conflict gets mistaken for semantic ambiguity
* utility preferences start smuggling themselves in as interpretive truth

---

## 3. ODEU_LANE_ADJUDICATION_MODEL

The key formal fact is that ODEU is **not one enlarged truth lattice**. It is a product of typed lane state spaces.

For each lane (l):

[
S_l = C_l \sqcup R_l \sqcup X_l
]

Where:

* (C_l) = closure states
* (R_l) = residual states
* (X_l) = escalation states

And globally:

[
S = S_O \times S_E \times S_D \times S_U
]

This is why ODEU is not generic many-valued logic. The non-boolean states are **typed and non-commensurable across lanes**.

### 3.1 O-lane

**Kernel role:** object typing, identity, boundary, scope, category consistency.

The O-kernel builds a typed object graph: what the claim/action is about, what counts as the same object, what is in scope, what decomposition is valid.

Typical booleanizable predicates here are:

* `same_entity(x,y)`
* `in_scope(x)`
* `well_typed(x)`
* `category_consistent(x)`

What remains non-boolean longer:

* alias sets not yet resolved
* blurred boundaries
* composite objects needing split
* scope conflict
* category ambiguity

Legitimate residual states include:

* `alias_unresolved`
* `boundary_ambiguous`
* `scope_conflict`
* `type_missing`
* `needs_object_split`

A lawful negative O-result is a true negative about a typed predicate, such as “x is not the same entity as y.”
That is very different from “I do not yet know what x refers to.”

### 3.2 E-lane

**Kernel role:** evidence sufficiency, provenance, admissibility, uncertainty, contradiction handling.

The E-kernel builds a warrant graph: what supports what, under what source rules, under what admissibility policy, with what conflicts.

Typical booleanizable predicates here are:

* `admissible(evidence_set)`
* `threshold_met(claim)`
* `contradicted(claim)`
* `provenance_valid(evidence_set)`

What remains non-boolean longer:

* insufficient evidence
* source conflict
* admissible but contradictory evidence
* uncalibrated threshold
* missing probe
* evidence exists but cannot yet be tied to the right object or scope

Legitimate residual states include:

* `insufficient_evidence`
* `inadmissible_source`
* `contradictory_support`
* `threshold_undeclared`
* `needs_probe`

Important distinction:

* `unsupported` means the current support threshold is not met
* `contradicted` means accepted support exists for the negation
* `insufficient_evidence` means there is no lawful closure yet

Those must not be collapsed.

### 3.3 D-lane

**Kernel role:** permission, prohibition, obligation, escalation, gate passage.

The D-kernel returns a **modal envelope**, not merely a truth value.

Canonical output states are things like:

* `permitted`
* `forbidden`
* `required`
* `must_escalate`
* `authority_missing`
* `policy_conflict`
* `out_of_scope`

Typical booleanizable predicates here are specific modal queries, for example:

* `permitted(action)`
* `within_policy(action)`
* `requires_approval(action)`

But the lane’s native alphabet is richer than boolean, because `required` is not the same as `permitted = true`, and `authority_missing` is not the same as `forbidden`.

Legitimate residual states include:

* `authority_missing`
* `policy_ambiguous`
* `policy_conflict`
* `requires_external_clearance`

This lane is the governing gate. It can veto an otherwise plausible or well-supported action.

### 3.4 U-lane

**Kernel role:** ranking lawful options, optimization within the lawful feasible set, tradeoff ordering.

The U-kernel builds an order structure, often not a total order:

* pairwise preference
* partial order
* tie class
* Pareto frontier
* threshold acceptance
* best-under-stated-objective

Typical booleanizable predicates here are narrow and model-dependent:

* `preferred(a,b)`
* `dominates(a,b)`
* `meets_utility_threshold(a)`

What remains non-boolean longer:

* incomparable options
* missing weights
* tradeoff frontiers
* underdeclared objective function
* multi-stakeholder conflict

Legitimate residual states include:

* `noncomparable`
* `pareto_frontier`
* `weights_missing`
* `needs_preference_input`

Critical bridge law:

[
U \text{ may only optimize over the D-passed feasible set}
]

or more explicitly:

[
\text{Feasible} = {a \mid O(a)\text{ typed} \land D(a)\in{\texttt{permitted},\texttt{required}}}
]

and U ranks only elements of `Feasible`.

Utility has no right to launder forbidden actions back into consideration.

### 3.5 Cross-lane bridge discipline

Proposal-time order can be free. Closure-time order is constrained.

The most important bridges are:

* O fixes reference and scope for E, D, and U
* E can constrain D where norms depend on factual preconditions
* D defines the lawful set for U
* U never grants permission on its own

So the architecture is not four disconnected bins. It is four distinct kernels with governed bridges.

---

## 4. BOOLEAN_PLACEMENT_AND_CLOSURE_LAW

Boolean is essential, but late.

### 4.1 What boolean is doing here

Boolean is not the semantic ontology. Boolean is a **terminal decision alphabet** for lane-local predicates once they have been lawfully formed.

Formally, for lane (l), boolean closure is only a **partial** operator:

[
\operatorname{Bool}_l(p)=
\begin{cases}
0 \text{ or } 1, & \text{if } CC_l(p) \
\bot_l(r), & \text{otherwise}
\end{cases}
]

Where:

* (CC_l(p)) = closure condition for predicate (p) in lane (l)
* (\bot_l(r)) = typed non-closure with reason (r)

This is the central reason-preservation law:

> **Non-closure is not the same thing as negative closure.**

So:

* `false` is lawful only when a typed predicate has been closed negatively
* `blocked`, `insufficient_evidence`, `authority_missing`, `noncomparable`, `poorly_typed`, `out_of_scope` are not `false`

### 4.2 Preconditions for lawful boolean closure

A predicate may be booleanized only after the relevant preconditions hold. In general these include:

* lane typing fixed
* scope fixed
* reference fixed
* kernel declared
* relevant residuals resolved or shown irrelevant
* provenance/admissibility satisfied where relevant
* authority frame bound where relevant
* lawful option set fixed where relevant
* utility model declared where relevant

Boolean closure is therefore **late** because it presupposes membrane work.

### 4.3 Which outputs can be booleanized directly

Directly booleanizable outputs include:

* O: identity, scope inclusion, category consistency
* E: admissibility, threshold met/not met, contradiction established
* D: permitted/not permitted for a specific action under a fixed policy frame
* U: pairwise preference or threshold satisfaction under a fixed utility model

### 4.4 Which outputs should remain typed residuals or bounded modal/order states

These should not be flattened to `true/false`:

* O: unresolved aliasing, fuzzy boundaries, scope conflict
* E: insufficient evidence, source conflict, threshold undeclared
* D: required, authority missing, policy conflict, escalate
* U: Pareto frontier, tie class, noncomparability, missing weights

So the terminal alphabets inside the architecture are of two kinds:

* **boolean closure** for narrow lane-local predicates
* **bounded non-boolean terminal states** for modality, escalation, and order structures

### 4.5 Pre-boolean vs peri-boolean

**Pre-boolean** means material has not yet been cleanly membrane-typed or kernel-prepared.

**Peri-boolean** means some local closure already exists, but the global settlement remains mixed.

Example:

[
\langle O=\texttt{typed}, E=\texttt{insufficient_evidence}, D=\texttt{authority_missing}, U=\texttt{not_invoked}\rangle
]

That is a fully lawful settlement record. It is not a truth value.

### 4.6 What happens when one lane closes and another does not

The result is a **partial settlement vector**, not a forced scalar collapse.

Examples:

* if D closes as `forbidden`, action execution is vetoed even if U never runs
* if O closes but E stays `insufficient_evidence`, the claim remains unresolved, not false
* if U produces a ranking but D is still open, the ranking is advisory only
* if D yields `required(single_action)`, U may be unnecessary

So boolean closure is lane-local and guarded; global settlement is vectorial.

---

## 5. RECURSIVE_VETO_AND_REPROPOSAL_LOOP

This is the architectural heart.

### 5.1 Formal loop

At pass (i):

1. **Outer stochastic proposal**
   [
   \delta_i = \Sigma^\uparrow(x, r_i, h_i)
   ]

2. **Membrane split**
   [
   M(x,\delta_i)=\langle Q_O,Q_E,Q_D,Q_U,R,J,\Xi,N\rangle
   ]

3. **Lane-local adjudication**
   [
   S_l^i = K_l(Q_l)
   ]

4. **Inner-office review**
   [
   G_i = C(S_O^i,S_E^i,S_D^i,S_U^i,R,\Xi)
   ]

5. **Inner decision**
   [
   a_i \in {\texttt{accept}, \texttt{partial_accept}, \texttt{reject}, \texttt{defer}, \texttt{escalate}}
   ]

6. **Reproposal generation if needed**
   [
   r_{i+1}=R^{\star}(G_i)
   ]

7. **Re-entry**
   [
   \delta_{i+1}=\Sigma^\uparrow(x,r_{i+1},h_i)
   ]

### 5.2 What the inner veto actually is

The inner office does not merely say no. It emits a **structured veto**.

A proper veto specifies at least:

* blocking lane
* reason code
* required probe or repair
* required retyping or rescoping
* frozen accepted substructures
* prohibited rewrites
* escalation target if any
* priority or severity

So a veto is not just rejection. It is a constrained demand for better decomposition.

### 5.3 Why recursion works

Recursion works because the same stochastic substrate can occupy two different contracts:

* **before the membrane**, it searches over possible decompositions
* **after the membrane**, it searches over typed uncertainty, repair, and ranking

The substrate is shared. The office is not.

The inner office gives the architecture its asymmetry: the outer court may explore; the inner office decides what crosses.

### 5.4 Freeze law

A good recursive system does not restart from semantic zero each pass.

Once some structure is accepted, it should enter a **frozen accepted core**:

[
F_i \subseteq \bigcup_{l \in L} Q_l^i
]

And future passes must preserve (F_i) unless there is an explicit revision reason.

This prevents two bad pathologies:

* endless drift from pass to pass
* wholesale rewrites caused by local failure in one lane

### 5.5 Why structured reproposal matters

Without structured reproposal, failure produces paralysis.

The architecture must turn blocked states into actionable upstream demands such as:

* `resolve_alias(x)`
* `collect_admissible_evidence(claim,candidate_sources)`
* `bind_authority_frame(policy_scope)`
* `declare_utility_weights(option_set,stakeholders)`

That is what makes recursion productive rather than circular.

### 5.6 Micro-trace

Take the entangled instruction:

> “Cancel the order if policy allows; if both candidates qualify, choose the cheaper lawful route; I may mean order 118 or 181.”

A lawful pass looks like this:

* O emits a residual: `alias_unresolved(order_118, order_181)`
* E may emit `needs_probe` for qualification facts
* D emits a typed query: `permitted(cancel(order_x))?`
* U emits a criterion packet: `minimize_cost within lawful options`

The inner office does **not** emit `false`. It emits a reproposal request: resolve intended order identity and collect qualification facts. On the next pass, once O and E are cleaner, D can close, and only then may U rank the lawful options.

That is the membrane in action.

---

## 6. HARVESTING_AND_PROCEDURE_COMPILATION_MODEL

The system should not only recurse. It should **learn procedures**.

### 6.1 Harvest operator

Define:

[
h_{i+1}=h_i \cup \operatorname{Harvest}(x,\delta_i,G_i,\text{trace}_i)
]

Where `Harvest` compiles accepted structure into reusable artifacts.

### 6.2 What gets harvested

At minimum, successful adjudication traces can compile into:

* **reusable schemas**
  canonical packet shapes, bridge constraints, closure guards

* **search priors**
  better upstream proposal conditioning for similar domains

* **escalation templates**
  repeatable routing patterns for policy conflict, authority absence, high-stakes ambiguity

* **admissibility heuristics**
  evidence-source filters, threshold defaults, provenance expectations

* **decomposition patterns**
  recurring ways entangled input tends to split across O/E/D/U

* **recomposition recipes**
  stable ways of turning lane vectors into settlement outputs

* **repair templates**
  if reason code X occurs in lane Y, ask probe Z or freeze substructure W

### 6.3 What harvesting is not

Harvest is not new authority from nowhere.

A harvested procedure is a **prior**, a **template**, a **conditioner**, or a **playbook**, not a self-authenticating truth source.

That matters because otherwise institutional learning would become authority laundering.

### 6.4 Human and machine relevance

Humans already do this informally:

* legal teams accumulate escalation playbooks
* engineers accumulate debugging templates
* mathematicians accumulate proof tactics
* editors accumulate revision heuristics

The architecture simply makes that process typed, explicit, replayable, and attachable to reason codes.

### 6.5 Why missing harvest is costly

Without harvest, the system keeps paying full search cost for recurrent cases.
With harvest, successful traces reduce future membrane load.

So the architecture is not only veto-based. It is **procedure-building**.

---

## 7. STRICT_DOMAIN_IMPLICIT_MEMBRANE_THEORY

This architecture explains why mathematics and code already work relatively well.

### 7.1 Mathematics

In mathematics, much of the membrane is already externalized:

* **O** is pre-built by formal objects, definitions, variable binding, theorem statements
* **E** is pre-built by proof obligations, derivation rules, and accepted proof witnesses
* **D** is pre-built by rule admissibility: what inference steps are allowed
* **U** is often secondary: proof elegance, brevity, generality, computational tractability

So the difficult work is often not raw membrane construction, but proof search inside a strongly typed space.

Boolean closure arrives early because predicates are already well-formed.

### 7.2 Code

In code, the same pattern holds:

* **O** is pre-built by syntax trees, type systems, module boundaries, explicit identifiers
* **E** is pre-built by compiler output, tests, runtime traces, static analysis, logs
* **D** is pre-built by language rules, API contracts, capability policies, deployment rules
* **U** is pre-built enough to talk about performance, readability, maintainability, latency

Again, the membrane is partially pre-built by the domain itself.

### 7.3 Why natural language is harder

In entangled natural-language or institutional reasoning:

* reference is implicit
* scope is floating
* evidence and hearsay mix
* obligations and suggestions blur
* utility criteria are often hidden or contested

So the membrane must be built much more explicitly on each pass.

That is why current systems can look highly capable in math/code but unstable in open institutional or conversational reasoning. The former arrives half-compiled.

### 7.4 Strong statement

Strict domains are successful not because they “need less reasoning,” but because they contribute heavy **pre-compiled membrane structure** before the model even begins.

---

## 8. MEMBRANE_FAILURE_MODE_TAXONOMY

Here are the major failure modes in the architecture.

1. **Premature booleanization.**
   Raw or under-typed material is forced into yes/no before closure conditions hold. Repair: require lane typing, scope fixation, and reason-preserving non-closure states.

2. **Lane mixing.**
   O/E/D/U material is cross-laundered so that one lane silently adjudicates another. Repair: explicit lane kernels and bridge rules.

3. **Treating unresolved as false.**
   `insufficient_evidence`, `authority_missing`, `underdetermined`, or `noncomparable` get collapsed into negative truth. Repair: reason preservation law.

4. **Treating advisory output as governing output.**
   A ranking, heuristic, or downstream confidence hint gets treated as permission or truth. Repair: explicit authority flags on every output.

5. **Outer stochastic court usurping the inner office.**
   A plausible decomposition or high-confidence proposal is treated as accepted merely because it is compelling. Repair: membrane acceptance tokens and veto authority.

6. **Over-conservative inner veto causing paralysis.**
   Everything uncertain is rejected instead of residualized, escalated, or partially accepted. Repair: richer bounded terminal states and partial-accept paths.

7. **Missing harvesting.**
   The architecture solves the same class of case repeatedly without compiling procedures. Repair: mandatory trace harvesting for recurrent success and recurrent block patterns.

8. **False certainty from E-lane compression.**
   A rich evidential graph is crushed into one confidence score, hiding provenance, contradiction, and admissibility structure. Repair: keep warrant graphs and reason codes explicit.

9. **D-lane laundering into U-lane convenience.**
   What is easy or cheap gets treated as what is allowed. Repair: D must gate U; utility cannot authorize.

10. **Inner-office decisions that fail to emit structured reproposal requests.**
    The system says “no” but cannot say what would make a future “yes” possible. Repair: every veto must specify block site, reason, and demanded repair.

11. **Scope collapse.**
    A local reading silently becomes a global impossibility or identity claim. Repair: explicit scope references and membrane rejection of scope-erasing crossings.

12. **Reason-code loss.**
    The architecture records only outcome class, not why it failed. Repair: every non-closure state carries lane, reason code, recoverability, and escalation posture.

A compact way to say all of this is:

> **The architecture fails whenever it forgets that typed non-closure is semantically real.**

---

# Machine-checkable schema blocks

Below are compact JSON Schema blocks for later hardening into compiler/checkpoint components.

### `semantic_membrane_architecture@1`

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "semantic_membrane_architecture@1",
  "title": "semantic_membrane_architecture@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "membrane_kind",
    "lanes",
    "outside_domain",
    "inside_domain",
    "ports",
    "operators",
    "authority_model",
    "reason_preservation_law",
    "reentry_enabled",
    "boolean_placement"
  ],
  "properties": {
    "schema": { "const": "semantic_membrane_architecture@1" },
    "membrane_kind": { "const": "governed_semantic_compilation_membrane" },
    "lanes": { "const": ["O", "E", "D", "U"] },
    "outside_domain": {
      "type": "object",
      "additionalProperties": false,
      "required": ["semantic_field_components", "proposal_status"],
      "properties": {
        "semantic_field_components": {
          "type": "array",
          "items": {
            "enum": [
              "utterance_stream",
              "world_state_refs",
              "context",
              "authority_frame",
              "task_frame",
              "background_priors"
            ]
          },
          "uniqueItems": true,
          "minItems": 1
        },
        "proposal_status": { "const": "entangled_preboolean" }
      }
    },
    "inside_domain": {
      "type": "object",
      "additionalProperties": false,
      "required": ["compiled_objects", "state_space_kind"],
      "properties": {
        "compiled_objects": {
          "type": "array",
          "items": {
            "enum": [
              "lane_packets",
              "lane_kernels",
              "residual_register",
              "escalation_queue",
              "settlement_record",
              "harvest_store"
            ]
          },
          "uniqueItems": true,
          "minItems": 1
        },
        "state_space_kind": { "const": "typed_product_state_space" }
      }
    },
    "ports": {
      "type": "object",
      "additionalProperties": false,
      "required": [
        "ingress",
        "accepted_egress",
        "residual_egress",
        "escalation_egress",
        "reentry_egress"
      ],
      "properties": {
        "ingress": { "const": ["semantic_field", "candidate_decomposition"] },
        "accepted_egress": { "const": ["O_packets", "E_packets", "D_packets", "U_packets"] },
        "residual_egress": { "const": "residual_register" },
        "escalation_egress": { "const": "escalation_queue" },
        "reentry_egress": { "const": "reproposal_request" }
      }
    },
    "operators": {
      "type": "array",
      "items": {
        "enum": [
          "typing",
          "lane_projection",
          "normalization",
          "rejection",
          "residualization",
          "escalation",
          "recomposition",
          "reproposal_emission"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    },
    "authority_model": {
      "type": "object",
      "additionalProperties": false,
      "required": ["outer_stochastic_status", "inner_office_status"],
      "properties": {
        "outer_stochastic_status": { "const": "proposal_only" },
        "inner_office_status": { "const": "authoritative_veto_and_acceptance" }
      }
    },
    "reason_preservation_law": { "const": true },
    "reentry_enabled": { "const": true },
    "boolean_placement": { "const": "late_lane_local_or_bounded_terminal" }
  }
}
```

### `stochastic_office_profile@1`

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "stochastic_office_profile@1",
  "title": "stochastic_office_profile@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "office_side",
    "substrate_relation",
    "decision_rights",
    "input_kinds",
    "output_kinds",
    "permitted_operations",
    "forbidden_operations",
    "accepts_reentry_requests",
    "emits_reentry_requests"
  ],
  "properties": {
    "schema": { "const": "stochastic_office_profile@1" },
    "office_side": { "enum": ["upstream", "downstream"] },
    "substrate_relation": { "const": "shared_reasoning_substrate_role_differentiated" },
    "decision_rights": { "enum": ["proposal_only", "advisory_under_inner_office"] },
    "input_kinds": {
      "type": "array",
      "items": {
        "enum": [
          "entangled_semantic_field",
          "candidate_lane_packets",
          "accepted_lane_packets",
          "lane_state",
          "reproposal_request",
          "harvested_priors"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    },
    "output_kinds": {
      "type": "array",
      "items": {
        "enum": [
          "candidate_decomposition",
          "probe_plan",
          "repair_candidate",
          "uncertainty_surface",
          "ranking_hint",
          "reentry_trigger"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    },
    "permitted_operations": {
      "type": "array",
      "items": {
        "enum": [
          "parse",
          "untangle",
          "boundary_inference",
          "scope_inference",
          "packet_proposal",
          "probe_generation",
          "repair_suggestion",
          "approximate_ranking",
          "conflict_balancing",
          "uncertainty_management"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    },
    "forbidden_operations": {
      "type": "array",
      "items": {
        "enum": [
          "mint_governing_authority",
          "collapse_unresolved_to_false",
          "override_inner_veto",
          "launder_utility_into_deontics",
          "launder_deontics_into_utility"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    },
    "accepts_reentry_requests": { "type": "boolean" },
    "emits_reentry_requests": { "type": "boolean" }
  }
}
```

### `odeu_lane_packet@1`

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "odeu_lane_packet@1",
  "title": "odeu_lane_packet@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "packet_id",
    "lane_id",
    "source_anchor_ids",
    "scope_ref",
    "normalized_payload",
    "dependencies",
    "admissibility_state",
    "reason_codes",
    "bridge_constraints",
    "proposed_kernel"
  ],
  "properties": {
    "schema": { "const": "odeu_lane_packet@1" },
    "packet_id": {
      "type": "string",
      "pattern": "^odeu_pkt:[A-Za-z0-9._:-]+$"
    },
    "lane_id": { "enum": ["O", "E", "D", "U"] },
    "source_anchor_ids": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "minItems": 1,
      "uniqueItems": true
    },
    "scope_ref": { "type": "string", "minLength": 1 },
    "normalized_payload": { "type": "object" },
    "dependencies": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "uniqueItems": true
    },
    "admissibility_state": {
      "enum": ["candidate", "accepted", "rejected", "residualized", "escalated"]
    },
    "reason_codes": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "uniqueItems": true
    },
    "bridge_constraints": {
      "type": "array",
      "items": {
        "enum": [
          "requires_scope_fix",
          "requires_provenance",
          "requires_authority",
          "lawful_option_set_only",
          "no_unresolved_to_false",
          "no_lane_laundering"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    },
    "proposed_kernel": { "type": "string", "minLength": 1 }
  }
}
```

### `lane_adjudication_kernel@1`

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "lane_adjudication_kernel@1",
  "title": "lane_adjudication_kernel@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "lane_id",
    "kernel_role",
    "decision_domain",
    "input_requirements",
    "booleanizable_predicates",
    "bounded_output_states",
    "residual_states",
    "escalation_triggers",
    "forbidden_collapses",
    "reentry_request_fields"
  ],
  "properties": {
    "schema": { "const": "lane_adjudication_kernel@1" },
    "lane_id": { "enum": ["O", "E", "D", "U"] },
    "kernel_role": { "type": "string", "minLength": 1 },
    "decision_domain": { "type": "string", "minLength": 1 },
    "input_requirements": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "minItems": 1,
      "uniqueItems": true
    },
    "booleanizable_predicates": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "uniqueItems": true
    },
    "bounded_output_states": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "minItems": 1,
      "uniqueItems": true
    },
    "residual_states": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "minItems": 1,
      "uniqueItems": true
    },
    "escalation_triggers": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "uniqueItems": true
    },
    "forbidden_collapses": {
      "type": "array",
      "items": {
        "enum": [
          "unresolved_to_false",
          "utility_to_deontic",
          "deontic_to_utility",
          "evidence_to_truth_without_scope",
          "scope_ambiguity_to_identity",
          "ranking_forbidden_options"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    },
    "reentry_request_fields": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "minItems": 1,
      "uniqueItems": true
    }
  }
}
```

### `boolean_closure_condition@1`

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "boolean_closure_condition@1",
  "title": "boolean_closure_condition@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "lane_id",
    "predicate_name",
    "closure_level",
    "closure_preconditions",
    "cross_lane_dependencies",
    "closed_output_alphabet",
    "nonclosure_output_kinds",
    "negative_closure_distinct_from_nonclosure"
  ],
  "properties": {
    "schema": { "const": "boolean_closure_condition@1" },
    "lane_id": { "enum": ["O", "E", "D", "U"] },
    "predicate_name": { "type": "string", "minLength": 1 },
    "closure_level": { "enum": ["lane_local", "global_execution", "global_reporting"] },
    "closure_preconditions": {
      "type": "array",
      "items": {
        "enum": [
          "lane_typed",
          "scope_fixed",
          "reference_fixed",
          "kernel_declared",
          "relevant_residuals_resolved_or_irrelevant",
          "provenance_admissible",
          "authority_frame_bound",
          "lawful_option_set_fixed",
          "utility_model_declared"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    },
    "cross_lane_dependencies": {
      "type": "array",
      "items": { "enum": ["O", "E", "D", "U"] },
      "uniqueItems": true
    },
    "closed_output_alphabet": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "minItems": 1,
      "uniqueItems": true
    },
    "nonclosure_output_kinds": {
      "type": "array",
      "items": {
        "enum": [
          "underdetermined",
          "insufficient_evidence",
          "blocked",
          "escalated",
          "out_of_scope",
          "poorly_typed",
          "noncomparable",
          "needs_probe"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    },
    "negative_closure_distinct_from_nonclosure": { "const": true }
  }
}
```

### `recursive_reproposal_loop@1`

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "recursive_reproposal_loop@1",
  "title": "recursive_reproposal_loop@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "loop_id",
    "same_substrate_different_offices",
    "stages",
    "inner_veto_actions",
    "reproposal_request_fields",
    "freeze_law",
    "termination_conditions",
    "max_passes",
    "harvest_on_accept"
  ],
  "properties": {
    "schema": { "const": "recursive_reproposal_loop@1" },
    "loop_id": { "type": "string", "minLength": 1 },
    "same_substrate_different_offices": { "const": true },
    "stages": {
      "const": [
        "upstream_proposal",
        "membrane_split",
        "lane_adjudication",
        "inner_office_review",
        "reproposal_request",
        "upstream_reproposal",
        "termination_or_repeat"
      ]
    },
    "inner_veto_actions": {
      "type": "array",
      "items": { "enum": ["accept", "partial_accept", "reject", "defer", "escalate"] },
      "uniqueItems": true,
      "minItems": 1
    },
    "reproposal_request_fields": {
      "type": "array",
      "items": {
        "enum": [
          "blocking_lane",
          "reason_code",
          "required_probe",
          "required_retyping",
          "frozen_substructures",
          "prohibited_rewrites",
          "escalation_target",
          "priority"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    },
    "freeze_law": {
      "type": "object",
      "additionalProperties": false,
      "required": [
        "accepted_substructures_persist",
        "revision_requires_reason_code"
      ],
      "properties": {
        "accepted_substructures_persist": { "const": true },
        "revision_requires_reason_code": { "const": true }
      }
    },
    "termination_conditions": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "minItems": 1,
      "uniqueItems": true
    },
    "max_passes": { "type": "integer", "minimum": 1 },
    "harvest_on_accept": { "type": "boolean" }
  }
}
```

### `harvested_procedure_template@1`

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "harvested_procedure_template@1",
  "title": "harvested_procedure_template@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "procedure_id",
    "source_trace_ref",
    "trigger_signature",
    "compiled_assets",
    "invariants",
    "reuse_scope",
    "authority_status",
    "feeds_back_to"
  ],
  "properties": {
    "schema": { "const": "harvested_procedure_template@1" },
    "procedure_id": {
      "type": "string",
      "pattern": "^odeu_proc:[A-Za-z0-9._:-]+$"
    },
    "source_trace_ref": { "type": "string", "minLength": 1 },
    "trigger_signature": {
      "type": "object",
      "additionalProperties": false,
      "required": ["domain_class", "lane_pattern", "outcome_pattern"],
      "properties": {
        "domain_class": { "type": "string", "minLength": 1 },
        "lane_pattern": {
          "type": "array",
          "items": { "enum": ["O", "E", "D", "U"] },
          "uniqueItems": true,
          "minItems": 1
        },
        "outcome_pattern": { "type": "string", "minLength": 1 }
      }
    },
    "compiled_assets": {
      "type": "array",
      "items": {
        "enum": [
          "decomposition_pattern",
          "probe_plan",
          "search_prior",
          "admissibility_heuristic",
          "escalation_template",
          "closure_recipe",
          "recomposition_recipe"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    },
    "invariants": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "minItems": 1,
      "uniqueItems": true
    },
    "reuse_scope": { "type": "string", "minLength": 1 },
    "authority_status": {
      "enum": [
        "prior_not_authority",
        "approved_template_under_current_governance"
      ]
    },
    "feeds_back_to": {
      "type": "array",
      "items": {
        "enum": [
          "upstream_office",
          "membrane_checkpoint",
          "lane_kernels",
          "downstream_office",
          "search_conditioning"
        ]
      },
      "uniqueItems": true,
      "minItems": 1
    }
  }
}
```

### `membrane_failure_report@1`

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "membrane_failure_report@1",
  "title": "membrane_failure_report@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "failure_id",
    "failure_class",
    "phase",
    "affected_lanes",
    "symptom",
    "root_cause",
    "reason_code_loss",
    "bad_collapse",
    "recommended_repair",
    "severity"
  ],
  "properties": {
    "schema": { "const": "membrane_failure_report@1" },
    "failure_id": {
      "type": "string",
      "pattern": "^odeu_fail:[A-Za-z0-9._:-]+$"
    },
    "failure_class": {
      "enum": [
        "premature_booleanization",
        "lane_mixing",
        "unresolved_as_false",
        "advisory_as_governing",
        "outer_usurps_inner",
        "over_veto_paralysis",
        "missing_harvest",
        "false_e_certainty",
        "d_into_u_laundering",
        "missing_reproposal_request",
        "scope_collapse",
        "reason_code_loss"
      ]
    },
    "phase": {
      "enum": [
        "upstream_stochastic",
        "membrane_checkpoint",
        "lane_kernel",
        "downstream_stochastic",
        "recomposition",
        "harvest"
      ]
    },
    "affected_lanes": {
      "type": "array",
      "items": { "enum": ["O", "E", "D", "U"] },
      "uniqueItems": true,
      "minItems": 1
    },
    "symptom": { "type": "string", "minLength": 1 },
    "root_cause": { "type": "string", "minLength": 1 },
    "reason_code_loss": { "type": "boolean" },
    "bad_collapse": {
      "enum": [
        "none",
        "unresolved_to_false",
        "advisory_to_governing",
        "utility_to_deontic",
        "deontic_to_utility",
        "evidence_to_truth",
        "scope_to_identity"
      ]
    },
    "recommended_repair": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 },
      "minItems": 1,
      "uniqueItems": true
    },
    "severity": { "enum": ["low", "medium", "high", "critical"] }
  }
}
```

## Bottom line

The strongest compressed formulation is this:

* **Outside the membrane**: semantic possibility, entanglement, proposal competition.
* **At the membrane**: typed semantic compilation, fail-closed routing, residualization, escalation, veto.
* **Inside the membrane**: lane-local kernels with non-identical state spaces.
* **Boolean**: late, local, conditional closure over already typed predicates.
* **Downstream stochasticity**: typed uncertainty, ranking, repair, escalation, re-entry generation.
* **Recursion**: structured reproposal driven by reason-coded failure, not blind looping.
* **Harvest**: successful traces become procedures, priors, and institutional memory.
* **Strict domains**: succeed because much membrane work is already precompiled.

So ODEU is neither “above logic” in a vague sense nor “instead of logic.” It is the **governed membrane that makes downstream logic, bounded control states, and recursive procedure-building lawful in the first place.**
