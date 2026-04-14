## Design note: endogenous cross-lane alignment by coupled boundary subdynamics

### 1. Executive thesis

The right formal picture is not

[
O \longleftrightarrow Z \longleftrightarrow D
]

with some third bridge object (Z) that mediates, translates, and settles meaning.

The right picture is:

* (O) remains ontically native.
* (D) remains deontically native.
* each lane contains a **pair-specific membrane-facing boundary band**,
* each boundary band carries both:

  1. a native exportable slice, and
  2. an imported image of the other lane,
* cross-lane influence is admitted only through **typed, witnessed, membrane-lawful boundary packets**,
* the coupled boundary bands may then synchronize,
* and the “bridge” is nothing over and above the induced coherence regime of that synchronization.

So the bridge is **not** a third sovereign layer. It is an **endogenous regime** in the product of the native lanes’ boundary dynamics.

> **Central distinction**
> The membrane is not a place where full lanes talk to each other.
> It is the law that governs which projected boundary images may lawfully couple.

That gives the architecture three sharply distinct objects:

1. **full lane dynamics** in (O) and (D),
2. **membrane-facing boundary subdynamics** inside (O) and (D),
3. **the induced bridge regime**, which is a coherence relation or attractor over lawful packet-pairs and packet-histories.

Downstream closure may rely on the lawful state of that induced regime without pretending that full ontic and full deontic states have become identical.

---

### 2. Why the bridge-layer picture is wrong or incomplete

Suppose one introduces an explicit bridge state (z_t \in Z) with

[
z_{t+1} = H(z_t, r_O(o_t), r_D(d_t)),
]

and then lets both lanes or downstream closure depend on (z_t).

That creates an immediate fork.

If (Z) has **no independent semantic content**, then it is reducible to a deterministic report over already-exported packet pairs. In that case it is not a real layer and adds no architecture.

If (Z) **does** have independent semantic content, then one of five failures occurs.

**Bridge-layer laundering risk.**
If (z_t) can settle disagreement not already settled by native witnesses in (O) or (D), then (Z) has minted authority.

**Silent strengthening / weakening risk.**
If closure strength changes because (H) chooses one interpretation rather than another, then force has moved into the bridge.

**Mistranslation risk.**
Because (O) and (D) are not the same kind of thing, any nontrivial translation function must choose what to preserve, what to compress, and what to ignore. Those choices are semantically substantive.

**Authority displacement risk.**
If downstream closure depends on (z_t) rather than on the witnessed packet-pair and explicit membrane law, then the bridge becomes the effective adjudicator.

**Semantic sovereignty drift.**
If two bridge histories with the same admissible packet inputs can yield different closure outcomes, the bridge has become an implicit witness source.

Formally, a bridge layer is architecturally illegitimate whenever there exist packet histories (\mathcal H) and two bridge states (z \neq z') such that

[
\operatorname{Close}(\mathcal H, z) \neq \operatorname{Close}(\mathcal H, z').
]

Then closure depends on bridge memory, not just on lawful packet history and membrane doctrine.

The endogenous-coupling alternative avoids this because there is no extra state (Z). There is only:

* native lane state,
* lawful packetization,
* boundary-local reciprocal coupling,
* deterministic evaluation of coherence over explicit packet histories.

The bridge is then a **relation / manifold / invariant tube** in those histories, not a stateful semantic sovereign.

---

### 3. Core definitions

I will use a discrete-time kernel (t \in \mathbb N). A continuous-time lift is immediate by replacing updates with flows.

#### Definition 1. Lane

A lane (L \in {O,D}) is a native state space (X_L) with its own local update law (F_L). It is not globally exposed to other lanes.

For the two-lane kernel, write

[
X_O = O, \qquad X_D = D.
]

#### Definition 2. Pair-specific boundary band

For the pair (O \leftrightarrow D), define the (D)-facing band inside (O) and the (O)-facing band inside (D):

[
B_O^D,\qquad B_D^O.
]

These are not third layers. They are internal factors of the native lanes.

We decompose

[
O = O^\circ \times B_O^D,\qquad D = D^\circ \times B_D^O,
]

where (O^\circ) and (D^\circ) are lane interiors not directly exposed across the membrane.

Each boundary band itself has two components:

[
B_O^D = E_O^D \times I_O^D,\qquad B_D^O = E_D^O \times I_D^O.
]

Here:

* (E_O^D) is the **native exportable O-side band** relevant to D,
* (I_O^D) is the **imported D-image carried inside O**,
* (E_D^O) is the **native exportable D-side band** relevant to O,
* (I_D^O) is the **imported O-image carried inside D**.

That is the formal expression of the retained intuition: each lane contains an internal subset that carries a projected image of the other lane.

#### Definition 3. Boundary extractor

Let

[
\beta_O : O \to B_O^D,\qquad \beta_D : D \to B_D^O
]

be the boundary extractors. Write

[
\beta_O(o_t) = (\eta_t^O, \rho_t^{D\leadsto O}),\qquad
\beta_D(d_t) = (\eta_t^D, \rho_t^{O\leadsto D}),
]

where (\eta) is native exportable boundary state and (\rho) is imported-image state.

#### Definition 4. Projected boundary packet

A lawful export is not a raw state leak. It is a **typed packet**.

Define pair-specific packet spaces

[
P_{O\to D},\qquad P_{D\to O}.
]

A packet has the form

[
p_{O\to D} = (\mathrm{ty},\sigma, W_O^{\mathrm{nat}}, L_{D\leadsto O}^{\mathrm{imp}}, \lambda_O),
]

and similarly for (p_{D\to O}), where:

* (\mathrm{ty}) is the packet type,
* (\sigma) is the exported payload,
* (W_O^{\mathrm{nat}}) is the native witness basis from (O),
* (L_{D\leadsto O}^{\mathrm{imp}}) is imported advisory lineage already present in O,
* (\lambda_O) is the O-side authority / force ceiling carried by the packet.

The crucial discipline is:

* native witness basis may support force,
* imported lineage may inform relevance,
* imported lineage may **not** silently become native witness.

#### Definition 5. Membrane law

The pairwise membrane law is a static contract

[
\mathsf M_{OD} =
(\mathcal E,\mathcal T,\mathcal A,\mathcal K,\Sigma,\Theta),
]

where:

* (\mathcal E) is the exposure policy,
* (\mathcal T) is the admissible packet type family,
* (\mathcal A) is the family of partial acceptance/adaptation maps,
* (\mathcal K) is the family of admissible coupling operators,
* (\Sigma) is the declared coherence-predicate signature,
* (\Theta) is the action-class closure threshold family.

This is the membrane in the strong sense: not a mediator object, but the law governing lawful reciprocal projection and coupling.

#### Definition 6. Coherence relation

Let (\Sigma = {\psi_k}_{k\in K}) be typed coherence predicates

[
\psi_k : P_{O\to D} \times P_{D\to O} \to {\top,\bot,?}.
]

These compare only declared, exportable fields. They are not latent translation embeddings and not a new ontology.

Define coherence error

[
\chi_{OD}(p_O,p_D) = \sum_{k\in K} w_k,\ell(\psi_k(p_O,p_D)),
]

with (\ell(\top)=0), (\ell(\bot)=1), and (\ell(?)=\gamma_k), where (\gamma_k \ge 1) and may be blocking for high-impact unknowns.

#### Definition 7. Induced bridge regime

For a tolerance (\varepsilon), define the instantaneous coherent set

[
\mathcal C_{OD}^{\varepsilon}
=============================

{(p_O,p_D) \in P_{O\to D}\times P_{D\to O}
;:;
\chi_{OD}(p_O,p_D)\le \varepsilon
\text{ and all blocking predicates pass}}.
]

The **induced bridge regime** is not a new state space. It is the subset of lane states whose exported boundary packets lie in that coherent set:

[
\mathfrak B_{OD}^{\varepsilon}
==============================

{(o,d)\in O\times D
;:;
(\pi_{O\to D}(o),\pi_{D\to O}(d)) \in \mathcal C_{OD}^{\varepsilon}}.
]

More generally, for oscillatory or phase-locked cases, the bridge regime is a lawful set of packet histories rather than a static set of packet pairs.

#### Definition 8. Closure requirement profile

Each downstream act (a) carries a requirement profile

[
R(a) = (G(a),\Omega(a),r_O(a),r_D(a)),
]

where:

* (G(a)) is the set of acceptable alignment regimes for (a),
* (\Omega(a)) is the witness-completeness requirement,
* (r_O(a)) is required O-side force/grounding level,
* (r_D(a)) is required D-side force/admissibility level.

This makes closure action-class-sensitive rather than absolute.

---

### 4. Two-lane formal model: the O/D kernel

#### 4.1 Boundary factorization

Every lawful O-to-D influence must factor as

[
O
\xrightarrow{\beta_O}
B_O^D
\xrightarrow{\mathrm{mask}*{O\to D}}
\widetilde B_O^D
\xrightarrow{\mathrm{pack}*{O\to D}}
P_{O\to D}^{\mathrm{adm}}
\xrightarrow{\alpha_{D\leftarrow O}}
I_D^O
\xrightarrow{\kappa_{O\to D}}
B_D^O,
]

and every lawful D-to-O influence must factor as

[
D
\xrightarrow{\beta_D}
B_D^O
\xrightarrow{\mathrm{mask}*{D\to O}}
\widetilde B_D^O
\xrightarrow{\mathrm{pack}*{D\to O}}
P_{D\to O}^{\mathrm{adm}}
\xrightarrow{\alpha_{O\leftarrow D}}
I_O^D
\xrightarrow{\kappa_{D\to O}}
B_O^D.
]

No direct morphism (O \to D^\circ) or (D \to O^\circ) is lawful.

That factorization is the formal core of the architecture.

#### 4.2 Projection operators

Define

[
\pi_{O\to D}
============

\mathrm{pack}*{O\to D}\circ \mathrm{mask}*{O\to D}\circ \beta_O,
\qquad
\pi_{D\to O}
============

\mathrm{pack}*{D\to O}\circ \mathrm{mask}*{D\to O}\circ \beta_D.
]

These are intentionally many-to-one and bounded. In general,

[
\pi_{O\to D} \neq \mathrm{id}*O,\qquad \pi*{D\to O} \neq \mathrm{id}_D.
]

So full lanes are not fully exposed.

#### 4.3 Membrane admissibility judgment

Write

[
\mathsf M_{OD}\vdash p_{O\to D};\mathrm{adm}
]

iff all of the following hold:

1. payload fields lie within the exposure mask (\mathcal E_{O\to D}),
2. packet type is in (\mathcal T_{O\to D}),
3. the packet’s force ceiling satisfies
   [
   \lambda_O \preceq_O \mathrm{ceil}_O(W_O^{\mathrm{nat}}),
   ]
4. imported lineage remains tagged as advisory lineage and is not reclassified as native witness,
5. no high-impact ambiguity remains unresolved on blocking predicates.

Similarly for (D\to O).

#### 4.4 Partial acceptance/adaptation maps

The receiver does not receive the other lane as such. It receives only an admitted image.

Define partial maps

[
\alpha_{D\leftarrow O}:P_{O\to D}^{\mathrm{adm}} \rightharpoonup I_D^O,\qquad
\alpha_{O\leftarrow D}:P_{D\to O}^{\mathrm{adm}} \rightharpoonup I_O^D.
]

Undefined means fail-closed import.

#### 4.5 Native update laws

Write full states as

[
o_t=(o_t^\circ,\eta_t^O,\rho_t^{D\leadsto O}),
\qquad
d_t=(d_t^\circ,\eta_t^D,\rho_t^{O\leadsto D}).
]

Then the native lane updates are

[
o_{t+1}^\circ
=============

f_O(o_t^\circ,\eta_t^O,\rho_t^{D\leadsto O},u_t^O),
]

[
(\eta_{t+1}^O,\rho_{t+1}^{D\leadsto O})
=======================================

g_O!\left(
o_t^\circ,\eta_t^O,\rho_t^{D\leadsto O},
\alpha_{O\leftarrow D}(p_{D\to O,t}),
u_t^O
\right),
]

[
d_{t+1}^\circ
=============

f_D(d_t^\circ,\eta_t^D,\rho_t^{O\leadsto D},u_t^D),
]

[
(\eta_{t+1}^D,\rho_{t+1}^{O\leadsto D})
=======================================

g_D!\left(
d_t^\circ,\eta_t^D,\rho_t^{O\leadsto D},
\alpha_{D\leftarrow O}(p_{O\to D,t}),
u_t^D
\right).
]

The cross-lane import appears directly only inside the boundary update (g_O, g_D), not as raw state injection into the opposite interior.

A useful locality condition is:

[
\frac{\partial o_{t+1}^\circ}{\partial p_{D\to O,t}} = 0,\qquad
\frac{\partial d_{t+1}^\circ}{\partial p_{O\to D,t}} = 0.
]

Interiors may still change indirectly through their own boundary bands, but not by foreign direct write.

#### 4.6 Export recursion

Exports are then

[
p_{O\to D,t} = \pi_{O\to D}(o_t),
\qquad
p_{D\to O,t} = \pi_{D\to O}(d_t).
]

Because (\eta_t^O,\eta_t^D) are themselves shaped by prior imports, each lane’s current export already contains a lane-native response to the other lane’s earlier projected image. That is endogenous reciprocal coupling.

#### 4.7 Synchronization condition

The minimal synchronization condition is not (o_t=d_t). That is meaningless.

It is instead

[
\chi_{OD}(p_{O\to D,t},p_{D\to O,t}) \le \varepsilon,
]

with the relevant (\varepsilon) chosen by action class and policy.

For strict coherence, (\varepsilon=0).

For bounded coherence, (\varepsilon>0) but finite and declared.

#### 4.8 Dynamic regime classification

Because some lawful alignments are oscillatory or phase-locked, the authoritative classifier should inspect explicit packet history

[
\mathcal H_t =
\big((p_{O\to D,\tau},p_{D\to O,\tau})\big)_{\tau=t-h}^t
]

and compute a regime class

[
\rho_t = \mathcal J_{OD}(\mathcal H_t),
]

where (\mathcal J_{OD}) is deterministic and policy-pinned.

This is consistent with “deterministic adjudicator authoritative” while avoiding any third semantic lane, because (\mathcal J_{OD}) evaluates only explicit packet history against declared predicates and thresholds.

#### 4.9 Local stability of the boundary regime

Choose coherence observables on the packet surface and let (e_t) be the transverse mismatch vector. Around a candidate coherent operating point,

[
e_{t+1} \approx J_\perp e_t.
]

Then:

* if (\rho(J_\perp)<1), coherence is locally attracting,
* if (\rho(J_\perp)=1), neutral / phase-locked behavior is possible,
* if (\rho(J_\perp)>1), the boundary regime is unstable.

Again: the object of stability analysis is the **coupled boundary subsystem**, not a bridge layer.

---

### 5. The membrane law as reciprocal projection governor

A doctrine-grade statement can be given as follows.

## Pairwise membrane law (OD form)

For (O) and (D), a cross-lane effect is lawful iff it satisfies all six clauses below.

**Clause 1. Exposure law.**
Only the membrane-designated boundary coordinates may be exported. No full-lane exposure is permitted.

**Clause 2. Projection law.**
Every export must be a typed, witnessed, force-ceiled packet. Projections may express, but may not mint authority.

**Clause 3. Acceptance law.**
A receiving lane may import only the admitted image of the other lane’s packet, never the other lane’s full state, and never a silently strengthened reinterpretation.

**Clause 4. Coupling law.**
Imported images may drive only the receiving lane’s boundary band directly. Any deeper effect must arise through that lane’s own native dynamics.

**Clause 5. Coherence law.**
Alignment is judged only on declared membrane predicates over packet pairs or packet histories; it is not judged by full-lane identity or hidden mediator state.

**Clause 6. Closure law.**
Downstream closure is permitted only when the authoritative regime classifier reports an action-adequate coherence regime and the resulting act does not exceed the componentwise witness ceilings carried by the coupled packets. High-impact unresolved ambiguity fails closed.

This is the membrane reformulated in the stronger way you requested:

* law of admissible reciprocal projection,
* law of lawful cross-lane exposure,
* governor of synchronization among lane-internal boundary images,
* regulator of when coupled coherence is strong enough for downstream closure.

---

### 6. Alignment regimes

Alignment is not one thing.

Let (\rho_t = \mathcal J_{OD}(\mathcal H_t)). Then at minimum the model should recognize the following.

#### 6.1 Strict fixed-point coherence

There exists a packet pair ((p_O^*,p_D^*)) such that for all sufficiently large (t),

[
p_{O\to D,t}=p_O^*,\qquad p_{D\to O,t}=p_D^*,\qquad \chi_{OD}(p_O^*,p_D^*)=0.
]

This is the cleanest membrane-level alignment. It is the right threshold for strong irreversible closure.

#### 6.2 Bounded synchronization

There exists (\varepsilon>0) such that

[
\limsup_{t\to\infty}\chi_{OD}(p_{O\to D,t},p_{D\to O,t}) \le \varepsilon,
]

with all blocking predicates still satisfied.

Packets need not be identical or constant. They remain inside a lawful coherence tube.

This is acceptable for many scoped actions.

#### 6.3 Phase-locked but non-identical evolution

Choose boundary observables with phases (\vartheta_O(t)) and (\vartheta_D(t)). There exist integers (m,n) and phase offset (\phi_0) such that for all large (t),

[
|m\vartheta_O(t)-n\vartheta_D(t)-\phi_0| \le \varepsilon_\phi,
]

while (\chi_{OD}) remains inside an admissible bound.

The lanes move differently, but their relevant boundary observables remain rhythmically coupled.

This may be acceptable for iterative, non-final coordination, but usually not for high-force closure unless explicitly declared.

#### 6.4 Admissible oscillatory coupling

The packet pair does not converge, but remains inside a declared invariant tube:

[
\chi_{OD}(t)\in[\varepsilon_{\min},\varepsilon_{\max}],
]

with no illicit force amplification and with explicit hold/defer posture on unresolved high-impact fields.

This is not “fully aligned,” but it can be lawful enough for weaker downstream acts such as:

* hold,
* defer,
* request more witness,
* stage local preparation,
* narrow scope.

#### 6.5 Persistent incoherence / membrane failure

If

[
\liminf_{t\to\infty}\chi_{OD}(t) > \varepsilon_{\mathrm{block}},
]

or blocking predicates remain unknown/contradictory beyond policy bounds, then the membrane posture is blocked.

This is not merely low-quality coupling. It is failure of admissible cross-lane synchronization.

#### 6.6 Illicit laundering

This is not just another regime. It is architectural invalidity.

If imported packets or coupling produce closure strength beyond native witness ceilings, or imported advisory lineage is reclassified as native authority, then the posture is laundering even if (\chi_{OD}) is small.

So a low mismatch score does **not** rescue an illicit architecture.

#### Regime classification

A good ADEU-native posture map is:

* **acceptable membrane-level alignment:** strict fixed-point, bounded synchronization, and some explicitly authorized phase-locked cases,
* **unstable but non-terminal:** admissible oscillatory coupling, transient under-projection, lawful insufficiency awaiting more witness,
* **blocking failure:** persistent incoherence, blocking unknowns, pseudo-alignment for the target action class,
* **illicit laundering:** force amplification, hidden mediator sovereignty, or capture.

---

### 7. Witness discipline and force constraints

This architecture is only ADEU-compatible if witness discipline is threaded through the model, not bolted on afterward.

#### 7.1 Native witness ceilings

Each lane has a native witness ceiling function:

[
\mathrm{ceil}_O : \mathcal W_O \to \Lambda_O,
\qquad
\mathrm{ceil}_D : \mathcal W_D \to \Lambda_D,
]

where (\Lambda_O,\Lambda_D) are lane-specific force/grounding posets.

Every packet must satisfy

[
\lambda_O \preceq_O \mathrm{ceil}_O(W_O^{\mathrm{nat}}),
\qquad
\lambda_D \preceq_D \mathrm{ceil}_D(W_D^{\mathrm{nat}}).
]

That is the no-stronger-than-witness rule at packet level.

#### 7.2 Imported images are weaker than or equal to their witness basis

The imported image

[
\alpha_{D\leftarrow O}(p_{O\to D})
]

must carry its native witness refs and authority ceiling with it. It may narrow, select, parameterize, or trigger existing local gates. It may not exceed the ceiling of the packet from which it came, and it may not be silently rewritten as locally native support.

Same for (\alpha_{O\leftarrow D}(p_{D\to O})).

#### 7.3 No silent deontic strengthening by ontic projection

Ontic projection may help determine whether an already-native D-side gate applies. It may not mint a new deontic force class.

Formally, let (A_D^{\max}(d_t^\circ)) be the D-side admissibility envelope licensed by D’s own native witness base. Then O-import may only select within it:

[
A_D(d_t, \alpha_{D\leftarrow O}(p_{O\to D,t}))
\subseteq
A_D^{\max}(d_t^\circ).
]

So O can ground applicability. It cannot create deontic authority ex nihilo.

#### 7.4 No silent ontic reification by deontic expectation

Similarly, D-import may shape what O must resolve, what distinctions matter, or what uncertainty blocks closure. It may not turn expectation into fact.

Let (G_O^{\max}(o_t^\circ)) be the O-side grounded proposition envelope licensed by O’s own native witness base. Then D-import may only focus or constrain within it:

[
G_O(o_t,\alpha_{O\leftarrow D}(p_{D\to O,t}))
\subseteq
G_O^{\max}(o_t^\circ).
]

So D can exert admissibility pressure on O-side interpretation. It cannot create world-facts.

#### 7.5 Action-class closure

At time (t), define the packet ceilings

[
\Lambda_t = (\lambda_{O,t},\lambda_{D,t}).
]

A downstream act (a) is membrane-authorized only if:

[
\rho_t \in G(a),
\qquad
\Omega(a)(\mathcal H_t)=\top,
\qquad
r_O(a)\preceq_O \lambda_{O,t},
\qquad
r_D(a)\preceq_D \lambda_{D,t}.
]

If those conditions fail, the system must either block or **descend lawfully** to a weaker act (a' \prec a) whose requirements are satisfied.

That is lawful descent / bounded exposure logic in dynamic form.

#### 7.6 Boundary sufficiency is claim-class specific

A projection pair may be sufficient for one class of action and insufficient for another.

Define ((\pi_{O\to D},\pi_{D\to O})) to be **(a)-separating** iff

[
\pi_{O\to D}(o)=\pi_{O\to D}(o'),
\quad
\pi_{D\to O}(d)=\pi_{D\to O}(d')
;\Longrightarrow;
\operatorname{Close}^a(o,d)=\operatorname{Close}^a(o',d').
]

If (a)-separation fails, then boundary coherence is insufficient to justify action (a), even if the packet pair looks aligned.

This is the formal guard against downstream overcommitment from boundary-only coherence.

---

### 8. O versus D asymmetry

The architecture should be treated as **structurally symmetric but semantically asymmetric**.

Structurally symmetric means:

* both lanes have pair-specific boundary bands,
* both export typed boundary packets,
* both receive imported images,
* both participate in reciprocal synchronization.

Semantically asymmetric means:

* (O) and (D) do not carry the same kind of content,
* (\pi_{O\to D}) and (\pi_{D\to O}) do very different work,
* (\kappa_{O\to D}) and (\kappa_{D\to O}) have different lawful effects.

In the O/D case:

**O generally furnishes grounding conditions for D.**
O-side packets export world conditions, boundary facts, scope matches, uncertainty markers, and other applicability-relevant material.

**D generally furnishes admissibility pressure on O.**
D-side packets export constraints, required distinctions, fail-closed gates, escalation triggers, and scope-narrowing conditions that tell O what must be known before closure is lawful.

So the reciprocal schema is not equivalence. It is **non-equivalent reciprocity**.

A good shorthand is:

[
O \to D: \text{grounding of applicability},
\qquad
D \to O: \text{pressure on interpretation and closure readiness}.
]

That preserves the user’s retained intuition without collapsing the lanes.

---

### 9. Failure taxonomy and anti-patterns

#### 9.1 Full-lane overexposure

**Symptom.**
A projection leaks interior coordinates not covered by the declared exposure mask, or a foreign packet directly drives interior state.

**Formal sign.**
Either (\pi_{i\to j}) exports protected/non-boundary fields, or

[
\frac{\partial x_{i,t+1}^\circ}{\partial p_{j\to i,t}} \neq 0.
]

**Meaning.**
The membrane has been bypassed. This is lane collapse, not alignment.

---

#### 9.2 Under-projection that prevents coupling

**Symptom.**
A packet omits boundary variables necessary for declared coherence predicates or for a target action class.

**Formal sign.**
For some required predicate (\psi_k), evaluation is persistently (?) even though relevant native witness exists in the sending lane.

**Meaning.**
The export mask is too narrow for the declared use. This may be lawful insufficiency or a projection design bug.

---

#### 9.3 Illicit force amplification

**Symptom.**
The imported image or the coupled regime licenses stronger closure than the native witness ceiling allows.

**Formal sign.**

[
r_D(a)\npreceq_D \mathrm{ceil}_D(W_D^{\mathrm{nat}})
\quad\text{or}\quad
r_O(a)\npreceq_O \mathrm{ceil}_O(W_O^{\mathrm{nat}}).
]

**Meaning.**
This is not mere drift. It is laundering.

---

#### 9.4 False synchronization due to lossy projection

**Symptom.**
Boundary packets match, but the projection has erased distinctions that matter for the target claim.

**Formal sign.**
There exist (o,o',d) such that

[
\pi_{O\to D}(o)=\pi_{O\to D}(o'),
\qquad
\chi_{OD}(\pi_{O\to D}(o),\pi_{D\to O}(d))
==========================================

\chi_{OD}(\pi_{O\to D}(o'),\pi_{D\to O}(d)),
]

yet

[
\operatorname{Close}^a(o,d)\neq \operatorname{Close}^a(o',d).
]

**Meaning.**
The packet surface is too lossy for action (a). Alignment is only apparent.

---

#### 9.5 Pseudo-alignment: boundary images match, interiors do not

**Symptom.**
The packet pair lies in (\mathcal C_{OD}^\varepsilon), but the underlying interiors cannot jointly satisfy the relevant invariants.

**Meaning.**
The boundary regime is coherent but not reintegrable. This is a reintegration failure, not true alignment.

---

#### 9.6 Membrane capture by one lane

**Symptom.**
One lane’s boundary band becomes a surrogate for the other lane rather than remaining lane-native.

**Formal sign.**
Sensitivity of a receiving boundary band to imported image dominates sensitivity to native state:

[
\left|
\frac{\partial g_D}{\partial \alpha_{D\leftarrow O}}
\right|
\gg
\left|
\frac{\partial g_D}{\partial (d^\circ,\eta^D)}
\right|,
]

or symmetrically for (O).

**Meaning.**
Reciprocal coupling has degenerated into lane domination.

---

#### 9.7 Unstable oscillation mistaken for lawful coupling

**Symptom.**
There is visible alternation, but it is not bounded, policy-pinned, or action-adequate.

**Formal sign.**
Oscillation amplitude grows, high-impact unknown dwell time is unbounded, or (\rho(J_\perp)>1).

**Meaning.**
This is not admissible oscillatory coherence. It is instability.

---

#### 9.8 Downstream overcommitment from boundary-only coherence

**Symptom.**
An action is authorized even though it depends on variables not preserved by the boundary packets.

**Formal sign.**
The target action class is not (a)-separating under the active projection family.

**Meaning.**
Invalid early closure.

---

#### 9.9 Hidden bridge surrogate

**Symptom.**
A latent similarity score, risk score, or mediator state resolves O/D mismatch and then drives closure.

**Meaning.**
That is a bridge layer in disguise. If it is indispensable, it is semantically sovereign; if not indispensable, remove it.

---

### 10. Generalization beyond the two-lane case

The principle generalizes cleanly if kept pairwise and task-scoped.

Let the lane set be

[
L={O,E,D,U}.
]

For each active pair ((i,j)), define:

* boundary bands (B_i^j, B_j^i),
* packet spaces (P_{i\to j},P_{j\to i}),
* pairwise membrane law (\mathsf M_{ij}),
* pairwise regime classifier (\mathcal J_{ij}).

For a task-scoped coupling graph (G_q=(L,E_q)), each lane decomposes as

[
X_i = X_i^\circ \times \prod_{j\in N_q(i)} B_i^j.
]

No full clique is required. Only declared task-relevant edges are active.

The overall coupled system is then a graph of pairwise membrane laws, not a global fusion layer.

#### 10.1 (O \leftrightarrow E)

* O exports entities, boundaries, states, object structure.
* E exports evidence sufficiency, unknown status, observability constraints.
* O cannot self-certify evidence.
* E cannot mint ontology.

This is synchronization of what exists with what is evidentially licensed.

#### 10.2 (O \leftrightarrow D)

This is the kernel already formalized:

* O grounds applicability,
* D constrains closure and required distinctions.

#### 10.3 (E \leftrightarrow D)

* E exports confidence, unknowns, contradiction structure, evidence sufficiency.
* D exports fail-closed thresholds, required evidence classes, escalation triggers.

This is synchronization of evidential state with deontic gating.

#### 10.4 (D \leftrightarrow U)

* D exports permissions, prohibitions, obligations, invariant boundaries.
* U exports pressure, cost, urgency, tradeoff tension.

Reciprocal coupling is allowed, but utility may only optimize **inside** deontic envelope, and deontic force may not pretend utility facts it does not have.

#### 10.5 Full ODEU

A full ODEU system should therefore be modeled as a task-scoped membrane graph of pairwise boundary synchronizations, with closure requiring the relevant subgraph to be in action-adequate lawful regimes.

What it should **not** do is invent a global bridge ontology that “unifies” O/E/D/U.

---

### 11. Worked examples

### Example A. Clean O/D coupling in a governed taskpack-execution lane

Let the downstream act be (a_{\mathrm{run}}): execute the exact compiled taskpack.

#### O-side native state

The O lane contains verified facts about the artifact and its boundary conditions:

* signature verification result,
* trust-anchor identity match,
* expiry/revocation freshness,
* scope hash match,
* requested capability subset.

Its O-to-D packet is

[
p_{O\to D}
==========

(\mathrm{exec_fact_packet},
\sigma_O,
W_O^{\mathrm{nat}},
L^{\mathrm{imp}},
\lambda_O),
]

with

[
\sigma_O =
{
\texttt{sig_valid}=1,
\texttt{anchor_match}=1,
\texttt{expiry_ok}=1,
\texttt{scope_match}=1,
\texttt{cap_subset}=1
}.
]

The native witness basis includes the signature verification result, the pinned trust-anchor registry snapshot, and the compiled scope binding.

#### D-side native state

The D lane contains native rule witness:

* execution is permitted only if signature is valid,
* trust anchor matches,
* expiry/revocation check is fresh,
* scope hash matches,
* requested capability is inside declared allowlist,
* unknown on any high-impact item fails closed.

Its D-to-O packet is

[
p_{D\to O}
==========

(\mathrm{exec_gate_packet},
\sigma_D,
W_D^{\mathrm{nat}},
L^{\mathrm{imp}},
\lambda_D),
]

with payload equivalent to:

* these are the required gate conditions,
* fail closed on freshness unknown,
* allowed closure class is exact execution only.

#### Coupling

O-to-D import does not mint permission. It supplies the grounding that D’s already-native gate requires.
D-to-O import does not create facts. It tells O which fact distinctions are closure-relevant and which unknowns block execution.

The coherence predicates are:

* (\psi_1): signature valid,
* (\psi_2): anchor match,
* (\psi_3): freshness present,
* (\psi_4): scope match,
* (\psi_5): capability subset.

All are satisfied, so

[
\chi_{OD}(p_{O\to D},p_{D\to O}) = 0.
]

The regime is strict fixed-point or at least bounded synchronization with zero mismatch.

#### Closure

Because

[
\rho_t \in G(a_{\mathrm{run}})
]

and the O-side and D-side witness ceilings both support the act, the membrane may authorize exact taskpack execution.

This is genuine endogenous alignment:

* no bridge layer,
* no laundering,
* no collapse of O into D,
* no collapse of D into O.

The bridge is simply the coherent packet-pair regime.

---

### Example B. False bridge / laundering case

Now suppose someone inserts a mediator state

[
z_t = H(
\texttt{sig_valid},
\texttt{history_success_rate},
\texttt{deadline_pressure},
\texttt{operator_confidence}
)
]

and declares:

* if (z_t > 0.8), execution is authorized.

This is invalid.

Why?

Because (\texttt{deadline_pressure}) is utility pressure, not deontic witness.
Because (\texttt{history_success_rate}) is empirical convenience, not current authority basis.
Because (\texttt{operator_confidence}) is advisory unless explicitly pinned as witness.
And because the bridge score is now settling closure.

If revocation freshness is unknown but the score is still (0.84), then the mediator has silently converted mixed pressure into permission.

Formally, the run act requires a D-side force class (r_D(a_{\mathrm{run}})), but there is no native D witness basis for the score rule. So

[
r_D(a_{\mathrm{run}})
\npreceq_D
\mathrm{ceil}_D(W_D^{\mathrm{nat}}).
]

This is not “creative synchronization.” It is illicit force amplification through an implicit bridge layer.

Even worse, if (z_t) is stateful across runs, then past mediator history can affect present closure with no explicit packet witness. That is semantic sovereignty drift.

---

### Example C. Partial / oscillatory coupling with lawful narrow closure

Again let the context be execution governance, but now revocation freshness is intermittently available.

At even (t):

[
\sigma_O^{(t)}
==============

{
\texttt{sig_valid}=1,
\texttt{anchor_match}=1,
\texttt{expiry_ok}=1,
\texttt{revocation_fresh}=1,
\texttt{scope_match}=1
}.
]

At odd (t):

[
\sigma_O^{(t+1)}
================

{
\texttt{sig_valid}=1,
\texttt{anchor_match}=1,
\texttt{expiry_ok}=1,
\texttt{revocation_fresh}= ?,
\texttt{scope_match}=1
}.
]

The D lane remains stable:

* execute only if revocation freshness is present and valid,
* otherwise hold, refresh witness, and do not execute.

The packet history exhibits a 1:1 phase-lock between freshness availability and D-side hold/permit boundary posture.

This is not strict fixed-point coherence. But suppose the oscillation is bounded and explicit:

[
\chi_{OD}(t)\in{0,\gamma_{\mathrm{fresh}}},
\qquad
\gamma_{\mathrm{fresh}} \le \varepsilon_{\mathrm{stage}}
< \varepsilon_{\mathrm{run}}^{\mathrm{forbidden}}.
]

Then two action classes behave differently.

For (a_{\mathrm{run}}), the requirement profile says:

* regime must be fixed-point or bounded sync without blocking unknown,
* freshness unknown is disallowed.

So (a_{\mathrm{run}}) is blocked.

For a weaker act (a_{\mathrm{stage}}), the requirement profile says:

* admissible oscillatory regime is acceptable,
* act is local-only,
* no irreversible execution occurs,
* explicit refresh request is emitted.

So (a_{\mathrm{stage}}) is authorized.

This is exactly the case you asked for: the system does not reach full agreement, but reaches bounded lawful coherence sufficient for some downstream action and insufficient for stronger claims.

---

### 12. Compact theorem-like statements

#### Proposition 1. Boundary-local factorization preserves lane sovereignty

If all lawful cross-lane effects factor through the boundary pipeline

[
X_j \to B_j^i \to P_{j\to i}^{\mathrm{adm}} \to I_i^j \to B_i^j,
]

then no foreign lane can directly write the receiver’s interior state.

**Reason.**
Direct cross-lane dependence is confined to the receiving boundary update. Interior effects can arise only through the receiver’s own native dynamics.

---

#### Proposition 2. Endogenous bridge sufficiency

If the coupled boundary subsystem is locally contractive on the transverse coherence error, i.e.

[
e_{t+1}\approx J_\perp e_t
\quad\text{with}\quad
\rho(J_\perp)<1,
]

then there exists a locally attracting coherent regime (\mathfrak B_{OD}) without any bridge layer.

**Reason.**
Synchronization is then a property of the coupled native boundary dynamics themselves.

---

#### Proposition 3. Non-amplification of authority

If packets are force-ceiled by native witness bases and closure is componentwise bounded by packet ceilings, then no downstream act can be stronger than the witness basis lawfully carried by the coupled packet pair.

**Reason.**
Closure is monotone under the ceiling constraints; imported advisory lineage cannot increase the ceiling.

---

#### Proposition 4. Bridge-layer redundancy or danger

If an explicit bridge state (Z) is fully reducible to deterministic evaluation of explicit packet histories, then it is redundant.
If it is not reducible, then it carries extra semantic authority and is dangerous.

**Reason.**
Those are the only two cases.

---

#### Proposition 5. Boundary coherence is not enough unless projections are action-separating

If the active projection family is not (a)-separating for action (a), then packet-level alignment cannot justify (a).

**Reason.**
Equal packet pairs can then mask distinct full-lane states that warrant different closures.

---

### 13. Repo-native / doctrine-native implications

This formalization fits the existing ADEU discipline cleanly.

It reinforces, rather than weakens, the doctrines already latent in the repo:

* projections may express but may not mint authority,
* deterministic adjudicator authoritative,
* oracle output advisory only,
* fail closed on high-impact ambiguity,
* lane-preserving decomposition,
* local-only repair rather than non-local semantic flattening.

What should be added is **not** a new bridge axis. It is a pairwise boundary-synchronization contract layered onto existing boundary-policy and alignment-report surfaces.

A natural implementation shape would be:

1. a pairwise membrane contract artifact for each active lane-pair,
2. explicit export masks and packet types,
3. declared coherence predicates,
4. regime classifier thresholds by action class,
5. laundering detectors and capture detectors,
6. a boundary-sync trace/report artifact over explicit packet histories.

In an ASIR-like pseudo-surface, the shape would look more like this than like a mediator layer:

```text
OD_BOUNDARY_SYNC taskpack_exec_v1 {
  O_FACE D {
    export_refs = [sig_valid, anchor_match, expiry_ok, revocation_fresh, scope_match, cap_subset]
  }

  D_FACE O {
    export_refs = [gate_execute, fail_closed_conditions, allowed_action_classes, required_witness_classes]
  }

  COHERENCE {
    predicate p1 = sig_valid == true
    predicate p2 = anchor_match == true
    predicate p3 = expiry_ok == true
    predicate p4 = revocation_fresh != unknown
    predicate p5 = scope_match == true
    predicate p6 = cap_subset == true
  }

  CLOSURE run_exact {
    acceptable_regimes = [strict_fixed_point, bounded_sync]
  }

  CLOSURE stage_local_refresh {
    acceptable_regimes = [admissible_oscillatory]
  }
}
```

That keeps the architecture lane-preserving and membrane-native.

The bridge remains endogenous.

---

## Closing claim

The strongest formulation is this:

Cross-lane alignment in ODEU does **not** require a third bridge layer.
It can be formalized as a **membrane-governed reciprocal synchronization of membrane-facing boundary subdynamics** within the native lanes themselves.

In the two-lane O/D kernel:

* full ontic and full deontic dynamics remain distinct,
* each lane exposes only a lawful boundary band,
* each boundary band carries a projected image of the other lane,
* cross-lane influence occurs only through typed, witnessed, non-authority-minting packets,
* the membrane governs exposure, projection, admissible coupling, and closure thresholds,
* and the resulting “bridge” is just the induced coherence regime of the coupled boundary subsystem.

So downstream closure may rely on the lawful state of that coupled boundary regime without pretending that full-lane identity, full semantic unification, or a sovereign mediator layer ever existed.
