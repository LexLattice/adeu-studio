## 1. Executive thesis

The retained architecture stands, but its seams must be tightened in four places.

First, the membrane-facing “boundary band” must be treated as a **contract-governed interface description**, not silently upgraded into a universal ontological factor of the lane. Product notation remains useful, but only as a local chart or contract-local factorization.

Second, cross-lane coherence must no longer be read from a compensatory scalar. The primary object is a **typed, non-compensatory coherence profile** over **admitted packet histories**. Some failures are terminal. Some unknowns are blocking. Force-ceiling violations are never tradable.

Third, the regime classifier must be pinned down as **adjudicative only**. It classifies explicit admitted histories against declared predicates and declared policy. It has no latent semantic state, no hidden memory beyond explicit history inputs, no authority of its own, and no right to behave differently on identical admitted histories under identical policy.

Fourth, membrane-level boundary coherence is not operational closure. Closure requires an explicit **reintegration law**: the target action must be lawfully reintegrable into full-lane execution without depending on masked or underdetermined interior degrees of freedom.

The result is the stronger doctrine-ready claim:

* the bridge is endogenous, not sovereign;
* only **lawfully admitted** membrane-facing boundary images participate in coupling;
* coherence is typed and non-compensatory;
* the classifier is a replayable adjudicator, not a hidden bridge;
* imported images remain provenance-tagged, weaker-than-native, and non-self-authenticating;
* pairwise contracts are the default, but higher-arity contracts are reserved for actions whose adequacy is not reducible to pairwise coherence.

---

## 2. What is retained from the current architecture

Retained without alteration in principle are:

* rejection of a third sovereign bridge layer,
* the central distinction among full lane dynamics, membrane-facing boundary subdynamics, and induced bridge regime,
* the two-lane (O/D) kernel,
* typed projected packets,
* the membrane as law of admissible reciprocal projection and coupling,
* action-class-sensitive closure,
* witness ceilings and no-stronger-than-witness discipline,
* structural symmetry with semantic asymmetry in (O \leftrightarrow D),
* the failure taxonomy direction,
* proposition-style doctrinal summary.

This pass does not replace that architecture. It tightens its formal status conditions.

---

## 3. Precise status of boundary bands: interface versus ontology

The strongest hardening needed is this:

> A boundary band is first and foremost a membrane-lawful interface object.
> It is not, by default, a global ontological component of the lane.

Let the native lane state spaces be (O) and (D). For the pairwise contract (O \leftrightarrow D), introduce contract-local domains

[
U_O^D \subseteq O,\qquad U_D^O \subseteq D,
]

and interface maps

[
\beta_O^D : U_O^D \to B_O^D,\qquad
\beta_D^O : U_D^O \to B_D^O.
]

Here (B_O^D) and (B_D^O) are **boundary interface objects** selected by the membrane contract. Depending on implementation, such an object may be realized as:

* a lawful observable interface,
* a boundary subobject,
* a quotient by an exposure relation,
* a contract-induced local factor,
* or a local interface chart.

The doctrine does **not** require that (O) or (D) globally decompose as Cartesian products.

When convenient, one may choose contract-local trivializations

[
\varphi_O^D : V_O^D \overset{\sim}{\longrightarrow} O^{\circ,D} \times B_O^D,
\qquad
\varphi_D^O : V_D^O \overset{\sim}{\longrightarrow} D^{\circ,O} \times B_D^O,
]

for suitable (V_O^D \subseteq U_O^D), (V_D^O \subseteq U_D^O).

Then notation such as

[
O \cong O^{\circ,D}\times B_O^D,\qquad
D \cong D^{\circ,O}\times B_D^O
]

must be read as **chart-local shorthand**, not as universal ontology unless independently proved.

This distinction is doctrinally decisive:

* claims about (O) and (D) as lanes are ontological claims,
* claims about (B_O^D), (B_D^O), masking, packetization, and coupling are interface-law claims.

The membrane governs the second class, not the first.

---

## 4. Revised two-lane formal kernel

Work in discrete time (t \in \mathbb N). The continuous-time analogue is straightforward.

### 4.1 Contract-local boundary coordinates

Within a chosen contract-local chart, write

[
\varphi_O^D(o_t)=(o_t^{\circ,D}, b_{O,t}^D),\qquad
\varphi_D^O(d_t)=(d_t^{\circ,O}, b_{D,t}^O).
]

Within a chosen interface chart on the boundary objects, write

[
\varsigma_O^D(b_{O,t}^D)=(\eta_{O,t}^D,\rho_{O,t}^D),\qquad
\varsigma_D^O(b_{D,t}^O)=(\eta_{D,t}^O,\rho_{D,t}^O).
]

Interpretation:

* (\eta_{O,t}^D) is the **O-side native export register** relevant to D,
* (\rho_{O,t}^D) is the **D-image shadow register carried inside O**,
* (\eta_{D,t}^O) is the **D-side native export register** relevant to O,
* (\rho_{D,t}^O) is the **O-image shadow register carried inside D**.

Again: these are interface-chart coordinates, not global ontological factors.

### 4.2 Only native export registers are packetized as payload

A key hardening rule is:

> Export payload is formed from the native export register (\eta), not from the imported image register (\rho).

Imported image state may appear only as tagged lineage, never as silently reclassified native witness.

Thus the projected packet maps are

[
\pi_{O\to D}^{\mathrm{proj}}(o_t)
=================================

\operatorname{pack}*{O\to D}!\big(
m*{O\to D}(\eta_{O,t}^D);
W_{O,t}^{\mathrm{nat}},
L_{O,t}^{\mathrm{imp}},
\lambda_{O,t},
\nu_{O,t}
\big),
]

[
\pi_{D\to O}^{\mathrm{proj}}(d_t)
=================================

\operatorname{pack}*{D\to O}!\big(
m*{D\to O}(\eta_{D,t}^O);
W_{D,t}^{\mathrm{nat}},
L_{D,t}^{\mathrm{imp}},
\lambda_{D,t},
\nu_{D,t}
\big).
]

Each projected packet has the form

[
p_{i\to j,t}
============

(\tau,\sigma,W_i^{\mathrm{nat}},L_i^{\mathrm{imp}},\lambda_i,\nu_i),
]

with the hard separation

[
W_i^{\mathrm{nat}} \cap L_i^{\mathrm{imp}} = \varnothing,
\qquad
\lambda_i \preceq_i \mathrm{ceil}_i(W_i^{\mathrm{nat}}).
]

So imported lineage may inform relevance, traceability, or local response. It may not contribute to native witness ceiling.

### 4.3 Admitted packet maps

Projected packets are only candidates. Lawful coupling begins only after admission.

Define total admission maps into admitted packet spaces plus an empty marker:

[
\hat\pi_{O\to D}^{\mathsf M}
============================

\operatorname{Adm}*{O\to D}^{\mathsf M}\circ \pi*{O\to D}^{\mathrm{proj}}
:
O \to \widehat P_{O\to D}\cup{\varnothing},
]

[
\hat\pi_{D\to O}^{\mathsf M}
============================

\operatorname{Adm}*{D\to O}^{\mathsf M}\circ \pi*{D\to O}^{\mathrm{proj}}
:
D \to \widehat P_{D\to O}\cup{\varnothing}.
]

Here (\varnothing) means **no admitted packet**. It is not a packet, carries no semantic content, and carries no authority.

### 4.4 Shadow-register updates

Imported image registers are updated only from admitted packets:

[
\rho_{O,t+1}^D = u_O^D(\rho_{O,t}^D,\hat p_{D\to O,t};\Pi),
]

[
\rho_{D,t+1}^O = u_D^O(\rho_{D,t}^O,\hat p_{O\to D,t};\Pi).
]

If (\hat p=\varnothing), the behavior is the declared fail-closed policy: hold, clear, age out, or descend. It is never “invent missing content.”

### 4.5 Native lane updates

The local native response then evolves by

[
(o_{t+1}^{\circ,D},\eta_{O,t+1}^D)
==================================

F_O^D(o_t^{\circ,D},\eta_{O,t}^D,\rho_{O,t+1}^D,u_t^O),
]

[
(d_{t+1}^{\circ,O},\eta_{D,t+1}^O)
==================================

F_D^O(d_t^{\circ,O},\eta_{D,t}^O,\rho_{D,t+1}^O,u_t^D).
]

This is the coupled boundary-subdynamic picture in hardened form:

* imported images update the shadow register,
* the receiving lane’s native boundary response evolves from that shadow register,
* full-lane interiors are not directly written by foreign packets.

The cross-lane effect is therefore endogenous to native dynamics, but membrane-governed.

### 4.6 Structural symmetry, semantic asymmetry

The schema is structurally symmetric: both sides have interface maps, packetization, admission, shadow registers, and boundary response laws.

But it remains semantically asymmetric.

In (O \leftrightarrow D):

* (O \to D) typically exports grounding and applicability conditions,
* (D \to O) typically exports admissibility pressure, closure requirements, and blocking distinctions.

So in general,

[
m_{O\to D} \neq m_{D\to O},\quad
\operatorname{pack}*{O\to D} \neq \operatorname{pack}*{D\to O},\quad
u_O^D \neq u_D^O,\quad
F_O^D \neq F_D^O.
]

Reciprocity does not imply equivalence.

---

## 5. Admissibility-before-coupling pipeline

The doctrinal order is now explicit and mandatory.

### Step 1. Extraction

[
b_{O,t}^D = \beta_O^D(o_t),\qquad
b_{D,t}^O = \beta_D^O(d_t).
]

### Step 2. Masking / projection

Only the contract-allowed native export registers are exposed:

[
\tilde\eta_{O,t}^D = m_{O\to D}(\eta_{O,t}^D),\qquad
\tilde\eta_{D,t}^O = m_{D\to O}(\eta_{D,t}^O).
]

### Step 3. Packetization

[
p_{O\to D,t} = \operatorname{pack}*{O\to D}(\tilde\eta*{O,t}^D;W_{O,t}^{\mathrm{nat}},L_{O,t}^{\mathrm{imp}},\lambda_{O,t},\nu_{O,t}),
]

[
p_{D\to O,t} = \operatorname{pack}*{D\to O}(\tilde\eta*{D,t}^O;W_{D,t}^{\mathrm{nat}},L_{D,t}^{\mathrm{imp}},\lambda_{D,t},\nu_{D,t}).
]

### Step 4. Admissibility judgment

[
\hat p_{O\to D,t}=\operatorname{Adm}*{O\to D}^{\mathsf M}(p*{O\to D,t})\in \widehat P_{O\to D}\cup{\varnothing},
]

[
\hat p_{D\to O,t}=\operatorname{Adm}*{D\to O}^{\mathsf M}(p*{D\to O,t})\in \widehat P_{D\to O}\cup{\varnothing}.
]

Only here does a lawful cross-lane object exist.

### Step 5. Import / adaptation

Imported images update only from admitted packets:

[
\rho_{O,t+1}^D = u_O^D(\rho_{O,t}^D,\hat p_{D\to O,t};\Pi),
\qquad
\rho_{D,t+1}^O = u_D^O(\rho_{D,t}^O,\hat p_{O\to D,t};\Pi).
]

### Step 6. Boundary coupling

Native boundary response laws run:

[
(o_{t+1}^{\circ,D},\eta_{O,t+1}^D)=F_O^D(\cdots),\qquad
(d_{t+1}^{\circ,O},\eta_{D,t+1}^O)=F_D^O(\cdots).
]

### Step 7. Coherence classification

Define the admitted history space over action horizon (h_a):

[
\widehat{\mathbb H}_{OD}^{(h_a)}
================================

\big((\widehat P_{O\to D}\cup{\varnothing})\times(\widehat P_{D\to O}\cup{\varnothing})\big)^{h_a}.
]

The current admitted history is

[
\widehat{\mathcal H}_{OD,t}^{(h_a)}
===================================

\big((\hat p_{O\to D,\tau},\hat p_{D\to O,\tau})\big)_{\tau=t-h_a+1}^{t}.
]

### Step 8. Action-class closure

Closure is evaluated only after coherence classification, witness-ceiling checks, witness-completeness checks, and reintegration sufficiency.

The critical consequence is this:

> The induced bridge regime is formed over admitted packet histories, not over raw projections.
> Inadmissible projected exports do not participate in lawful bridge content.

They can only contribute negatively through the fact of non-admission.

---

## 6. Typed coherence profile and regime classification

The scalar weighted-error model is no longer primary. The primary object is a typed profile with blocking-first, non-compensatory reading.

### 6.1 Action policy

For an action class (a), let

[
\Pi_a
=====

(h_a,\Sigma_a^{\mathrm{blk}},\Sigma_a^{\mathrm{req}},\Sigma_a^{\mathrm{adv}},G(a),\Omega(a),r_O(a),r_D(a)).
]

Here:

* (h_a) is the declared history horizon,
* (\Sigma_a^{\mathrm{blk}}) are blocking predicates,
* (\Sigma_a^{\mathrm{req}}) are act-required predicates,
* (\Sigma_a^{\mathrm{adv}}) are advisory predicates,
* (G(a)) is the set of acceptable regime classes,
* (\Omega(a)) is witness-completeness policy,
* (r_O(a), r_D(a)) are lane-specific force requirements.

Each predicate is declared, typed, and explicit:

[
\psi : \widehat{\mathbb H}_{OD}^{(h_a)} \to {\mathsf P,\mathsf U,\mathsf F}.
]

(\mathsf P) means pass, (\mathsf U) unknown, (\mathsf F) fail.

Unknown is not a numerical midpoint. For any predicate assigned to a blocking stratum, unknown is closure-negative.

### 6.2 Coherence profile

Define the action-specific coherence profile

[
\Gamma_{OD}^a(\widehat{\mathcal H})
===================================

\big(
v^{\mathrm{adm}},
v^{\mathrm{force}},
\mathbf s^{\mathrm{blk}},
\mathbf s^{\mathrm{req}},
\mathbf s^{\mathrm{adv}},
\rho
\big),
]

where:

* (v^{\mathrm{adm}} \in {\mathsf{clean},\mathsf{missing}}),
* (v^{\mathrm{force}} \in {\mathsf{within},\mathsf{violation}}),
* (\mathbf s^{\mathrm{blk}} = ( \psi(\widehat{\mathcal H}) )_{\psi\in\Sigma_a^{\mathrm{blk}}}),
* (\mathbf s^{\mathrm{req}} = ( \psi(\widehat{\mathcal H}) )_{\psi\in\Sigma_a^{\mathrm{req}}}),
* (\mathbf s^{\mathrm{adv}} = ( \psi(\widehat{\mathcal H}) )_{\psi\in\Sigma_a^{\mathrm{adv}}}),
* (\rho \in \mathsf{Reg}_a), where typically

[
\mathsf{Reg}_a
==============

{\mathsf{fixed},\mathsf{bounded},\mathsf{phase},\mathsf{oscillatory},\mathsf{incoherent}}.
]

### 6.3 Non-compensatory reading

The profile is read lexicographically, not additively:

1. admission status,
2. force-ceiling status,
3. blocking predicates,
4. act-required predicates,
5. regime class,
6. advisory predicates.

Thus no amount of advisory success can compensate for:

* missing admission,
* force-ceiling violation,
* blocking failure,
* blocking unknown.

Formally, the profile is action-allowable only if

[
\Gamma_{OD}^a(\widehat{\mathcal H}) \in \mathfrak A_a,
]

where

[
\mathfrak A_a
=============

\left{
\Gamma:
\begin{array}{l}
v^{\mathrm{adm}}=\mathsf{clean},[2pt]
v^{\mathrm{force}}=\mathsf{within},[2pt]
s=\mathsf P\ \forall s\in\mathbf s^{\mathrm{blk}},[2pt]
s=\mathsf P\ \forall s\in\mathbf s^{\mathrm{req}},[2pt]
\rho \in G(a)
\end{array}
\right}.
]

This is the primary closure basis. No scalar replaces it.

A scalar summary may still exist as a diagnostic convenience,

[
\delta_a : \mathsf{Prof}_a \rightharpoonup \mathbb R,
]

but only as a derived explanation or ranking device on already non-blocked cases. It has no closure authority.

### 6.4 Induced bridge regimes as extensional sets of admitted histories

For each action (a) and regime label (\rho), define

[
\mathfrak B_{OD}^{\rho,a}(\Pi_a)
\subseteq
\widehat{\mathbb H}_{OD}^{(h_a)}
]

as the policy-declared set of admitted histories whose profile has regime label (\rho).

Then the induced bridge regime is not a mediator object. It is one of these extensional subsets of admitted history space. The actual coupled system realizes a point in that history space; the classifier merely reports which extensional regime set contains it.

### 6.5 Classifier discipline: adjudicative only

Let

[
\mathcal J_{OD}^a : \widehat{\mathbb H}_{OD}^{(h_a)} \times \Pi_a \to \mathsf{Prof}_a
]

be the classifier/evaluator.

It must satisfy all of the following.

**Extensionality**
[
\widehat{\mathcal H}=\widehat{\mathcal H}' \ \land\ \Pi_a=\Pi_a'
;\Rightarrow;
\mathcal J_{OD}^a(\widehat{\mathcal H},\Pi_a)
=============================================

\mathcal J_{OD}^a(\widehat{\mathcal H}',\Pi_a').
]

**No latent semantic state**
If an implementation carries internal cache (z), it must be observationally inert:

[
\mathcal J_{OD}^{a,\mathrm{impl}}(z,\widehat{\mathcal H},\Pi_a)
===============================================================

\mathcal J_{OD}^{a,\mathrm{impl}}(z',\widehat{\mathcal H},\Pi_a)
]

for all (z,z').

**Replayability**
Archived admitted history plus declared policy must reproduce the same profile.

**No new witness source**
(\mathcal J_{OD}^a) may output only profile and regime labels. It may not output new witness, new force, or new semantic facts.

So the classifier may classify the bridge regime. It may not become the bridge.

---

## 7. Reintegration law and action adequacy

This is the missing doctrinal seam.

Boundary coherence is not, by itself, operational sufficiency.

### 7.1 Action semantics

Let (a) be a target action class with full-lane operational semantics

[
\operatorname{Exec}_a : U_a \rightharpoonup Y_a,
\qquad
U_a \subseteq O \times D.
]

(\operatorname{Exec}_a) represents the closure-relevant operational effect or operational result class of performing (a).

### 7.2 Compatibility class

Let (W_t^a) be the native witness footprint actually available for (a) at time (t).

Define the compatibility class

[
\mathcal K_a(\widehat{\mathcal H}_{OD,t}^{(h_a)},W_t^a)
=======================================================

\left{
(o',d')\in U_a
:
(o',d') \vDash_a \widehat{\mathcal H}_{OD,t}^{(h_a)}
\ \land
W^a(o',d')=W_t^a
\right},
]

where ((o',d') \vDash_a \widehat{\mathcal H}) means “compatible with the admitted history under the declared contract semantics for (a).”

### 7.3 Reintegration law

Define reintegration sufficiency by

[
\operatorname{RInt}*a(\widehat{\mathcal H}*{OD,t}^{(h_a)},W_t^a)=\top
\iff
\operatorname{Exec}*a
\text{ is constant on }
\mathcal K_a(\widehat{\mathcal H}*{OD,t}^{(h_a)},W_t^a).
]

Interpretation:

Once admitted history and available native witness are fixed, any masked or underdetermined interior degrees of freedom still compatible with them must be irrelevant to the operational result of (a).

If not, then membrane-level coherence is not enough for (a).

This is the hardened form of the earlier action-separation intuition.

### 7.4 Action authorization

Let

[
\Lambda_O^a(t)=\bigwedge_{\hat p\in \operatorname{Rel}*O^a(\widehat{\mathcal H}*{OD,t}^{(h_a)})}\lambda_O(\hat p),
\qquad
\Lambda_D^a(t)=\bigwedge_{\hat p\in \operatorname{Rel}*D^a(\widehat{\mathcal H}*{OD,t}^{(h_a)})}\lambda_D(\hat p).
]

Then

[
\operatorname{Close}_a(o_t,d_t)=\mathsf{allow}
]

iff all of the following hold:

[
\Gamma_{OD}^a(\widehat{\mathcal H}_{OD,t}^{(h_a)}) \in \mathfrak A_a,
]

[
\Omega(a)(W_t^a,\widehat{\mathcal H}_{OD,t}^{(h_a)})=\top,
]

[
r_O(a)\preceq_O \Lambda_O^a(t),
\qquad
r_D(a)\preceq_D \Lambda_D^a(t),
]

[
\operatorname{RInt}*a(\widehat{\mathcal H}*{OD,t}^{(h_a)},W_t^a)=\top.
]

If these fail for (a) but hold for a weaker (a' \prec a), then lawful descent is required rather than illicit closure.

So the membrane no longer says only, “the packets look coherent.” It says:

> the admitted boundary regime is action-adequate and reintegrable for this specific class of downstream act.

---

## 8. Witness ceilings, provenance law, and anti-laundering constraints

### 8.1 Witness ceiling law

For each lane (i \in {O,D}), native witness ceilings satisfy

[
\lambda_i(\hat p)\preceq_i \mathrm{ceil}_i(W_i^{\mathrm{nat}}(\hat p)).
]

Imported lineage (L_i^{\mathrm{imp}}) may never raise this ceiling.

Thus relevant current force is computed only from native witness-bearing packets:

[
\Lambda_i^a(t)=\bigwedge_{\hat p\in \operatorname{Rel}_i^a(\widehat{\mathcal H}_t)} \lambda_i(\hat p).
]

Using the meet, not a compensatory sum, is deliberate. It prevents force amplification by aggregation.

### 8.2 Provenance law for imported images

Imported shadow registers are not witness stores. They are provenance-tagged replayable images.

For each receiving lane, every imported register value carries provenance

[
\operatorname{Prov}(\rho_{O,t}^D)
\subseteq
{\operatorname{id}(\hat p_{D\to O,\tau}) : \tau \le t},
]

[
\operatorname{Prov}(\rho_{D,t}^O)
\subseteq
{\operatorname{id}(\hat p_{O\to D,\tau}) : \tau \le t}.
]

Moreover, the shadow registers are replayable from admitted packet history and declared update law:

[
\rho_{O,t+1}^D = u_O^D(\rho_{O,t}^D,\hat p_{D\to O,t};\Pi),
\qquad
\rho_{D,t+1}^O = u_D^O(\rho_{D,t}^O,\hat p_{O\to D,t};\Pi).
]

So the imported image store is transparent to replay. It is not an autonomous semantic reservoir.

### 8.3 Non-self-authentication law

Imported images remain imported:

[
\rho_{O,t}^D \notin \mathcal W_O^{\mathrm{nat}},
\qquad
\rho_{D,t}^O \notin \mathcal W_D^{\mathrm{nat}},
]

unless an explicit receiving-lane witnessing event occurs with new native witness basis.

Persistence does not authenticate.
Recurrence does not authenticate.
Reuse does not authenticate.

Only an explicit native witnessing transform, backed by new native witness, may create new native witness status. The imported image itself does not become native by being remembered.

### 8.4 No silent force minting, no silent fact minting

Let (\mathcal A_D^{\max}(d_t)) be the maximal deontic admissibility envelope supported by D’s own native witness. Then O-import may only select within it:

[
\mathcal A_D(d_t,\rho_{D,t}^O) \subseteq \mathcal A_D^{\max}(d_t).
]

So (O \to D) may ground applicability. It may not mint stronger D-force.

Likewise, let (\mathcal G_O^{\max}(o_t)) be the maximal set of O-grounded propositions supported by O’s own native witness. Then D-import may only constrain, focus, or block within it:

[
\mathcal G_O(o_t,\rho_{O,t}^D) \subseteq \mathcal G_O^{\max}(o_t).
]

So (D \to O) may pressure interpretation and closure readiness. It may not turn expectation into fact.

### 8.5 No-hidden-sovereign principle

No auxiliary artifact may become semantically sovereign for closure.

Not:

* the bridge regime label,
* the classifier state,
* the imported image store,
* the scalar diagnostic summary.

Closure is governed only by:

* native witness,
* declared membrane law,
* explicit admitted packet history,
* declared action policy,
* reintegration sufficiency.

Anything else is a hidden sovereign.

---

## 9. Pairwise default and higher-arity reserve

The default architecture remains pairwise.

For task-scoped lane set (L), use declared pairwise membrane contracts on the active edge set (E_q). This is still the correct default.

But pairwise coherence is not universally complete.

### 9.1 Pairwise adequacy criterion

Let (H_a \subseteq L) be the lanes relevant to action (a). Pairwise contracts are (a)-adequate on (U_a) only if

[
\forall x,x' \in U_a,
\quad
\Big(
\Gamma_{ij}^a(x)=\Gamma_{ij}^a(x')
\ \forall (i,j)\in E(H_a)
\Big)
\Rightarrow
\operatorname{Exec}_a(x)=\operatorname{Exec}_a(x').
]

If this implication fails, then independent pairwise coherence does not determine action adequacy.

### 9.2 Higher-arity reserve

When pairwise adequacy fails, introduce a task-scoped higher-arity membrane contract

[
\mathsf M_{H_a}
]

over the relevant joint interface slice or joint admitted-history family.

This is not a new mediator lane. It is a reserved joint membrane law for irreducibly joint actions.

Typical cases:

* (O!-!E!-!D): applicability and evidential sufficiency interact jointly,
* (O!-!D!-!U): utility may matter only within a jointly declared ontic/deontic envelope.

Doctrine rule:

> Pairwise contracts are the default.
> Higher-arity contracts are introduced only when pairwise profiles are formally inadequate for the target action class.

---

## 10. Failure taxonomy

**1. Interface inflation.**
A contract-local chart such as (O^{\circ,D}\times B_O^D) is treated as a global metaphysical decomposition of (O). This overstates interface law into ontology.

**2. Full-lane overexposure.**
A projection exports material outside the declared mask, or foreign packets directly drive interior state rather than boundary response.

**3. Under-projection.**
The interface omits variables required by declared predicates or reintegration for the target act. The boundary looks clean only because it is too thin.

**4. Inadmissible projection counted as bridge content.**
A raw projected packet is treated as if it had entered lawful coupling even though admission failed. This collapses the membrane.

**5. Compensatory score laundering.**
A single score trades off blocking unknowns, force violations, or missing admission against other successes. This is pseudo-rigor and doctrinally invalid.

**6. Classifier sovereignty.**
The evaluator carries hidden state, hidden memory, or undeclared features, so identical admitted histories under identical policy can yield different regime labels.

**7. Provenance accretion.**
Imported image registers persist long enough to be treated as if they were native witness. This slowly turns shadow state into fake evidence.

**8. Re-export laundering.**
Imported content reappears as if it were native payload rather than tagged lineage. The system silently certifies what it merely received.

**9. Force amplification.**
The coupled regime licenses stronger closure than the native witness ceilings support.

**10. Pseudo-alignment by lossy projection.**
Boundary packets match, but hidden interior distinctions still matter for the target act. Without reintegration, this is false coherence.

**11. Membrane capture by one lane.**
The receiving boundary response becomes dominated by imported shadow state rather than remaining lane-native.

**12. Oscillation misread as lawful coupling.**
A visibly repeating pattern is mistaken for acceptable oscillation even though blocking unknowns remain unresolved or amplitudes are not policy-bounded.

**13. Pairwise completeness error.**
Independent pairwise coherence is assumed sufficient for an action that actually requires irreducibly joint consistency across a larger task-scoped subgraph.

---

## 11. Worked examples

### Example A. Clean (O/D) coupling with exact execution authorization

Retain the execution-governance case, but harden it with the revised seams.

#### O-side native export register

At time (t), O’s relevant export register contains:

* signature valid,
* trust anchor match,
* revocation freshness present,
* scope hash match,
* capability subset match.

The projected O-packet is

[
p_{O\to D,t}
============

(\texttt{exec_fact},\sigma_O,W_O^{\mathrm{nat}},L_O^{\mathrm{imp}},\lambda_O,\nu_O),
]

with (\sigma_O) carrying exactly those fields. Admission succeeds, so (\hat p_{O\to D,t}\neq\varnothing).

#### D-side native export register

D’s export register contains the deontic gate conditions:

* execution requires signature validity,
* anchor match,
* fresh revocation check,
* scope match,
* capability subset,
* any missing high-impact item blocks exact execution.

This yields admitted packet (\hat p_{D\to O,t}).

#### Typed coherence profile

For action (a_{\mathrm{run}}), let

[
\Sigma_{a_{\mathrm{run}}}^{\mathrm{blk}}
========================================

{
\texttt{sig_valid},
\texttt{anchor_match},
\texttt{revocation_fresh},
\texttt{scope_match},
\texttt{cap_subset}
}.
]

All evaluate to (\mathsf P). No force violation occurs. The current admitted history falls in (\mathfrak B_{OD}^{\mathsf{fixed},a_{\mathrm{run}}}).

So

[
\Gamma_{OD}^{a_{\mathrm{run}}}(\widehat{\mathcal H}*t)
\in
\mathfrak A*{a_{\mathrm{run}}}.
]

#### Reintegration

For exact taskpack execution, the declared operational effect depends only on those gate variables and their current native witnesses. No masked interior degree of freedom in the contract domain changes the allow/deny outcome once these are fixed.

So

[
\operatorname{RInt}*{a*{\mathrm{run}}}(\widehat{\mathcal H}*t,W_t^{a*{\mathrm{run}}})=\top.
]

#### Result

Exact execution is authorized.

Nothing here required a bridge layer. The bridge is just the lawful admitted-history regime of the coupled O-side and D-side boundary subdynamics.

---

### Example B. False bridge by compensatory score and hidden state

Keep the earlier false-bridge case, but harden the diagnosis.

Suppose a mediator score is introduced:

[
s_t
===

0.45\cdot \texttt{sig_valid}
+
0.20\cdot \texttt{deadline_urgency}
+
0.20\cdot \texttt{prior_success}
+
0.15\cdot \texttt{operator_confidence}.
]

Execution is then authorized if (s_t > 0.8).

This fails in two distinct ways.

#### First failure: compensatory laundering

Assume (\texttt{revocation_fresh}=\mathsf U), which is blocking for exact execution. Even if all other terms are high, a blocking unknown may not be traded away. The typed profile blocks; the score does not. Therefore the score is not merely a summary. It is an illicit closure basis.

#### Second failure: hidden sovereignty

If (\texttt{prior_success}) or (\texttt{operator_confidence}) are not part of the admitted O/D packet history and declared policy, then two identical admitted histories can yield different (s_t). That makes the score state semantically active.

If urgency genuinely matters, it must enter through an explicit declared contract, perhaps (D \leftrightarrow U) or an irreducibly joint (O!-!D!-!U) contract. It may not be smuggled into an undeclared bridge score.

So this case is not “stronger synchronization.” It is hidden bridge sovereignty plus compensatory laundering.

---

### Example C. Partial oscillatory coupling with lawful descent

Again keep the execution setting, but classify it under the hardened regime model.

Suppose O-side revocation freshness alternates between admitted and unavailable.

At even times:
[
\hat p_{O\to D,t}\ \text{contains}\ \texttt{revocation_fresh}=\mathsf P.
]

At odd times:
[
\hat p_{O\to D,t+1}=\varnothing
]
for the freshness field because fresh witness is unavailable and admission fails.

D-side threshold packet remains stable: exact execution requires fresh revocation status; staging-only preparation does not.

#### For exact execution

The action policy (a_{\mathrm{run}}) treats fresh revocation as blocking. Therefore the current admitted history does not enter (\mathfrak A_{a_{\mathrm{run}}}) whenever the history window includes missing fresh admission at a required slot.

So exact execution remains blocked.

#### For staging / refresh

Consider a weaker action (a_{\mathrm{stage}}) with policy:

* exact execution not permitted,
* local staging permitted,
* explicit refresh request required,
* oscillatory regime acceptable if no irreversible action occurs.

Then the same admitted history may satisfy

[
\Gamma_{OD}^{a_{\mathrm{stage}}}(\widehat{\mathcal H}*t)\in \mathfrak A*{a_{\mathrm{stage}}},
\qquad
\operatorname{RInt}*{a*{\mathrm{stage}}}=\top.
]

So the system lawfully descends:

* not run,
* do stage,
* request refresh,
* hold stronger commitment.

This is genuine bounded endogenous coupling without false finality.

---

### Example D. (E \leftrightarrow D) threshold / sufficiency case outside execution governance

To show the theory is not merely an execution-trust formalism, use an evidential/deontic case.

Let the action classes be:

* (a_{\mathrm{confirm}}): issue a confirmed incident notice,
* (a_{\mathrm{investigate}}): open an investigation without confirming the incident.

#### E-side interior and boundary export

The evidential lane (E) has a rich interior:

* source graph,
* chain-of-custody details,
* measurement metadata,
* contradiction analysis,
* source-independence structure.

Its membrane-facing export register exposes only:

* corroboration count,
* source independence status,
* chain integrity status,
* material contradiction status.

At time (t), the admitted E-packet says:

[
\texttt{corroboration_count}=1,\quad
\texttt{source_independence}=\mathsf U,\quad
\texttt{chain_integrity}=\mathsf P,\quad
\texttt{material_contradiction}=\mathsf P.
]

#### D-side interior and boundary export

The deontic lane (D) contains the native rules:

* confirmed notice requires at least two independent corroborating sources,
* any material contradiction blocks confirmation,
* an investigation may be opened on one credible source with intact chain,
* unknown independence blocks confirmation but not preliminary investigation.

So D exports a threshold packet expressing exactly those requirements.

#### Typed profiles

For (a_{\mathrm{confirm}}):

[
\Sigma_{a_{\mathrm{confirm}}}^{\mathrm{req}}
============================================

{
\texttt{corroboration_count}\ge 2,
\texttt{source_independence}=\mathsf P,
\texttt{material_contradiction}=\mathsf P
}.
]

These do not all pass. Confirmation is not authorized.

For (a_{\mathrm{investigate}}):

[
\Sigma_{a_{\mathrm{investigate}}}^{\mathrm{req}}
================================================

{
\texttt{corroboration_count}\ge 1,
\texttt{chain_integrity}=\mathsf P
}.
]

These pass. The admitted history may therefore fall in an allowed bounded regime for investigation.

#### Reintegration

For opening an investigation, the masked interior details of the evidence graph do not alter the action once the visible threshold conditions are fixed. So reintegration holds.

For issuing a confirmed notice, however, the hidden independence structure still matters. Reintegration does not hold until that structure is either exposed in the boundary contract or independently resolved by native evidence.

#### Result

The system does not need a mediator saying “overall evidence quality = 0.78.” It needs only:

* E’s admitted evidential boundary image,
* D’s admitted threshold boundary image,
* their typed profile,
* action-specific reintegration.

The bridge remains endogenous.

---

## 12. Compact propositions / theorems

### Proposition 1. Interface modesty

Any decomposition written as (X_i \cong X_i^\circ \times B_i^j) in this framework is doctrine-valid only as a contract-local chart or local factorization unless global factorization is independently proven.

**Reason.**
The membrane governs observation, exposure, and coupling rights; it does not, by itself, legislate lane ontology.

---

### Proposition 2. Admissibility precedence

If a projected packet (p_{i\to j,t}) fails admission, then it contributes no lawful bridge content. Only (\varnothing) enters the admitted history.

**Reason.**
The bridge regime is defined over admitted histories, not raw projections.

---

### Proposition 3. Non-compensability

For any action (a), if (v^{\mathrm{adm}}=\mathsf{missing}), or (v^{\mathrm{force}}=\mathsf{violation}), or any blocking predicate is not (\mathsf P), then no advisory success can place (\Gamma_{ij}^a) in (\mathfrak A_a).

**Reason.**
The profile is lexicographic and blocking-first, not additive.

---

### Proposition 4. Classifier non-sovereignty

If (\mathcal J_{ij}^a) is extensional in admitted history and policy, replayable, and state-free up to observational equivalence, then the classifier is not semantically sovereign.

Formally, any implementation state (z) is inert iff

[
\mathcal J_{ij}^{a,\mathrm{impl}}(z,\widehat{\mathcal H},\Pi_a)
===============================================================

\mathcal J_{ij}^{a,\mathrm{impl}}(z',\widehat{\mathcal H},\Pi_a)
]

for all (z,z').

**Reason.**
Then regime labels are only names for extensional history sets.

---

### Proposition 5. Imported-image non-authentication

If imported image registers are provenance-tagged and replayable from admitted packet history via declared update law, then persistence or repetition of imported content does not create native witness.

**Reason.**
The register remains in shadow-image space unless an explicit receiving-lane witnessing event supplies new native witness basis.

---

### Proposition 6. Reintegration necessity

Boundary coherence and witness ceilings are necessary but not sufficient for action authorization. Sufficiency for (a) requires

[
\operatorname{RInt}_a(\widehat{\mathcal H},W^a)=\top.
]

**Reason.**
Otherwise masked interior degrees of freedom still affect the operational result of (a).

---

### Proposition 7. Pairwise reserve criterion

If there exist (x,x' \in U_a) with identical relevant pairwise profiles but different (\operatorname{Exec}_a) outcomes, then pairwise contracts are not (a)-adequate and a higher-arity contract is required.

**Reason.**
Independent pairwise coherence then fails to determine action adequacy.

---

### Proposition 8. Hidden bridge redundancy or ban

Any explicit bridge object reducible to extensional membership in policy-defined admitted-history regimes is redundant. Any bridge object not so reducible is semantically sovereign and banned.

**Reason.**
There is no third permissible case.

---

## 13. Closing doctrinal statement

The hardened doctrine is now exact.

The membrane is not a place where full lanes talk to each other. It is the law governing which projected boundary images may be extracted, masked, packetized, admitted, imported, coupled, classified, and relied upon.

The boundary band is an interface object, not automatically a metaphysical component. Projected packets are not yet lawful bridge elements; only admitted packets are. Coherence is not a weighted score; it is a typed, blocking-first profile over admitted packet histories. The regime classifier is adjudicative only: replayable, extensional, and non-authority-minting. Boundary coherence is not sufficient for closure unless reintegration for the target action class succeeds. Imported images remain provenance-tagged shadow state, not native witness. Pairwise contracts remain the default, with higher-arity reserve only where pairwise adequacy is formally insufficient.

So the final doctrine-grade claim is:

* cross-lane alignment in ODEU need not be mediated by a sovereign bridge layer;
* it is realized as endogenous synchronization of membrane-facing boundary subdynamics inside native lanes;
* the lawful object of coupling is the admitted packet history, not raw cross-lane exposure;
* the induced bridge regime is an extensional regime over those admitted histories, not a new ontology;
* and downstream closure is permitted only when typed coherence, witness ceilings, witness completeness, and reintegration sufficiency all hold for the target action class.

That closes the remaining seams without changing the architecture.
