## 1. Executive sharpening summary

This pass leaves the architecture intact and closes the last four live seams in the 2nd hardening note: reintegration is made witness-bearing rather than oracle-like; shadow-state influence is prevented from laundering itself into later “native” export; admission is refined from coarse presence/absence into a typed verdict; and the raw evaluated profile is separated cleanly from regime classification. A short same-family audit then patches the remaining edge cases of the same kind: vacuous reintegration on empty compatibility classes, hidden discretion in admission, and echo-amplification of recirculated provenance. The retained backbone remains unchanged. 

## 2. Retained architecture statement

Nothing essential is reopened. The following remain as previously fixed: the bridge is endogenous rather than sovereign; the membrane governs lawful extraction, masking, packetization, admission, import, coupling, classification, and closure; boundary bands are contract-local interface objects rather than silently global ontology; only admitted packet histories participate in lawful coupling; coherence is typed and blocking-first; the classifier is extensional and replayable; reintegration is required for operational sufficiency; imported images remain provenance-tagged and non-self-authenticating; pairwise contracts are the default, with higher-arity reserve only where pairwise adequacy fails. 

What follows is surgical: it closes loopholes without changing that structure.

## 3. Reintegration witness law

Retain the semantic truth-condition for reintegration, but make positive assertion witness-governed and non-vacuous.

### 3.1 Semantic condition, sharpened

Let the verdict-tagged admitted history for action horizon (h_a) be denoted

[
\widetilde{\mathcal H}_{OD,t}^{(h_a)}.
]

Let (W_t^a) be the native witness footprint relevant to action (a), and let

[
\mathcal K_a(\widetilde{\mathcal H}_{OD,t}^{(h_a)},W_t^a)
\subseteq U_a
]

be the compatibility class as before.

Define semantic reintegration sufficiency by

[
\operatorname{RInt}^{\mathrm{sem}}*a(\widetilde{\mathcal H}*{OD,t}^{(h_a)},W_t^a)=\top
\iff
\mathcal K_a(\widetilde{\mathcal H}_{OD,t}^{(h_a)},W_t^a)\neq\varnothing
\ \land
\operatorname{Exec}*a
\text{ is constant on }
\mathcal K_a(\widetilde{\mathcal H}*{OD,t}^{(h_a)},W_t^a).
]

The non-emptiness clause matters. Otherwise reintegration could hold vacuously on an impossible compatibility class.

### 3.2 Reintegration witness family

For each action class (a), declare a reintegration-witness family

[
\mathsf{Cert}_a^{R},
]

together with a replayable verifier

[
\operatorname{Chk}_a^{R} :
\mathsf{Cert}*a^{R}
\times
\widetilde{\mathbb H}*{OD}^{(h_a)}
\times
\mathcal W_a
\times
\Pi_a
\to
{\mathsf P,\mathsf F}.
]

A reintegration certificate may be any declared artifact of one of the following strict forms:

* an explicit separability proof over the active interface,
* an action-specific adequacy theorem,
* an exhaustive bounded partition of the compatibility class on which (\operatorname{Exec}_a) is constant per cell,
* a contract-pinned adequacy artifact of equivalent strength.

No undeclared checker may “just know” that reintegration holds.

### 3.3 Operational assertion law

A system may assert positive reintegration status only if there exists a declared certificate that passes verification:

[
\operatorname{RInt}^{\mathrm{op}}*a(\widetilde{\mathcal H}*{OD,t}^{(h_a)},W_t^a)=\top
\iff
\exists c\in \mathsf{Cert}_a^{R}
\text{ such that }
\operatorname{Chk}*a^{R}(c,\widetilde{\mathcal H}*{OD,t}^{(h_a)},W_t^a,\Pi_a)=\mathsf P.
]

Soundness is mandatory:

[
\operatorname{Chk}_a^{R}(c,\widetilde{\mathcal H},W,\Pi_a)=\mathsf P
;\Rightarrow;
\operatorname{RInt}^{\mathrm{sem}}_a(\widetilde{\mathcal H},W)=\top.
]

Completeness is not required. A system may fail to certify a true reintegration condition and therefore descend or block; it may not certify without witness.

### 3.4 Verifier discipline

The reintegration verifier itself must satisfy the same anti-sovereignty conditions already imposed on regime classification:

[
(c,\widetilde{\mathcal H},W,\Pi_a)=(c',\widetilde{\mathcal H}',W',\Pi_a')
\Rightarrow
\operatorname{Chk}_a^{R}(c,\widetilde{\mathcal H},W,\Pi_a)
==========================================================

\operatorname{Chk}_a^{R}(c',\widetilde{\mathcal H}',W',\Pi_a').
]

So reintegration status is inspectable, replayable, and non-intuitive. It is not a discretionary impression.

## 4. Lineage-preserving re-export / native re-witnessing law

This closes the last major laundering path.

### 4.1 Field-origin metadata

Refine packet metadata so that the provenance component (\nu_i) explicitly contains both provenance and field-origin status:

[
\nu_i = (\operatorname{Prov}_i,\omega_i),
]

where for each exported field (f) of payload (\sigma_i),

[
\omega_i(f)\in{\mathsf{nat},\mathsf{der},\mathsf{rewit}}.
]

Interpretation:

* (\mathsf{nat}): supported purely by current-lane native witness,
* (\mathsf{der}): materially shaped by imported shadow state and therefore derived,
* (\mathsf{rewit}): previously shadow-influenced, but re-grounded by a fresh native witnessing event.

### 4.2 Shadow-influence criterion

For a receiving lane (i) and its export field (f) inside (\eta_i^j), write

[
f \triangleleft \rho_i^j
]

iff under the declared update law there exist two admissible histories with the same lane-(i) native inputs and same lane-(i) native witness basis, but different imported shadow histories, such that the value of (f) differs.

This is the doctrine-grade meaning of “materially shaped by imported shadow state.”

### 4.3 Lineage-preserving export law

If (f \triangleleft \rho_i^j) and no re-witnessing event has occurred, then any later export of (f) must satisfy all of the following:

[
\omega_i(f)=\mathsf{der},
]

[
\operatorname{Prov}_i(f)\cap \operatorname{ImpRoot}_i^j \neq \varnothing,
]

[
f \notin W_i^{\mathrm{nat}},
]

and (f) may not increase (\lambda_i).

So a shadow-influenced field may be exported as derived content, but it may not silently reappear as purely native witness-bearing support.

### 4.4 Native re-witnessing law

A shadow-influenced field may re-enter native-authority space only through a declared fresh witnessing event.

For each such field (f), declare a re-witnessing certificate family

[
\mathsf{Cert}_{i,f}^{RW}
]

and verifier

[
\operatorname{Chk}*{i,f}^{RW} :
\mathsf{Cert}*{i,f}^{RW}
\times
\widetilde{\mathbb H}
\times
\Pi
\to
{\mathsf P,\mathsf F}.
]

If a certificate (c) passes,

[
\operatorname{Chk}_{i,f}^{RW}(c,\widetilde{\mathcal H},\Pi)=\mathsf P,
]

then (f) may be marked

[
\omega_i(f)=\mathsf{rewit},
]

with a fresh native witness basis (W_{i,f}^{RW}), and the field may contribute to native force only through that fresh basis:

[
\lambda_i(f)\preceq_i \mathrm{ceil}*i(W*{i,f}^{RW}).
]

The earlier imported provenance is not erased. Re-witnessing re-grounds authority; it does not delete lineage.

### 4.5 Echo non-independence corollary

To prevent recirculated foreign influence from counting twice, define an ultimate-source equivalence relation on provenance roots:

[
u \sim_{\mathrm{root}} v
\iff
\operatorname{Root}(u)=\operatorname{Root}(v).
]

Independence tests, corroboration counts, and support aggregation operate on (\sim_{\mathrm{root}})-classes, not on raw occurrences. So an echoed packet that returns after cross-lane circulation is not new independent support.

## 5. Typed admission verdict and closure semantics

The coarse distinction ( \mathsf{clean}/\mathsf{missing} ) is replaced by a bounded typed verdict.

### 5.1 Admission verdict set

For direction (i\to j), let

[
\mathsf V_{i\to j}^{adm}
========================

{
\mathsf{adm},
\mathsf{abs},
\mathsf{rej},
\mathsf{stl},
\mathsf{unk},
\mathsf{wth},
\mathsf{prt}
}.
]

Interpretation:

* (\mathsf{adm}): admitted in full,
* (\mathsf{abs}): no packet is owed or applicable under the current contract state,
* (\mathsf{rej}): projected packet was present but rejected as inadmissible,
* (\mathsf{stl}): would otherwise be admissible but is stale or expired for the active horizon,
* (\mathsf{unk}): admissibility or required structure is itself undetermined,
* (\mathsf{wth}): explicitly withheld under a declared withholding rule,
* (\mathsf{prt}): partial admission of a declared subpacket.

### 5.2 Refined admission operator

The membrane admission judgment now returns a verdict-tagged result:

[
\operatorname{Adm}_{i\to j}^{\mathsf M}(p)
==========================================

(v_{i\to j},\hat p_{i\to j}),
]

with

[
v_{i\to j}\in \mathsf V_{i\to j}^{adm}.
]

Only (v_{i\to j}\in{\mathsf{adm},\mathsf{prt}}) may yield a nonempty admitted packet. Otherwise,

[
\hat p_{i\to j}=\varnothing.
]

If (v_{i\to j}=\mathsf{prt}), the admitted subpacket and the excluded residual fields must be explicit in the packet’s provenance/mask metadata. Partial admission is never silent truncation.

### 5.3 Admission discipline

Admission is itself an adjudicative function and therefore must be extensional and replayable:

[
p=p',\ \mathsf M=\mathsf M'
\Rightarrow
\operatorname{Adm}_{i\to j}^{\mathsf M}(p)
==========================================

\operatorname{Adm}_{i\to j}^{\mathsf M'}(p').
]

No hidden admission memory, no latent risk score, no undeclared implementation discretion.

### 5.4 Verdict-tagged admitted history

Replace the earlier admitted-history notation by the verdict-tagged form

[
\widetilde{\mathcal H}_{OD,t}^{(h_a)}
=====================================

\Big(
(v_{O\to D,\tau},\hat p_{O\to D,\tau}),
(v_{D\to O,\tau},\hat p_{D\to O,\tau})
\Big)_{\tau=t-h_a+1}^{t}.
]

Strictly speaking, this is the lawful object of coupling and closure: not raw projections, not bare admitted packets, but verdict-tagged admitted history.

### 5.5 Action-class reading of verdicts

For each action (a), declare an admission-handling policy

[
\Xi_a :
(\mathsf V_{O\to D}^{adm}\times \mathsf V_{D\to O}^{adm})^{h_a}
\to
{\mathsf{pass},\mathsf{descend},\mathsf{block}}.
]

Default doctrine:

* (\mathsf{adm}) passes,
* (\mathsf{abs}) is neutral only where the contract declares the packet not owed for (a); otherwise it blocks,
* (\mathsf{rej}), (\mathsf{stl}), and (\mathsf{unk}) block whenever any blocking or required predicate depends on the missing content,
* (\mathsf{wth}) blocks unless (a) explicitly authorizes withholding-compatible descent,
* (\mathsf{prt}) passes only if every blocking and required predicate is decidable from the admitted subpacket; otherwise it descends or blocks by declared policy.

This prevents materially distinct states from collapsing into generic “missing.”

## 6. Raw profile versus regime classification cleanup

The raw evaluated profile and regime label are now separated.

### 6.1 Raw evaluated profile

Define the raw action-specific evaluated profile

[
\Phi_{OD}^a(\widetilde{\mathcal H})
===================================

\big(
\mathbf v^{adm},
v^{force},
\mathbf s^{blk},
\mathbf s^{req},
\mathbf s^{adv}
\big),
]

where:

* (\mathbf v^{adm}) is the verdict sequence extracted from (\widetilde{\mathcal H}),
* (v^{force}\in{\mathsf{within},\mathsf{violation}}),
* (\mathbf s^{blk},\mathbf s^{req},\mathbf s^{adv}) are the blocking, required, and advisory predicate vectors.

### 6.2 Regime classification

Define the regime classifier separately:

[
\mathcal R_{OD}^a :
\widetilde{\mathbb H}_{OD}^{(h_a)} \times \Pi_a
\to
\mathsf{Reg}_a.
]

Then the combined adjudication report is

[
\Gamma_{OD}^a(\widetilde{\mathcal H},\Pi_a)
===========================================

\big(
\Phi_{OD}^a(\widetilde{\mathcal H}),
\mathcal R_{OD}^a(\widetilde{\mathcal H},\Pi_a)
\big).
]

No circularity remains: the raw profile is evaluated first; the regime label is then assigned.

### 6.3 Allowability

Define action allowability by

[
\Gamma_{OD}^a(\widetilde{\mathcal H},\Pi_a)\in \mathfrak A_a
]

iff all of the following hold:

[
\Xi_a(\mathbf v^{adm})=\mathsf{pass},
]

[
v^{force}=\mathsf{within},
]

[
s=\mathsf P \quad \forall s\in\mathbf s^{blk},
\qquad
s=\mathsf P \quad \forall s\in\mathbf s^{req},
]

[
\mathcal R_{OD}^a(\widetilde{\mathcal H},\Pi_a)\in G(a).
]

A scalar summary may still exist diagnostically, but it is downstream of this structure and has no closure authority.

### 6.4 Induced bridge regimes

The induced bridge regime remains extensional, now over verdict-tagged admitted histories:

[
\mathfrak B_{OD}^{\rho,a}(\Pi_a)
================================

{
\widetilde{\mathcal H}\in \widetilde{\mathbb H}*{OD}^{(h_a)}
:
\mathcal R*{OD}^a(\widetilde{\mathcal H},\Pi_a)=\rho
}.
]

The bridge is still not a mediator object. It is a policy-declared subset of lawful admitted-history space.

## 7. Small formal cleanups

### 7.1 Pairwise adequacy notation

Where pairwise adequacy is used, make the history dependency explicit.

For a full task-state (x\in U_a), let

[
\widetilde{\mathcal H}_{ij}^a(x)
]

be the verdict-tagged admitted history induced on pair ((i,j)) under the declared contract and horizon for action (a).

Then pairwise adequacy reads:

[
\forall x,x'\in U_a,\quad
\Big(
\Gamma_{ij}^a(\widetilde{\mathcal H}_{ij}^a(x),\Pi_a)
=====================================================

\Gamma_{ij}^a(\widetilde{\mathcal H}_{ij}^a(x'),\Pi_a)
\ \forall (i,j)\in E(H_a)
\Big)
\Rightarrow
\operatorname{Exec}_a(x)=\operatorname{Exec}_a(x').
]

This preserves the ontology/interface distinction.

### 7.2 Empty-meet case

For lane (i), define

[
\Lambda_i^a(t)
==============

\bigwedge_{\hat p\in \operatorname{Rel}*i^a(\widetilde{\mathcal H}*{OD,t}^{(h_a)})}\lambda_i(\hat p),
]

with the explicit convention

[
\bigwedge \varnothing := \bot_i,
]

where (\bot_i) is the least force element, meaning “no support.”

Therefore any action with nontrivial force requirement fails closed if the relevant packet set is empty:

[
r_i(a)\npreceq_i \bot_i
]

for all nonzero-force acts. Only an explicitly declared zero-force housekeeping act may lawfully proceed against (\bot_i).

### 7.3 Updated closure condition

The closure rule is now:

[
\operatorname{Close}_a(o_t,d_t)=\mathsf{allow}
]

iff all of the following hold:

[
\Gamma_{OD}^a(\widetilde{\mathcal H}_{OD,t}^{(h_a)},\Pi_a)\in \mathfrak A_a,
]

[
\Omega(a)(W_t^a,\widetilde{\mathcal H}_{OD,t}^{(h_a)})=\top,
]

[
r_O(a)\preceq_O \Lambda_O^a(t),
\qquad
r_D(a)\preceq_D \Lambda_D^a(t),
]

[
\operatorname{RInt}*a^{\mathrm{op}}(\widetilde{\mathcal H}*{OD,t}^{(h_a)},W_t^a)=\top.
]

If these fail for (a) but hold for (a'\prec a), lawful descent is required.

## 8. Residual blindspot scan

**Admission checker as hidden sovereign — patched.**
The refined admission operator is now extensional, replayable, and verdict-typed. It is no longer a coarse status bucket or a hidden discretionary gate.

**Vacuous reintegration on impossible histories — patched.**
The non-emptiness condition on (\mathcal K_a) blocks vacuous truth.

**Shadow influence laundering through re-export — patched.**
Field-origin status and re-witnessing law now prevent shadow-shaped coordinates from reappearing as silently native witness-bearing export.

**Echo amplification / recirculated provenance counted twice — patched.**
Root-provenance equivalence ensures echoed lineage is not independent support.

**Freshness seam — patched.**
Stale/expired status is now explicit in admission verdicts and therefore policy-readable rather than hidden inside “missing.”

**Summary object accidentally becoming sovereign — already closed.**
The scalar summary remains diagnostic only, and the raw-profile/regime split removes the remaining presentation ambiguity.

**Interface-law silently becoming ontology — already closed.**
Boundary bands remain contract-local interface objects, not universal lane factors.

**No additional same-family seam found.**
After these patches, no further blindspot of the same structural type remains materially open.

## 9. Revised compact propositions / doctrinal clauses

The earlier propositions on interface modesty, admissibility precedence, classifier non-sovereignty, pairwise reserve, and hidden bridge redundancy remain in force. The present sharpening adds the following.

**Proposition 1. Reintegration witness requirement.**
Positive reintegration status for action (a) may be asserted only if a declared reintegration certificate passes a replayable verifier; absent such a certificate, reintegration may not be asserted as a basis for closure.

**Proposition 2. Reintegration non-vacuity.**
If (\mathcal K_a(\widetilde{\mathcal H},W)=\varnothing), then (\operatorname{RInt}^{\mathrm{sem}}_a(\widetilde{\mathcal H},W)\neq\top).

**Proposition 3. Shadow-influenced export non-nativity.**
If an exported field is materially shadow-influenced and has not been freshly re-witnessed, then it must remain derived, provenance-tagged, and non-authority-bearing.

**Proposition 4. Re-witnessing without provenance erasure.**
Fresh native re-witnessing may re-ground authority for a field, but it does not erase imported lineage from that field’s provenance history.

**Proposition 5. Typed admission non-conflation.**
Admission verdicts (\mathsf{abs}, \mathsf{rej}, \mathsf{stl}, \mathsf{unk}, \mathsf{wth}, \mathsf{prt}) are materially distinct policy states and may not be collapsed into a generic “missing” status for closure.

**Proposition 6. Empty-support fail-closure.**
If (\operatorname{Rel}_i^a(\widetilde{\mathcal H})=\varnothing), then (\Lambda_i^a=\bot_i), which is insufficient for any nontrivial action requirement.

**Proposition 7. Echoed-lineage non-independence.**
Support items with the same root provenance may not be counted as independent corroboration or cumulatively stronger support merely by circulation or repetition.

## 10. Closing promotion-readiness statement

The doctrine is now lock-clean on the seams that were still open.

Reintegration can no longer be asserted as an oracle intuition; it requires a declared witness form. Shadow-state influence can no longer re-emerge as silently native authority; it must remain lineage-tagged as derived, or be freshly re-witnessed without provenance erasure. Admission is no longer a coarse presence/absence bucket; it is a typed verdict with action-class-specific semantics. Raw evaluated profile and regime classification are now separate. Empty-set edge cases are fail-closed or explicitly governed. The remaining same-family blindspots have been scanned and either patched or confirmed already closed.

That leaves the main architecture unchanged and promotion-ready:

* the bridge remains endogenous, not sovereign;
* the lawful coupling object is the verdict-tagged admitted packet history;
* closure remains governed only by native witness, declared membrane law, explicit action policy, replayable adjudication, and certified reintegration;
* and no hidden bridge, checker, shadow store, summary object, or empty-case loophole remains available to mint authority.
