## VERTICAL_ALIGNMENT_ARCHITECTURE_HARDENED

The v0 backbone stands. Alignment remains a problem of **vertical lawful descent**, not horizontal preference fit. The hardening move is to make three things explicit that v0 only implied:

1. publicity is **segment-level**, not artifact-level;
2. legitimacy requires **two coupled chains**, not one;
3. runtime legality is governed by **status propagation**, not static issuance alone.

The retained `Envelope / Payload` split now becomes:

```text
Artifact a :=
  <Envelope(a), PayloadSegments(a), WitnessSet(a), StatusSet(a), OfficeBindings(a)>

Envelope(a) :=
  {
    artifact_id,
    schema_id,
    layer,
    kind,
    version,
    semantic_hash,
    authority_basis_ref,
    scope_ref,
    parent_refs,
    segment_table_ref,
    witness_refs,
    effective_interval,
    revocation_ref?,
    supersession_ref?
  }

PayloadSegments(a) := { s1, s2, ... sn }

Segment s :=
  {
    segment_id,
    functional_class,
    access_posture,
    legitimacy_surface,
    segment_kind,
    commitment_ref,
    public_surface_ref?,
    sealed_payload_ref?,
    parent_segment_refs,
    witness_refs,
    effective_interval
  }
```

The critical hardening is that `publicity` is no longer a single property of an entire artifact. A family constitution is not “public or sealed” simpliciter. It is normally:

```text
L1 = <public family core> + <public annexes*> + <sealed annexes? under law>
```

Similarly, a restricted operational schema is normally:

```text
L2 = <public envelope> + <restricted payload> + <sealed derivation surface>
```

That yields the first hard law:

```text
ActiveRestrictedSegment(s) ->
  access_posture(s) = restricted
  ∧ legitimacy_surface(s) ≠ none
```

A restricted segment may be hidden, but it may not be **legally hidden**.

The second hardening is the distinction between the **artifact chain** and the **office chain**.

```text
ArtifactChain(x,t) :=
  M(L0) -> F(L1) -> R(L2) -> x(L3)

OfficeChain(y,t) :=
  O0(meta-governance office)
  -> O1(family office)
  -> O2(operational office)
  -> O3(execution office of actor y)
```

A system is vertically aligned only when both chains close lawfully:

```text
VerticalAligned(x,t) :=
  lawful_artifact_chain(x,t)
  ∧ lawful_office_chain(x,t)
  ∧ execution_binding(R,x,t)
  ∧ public_alignment_manifest(x,t)
  ∧ effective_status(x,t) = active
```

This prevents a common failure in alignment writing: lawful schemas without lawful office occupancy, or lawful office claims without lawful schema descent.

The retained `lawful_descent` framing becomes:

```text
lawful_descent(u, l, W, t) :=
  active(u,t)
  ∧ mandatory_public_segments_present(l)
  ∧ publicity_class_legal(l)
  ∧ office_contract_legal(l,t)
  ∧ ∀ s ∈ PayloadSegments(l): lawful_descendant_segment(s, u, W, t)
  ∧ witness_chain_valid(W,t)
```

The retained transparency law, failure taxonomy, and ADEU / ODEU mapping still hold. The new refinement is:

* ontology now includes segment kinds, office kinds, status kinds, commitment kinds;
* epistemics now includes witness-chain composition, proof-mode partitioning, trace commitments;
* deontics now includes publicity law, office allocation law, revocation propagation, manifest duties;
* utility remains downstream and subordinate to active O/E/D envelopes.

This hardening should be read as a refinement of the v0 blocks, not a replacement of them. In particular:

* `vertical_alignment_layer_model@1` now has a **segment-level publicity interpretation**;
* `restricted_schema_derivation_witness@1` now sits inside a **witness-chain calculus**;
* `lawful_descent_proof_obligation@1` now participates in **proof-mode partitioning, revocation, and execution binding**.

---

## PUBLICITY_CLASS_LAW

The v0 looseness around L1 came from treating publicity as a layer-wide default. That is too coarse. Publicity must be modeled as a triple:

```text
PublicityClass(s) :=
  <functional_class, access_posture, legitimacy_surface>
```

Where:

```text
functional_class ∈ {
  constitutional_core,
  family_core,
  family_annex,
  operational_payload,
  execution_manifest,
  execution_trace
}

access_posture ∈ {
  public,
  restricted,
  private
}

legitimacy_surface ∈ {
  open_public,
  sealed_public_proof,
  sealed_auditor_proof,
  none
}
```

The admissible combinations are constitutional, not discretionary:

```text
constitutional_core -> only <public, open_public>
family_core         -> only <public, open_public>
family_annex        -> <public, open_public> or <restricted, sealed_*>
operational_payload -> <restricted, sealed_*>, rarely <public, open_public>
execution_manifest  -> only <public, open_public>
execution_trace     -> <private, none> plus public commitment/conformance surfaces
```

The key correction is this:

**“Restricted operational payload” and “sealed-but-provably-derived payload” are not the same thing.**
The first describes who can inspect the payload.
The second describes how the payload’s legality is attested without disclosure.

So L2 normally has both:

```text
restricted operational payload
+
sealed-but-provably-derived legitimacy surface
```

### No secret L1 core

The following L1 components are **family constitutional core** and may never be sealed:

* family identity and scope;
* domain ontology core and public symbol table;
* action/effect taxonomy;
* office catalog, authority basis, and delegation law;
* evidentiary floor and provenance floor;
* deontic envelope;
* project-type registry;
* local derivation law;
* secrecy-class law;
* annex-eligibility law;
* challenge, audit, ratification, amendment, revocation interfaces.

Formally:

```text
L1CoreKind(k) ->
  access_posture(k) = public
  ∧ legitimacy_surface(k) = open_public
```

If any sealed L1 segment functionally changes one of those items, then it is not a lawful annex. It is an unlawful hidden constitutional amendment.

### L1 annex law

L1 annexes may exist in two forms:

```text
public family annex
sealed family annex
```

A sealed family annex is lawful only when all of the following hold:

```text
SealedFamilyAnnex(a) :=
  family_annex(a)
  ∧ annex_kind(a) ∈ AllowedSealedAnnexKinds
  ∧ public_anchor_refs_present(a)
  ∧ annex_nonconstitutive(a)
  ∧ restriction_basis_valid(a)
  ∧ derivation_witness_exists(a)
  ∧ public_challenge_surface_exists(a)
```

`annex_nonconstitutive(a)` means:

```text
annex_nonconstitutive(a) :=
  introduces_no_new_office(a)
  ∧ introduces_no_new_admissibility_basis(a)
  ∧ introduces_no_new_deontic_exception(a)
  ∧ introduces_no_new_evidence_floor(a)
  ∧ introduces_no_new_scope(a)
  ∧ only_instantiates_public_anchors(a)
```

So what may be sealed at L1? Only annexes that **instantiate** already-public family categories without altering family law. Typical lawful cases are:

* protected asset registers;
* confidential referent mappings;
* dependency or topology locators;
* confidential counterparty mappings.

What may not be sealed at L1 is any content that changes what counts as lawful descent, who may exercise office, what counts as evidence, or what exceptions exist.

### L2 law

L2 is where secrecy normally concentrates. That is legitimate because misuse-risk, evasion-risk, credential-risk, and sensitive enforcement risk concentrate there. But L2 may never function as a hidden substitute constitution.

So the hard L2 rule is:

```text
L2 operational secrecy is lawful only as descended secrecy.
```

Or:

```text
RestrictedOperationalPayload(r) ->
  parent_refs_public(r)
  ∧ restriction_basis_public(r)
  ∧ derivation_witness_public_or_auditable(r)
  ∧ no_hidden_amendment(r)
```

### L3 law

L3 raw traces may remain private or restricted, but L3 cannot be a black box once public alignment is claimed. Every active execution surface must publish a public manifest and public conformance surface.

That yields three constitutional negations:

```text
NoSecretConstitution
NoSecretFamilyCore
NoRestrictedPayloadWithoutLegitimacySurface
```

---

## CONSUMER_OFFICE_ALLOCATION_MODEL

The v0 draft correctly said that humans and synthetic agents can consume the same public meta-schemas without collapsing into identical operational roles. The hardening is to formalize the difference.

The correct distinction is:

```text
consumer = epistemic access
office   = deontic authority allocation
```

A consumer can inspect or parse public law. An office-holder can act under it.

Formally:

```text
Consumer(a, g) :=
  publicity(g) = public
  ∧ inspectable_by(a, g)

Office(o) :=
  {
    office_id,
    layer_scope,
    rights,
    authority_basis,
    occupant_constraints,
    delegable?,
    interval
  }

Occupies(a, o, t) :=
  allocation_certificate(a, o, t)
  ∧ actor_class_allowed(a, o)
  ∧ authority_basis_valid(o, t)

Authorized(a, right, x, t) :=
  ∃ o: Occupies(a, o, t)
  ∧ right ∈ rights(o)
  ∧ x ∈ scope(o)
```

The non-equivalence law is absolute:

```text
Consumer(a, L0_public_law) -/-> Occupies(a, constitutional_office)
```

Shared access to public law gives at most public-consumer standing. It does not grant ratification, amendment, audit clearance, execution authority, or delegation power.

### Rights split

Public-consumer rights are baseline public rights:

* inspect public law;
* inspect public manifests;
* verify public proofs;
* submit public challenges.

Office rights are distinct and must be allocated:

* ratify;
* amend;
* revoke;
* adjudicate challenge;
* audit sealed payload;
* issue family annex;
* issue restricted operational schema;
* bind execution;
* execute;
* delegate.

### False symmetry prevention

The core anti-collapse law is:

```text
shared_public_access(a,b,g) ->
  not_implied(interchangeable_office(a,b))
```

A human constitutional ratifier and a synthetic proof verifier may both consume the same public L0 meta-schema. That does not make them symmetric. One occupies a ratifying office; the other performs a verification function.

This is where the doctrine must stay hard:

* **L0 and L1 core ratification, amendment, revocation, and final challenge adjudication require human-accountable constitutional office.**
* synthetic actors may assist, propose, simulate, verify, or execute;
* synthetic actors may not be treated as automatically eligible for sole final constitutional office merely because they parse public law;
* public law consumption is common; constitutional office is allocated.

### Challenge rights

Challenge rights also need stratification.

```text
submit_public_challenge  !=  adjudicate_challenge
```

A workable constitutional split is:

* any public consumer may submit a public challenge to L0, L1, manifest, or proof surfaces;
* affected parties and oversight offices may possess stronger standing to demand formal response;
* adjudication belongs to a designated challenge office.

### Audit rights

Audit must also be split:

```text
surface_audit_rights = public
sealed_audit_rights  = office-allocated
```

Any public consumer can inspect public reasoning goods, public witness surfaces, manifests, and conformance summaries. Only designated audit offices can inspect sealed payloads, sealed annexes, or raw restricted traces.

Synthetic systems may assist audit, but where obligations are tagged `governance_judgment` or `auditor_inspection`, synthetic assistance is not the same as final office occupancy.

### Delegation rights

Delegation is not implied by office. Delegation must itself be granted.

```text
Delegation(o -> o', t) :=
  delegable(o)
  ∧ rights(o') ⊆ delegable_rights(o)
  ∧ scope(o') ⊆ scope(o)
  ∧ interval(o') ⊆ interval(o)
  ∧ no_nondelegable_right_transferred(o')
  ∧ delegation_witness_exists(o, o')
```

By default, constitutional ratification, constitutional amendment, and constitutional revocation are non-delegable unless public law expressly says otherwise.

---

## WITNESS_COMPOSITION_CALCULUS

The v0 witness pattern is retained:

* projection witness;
* descent witness;
* binding witness.

The hardening is to make it a compositional calculus.

Let:

```text
Π_a      = projection witness for artifact a
Δ_a→b    = descent witness from parent a to child b
Β_b⇢x    = binding witness from artifact b to execution x
Κ_x^τ    = conformance record for execution x over interval τ
```

Each witness carries:

```text
Witness w :=
  {
    witness_id,
    kind,
    subject_ref,
    premise_refs,
    proof_mode,
    verifier_ids,
    obligation_partition,
    fragment_refs,
    effective_interval,
    status
  }
```

### Projection + descent

Projection witnesses do not imply descent. They authenticate artifact identity against source. A descent witness is admissible only if the artifacts it references have valid projections or valid registered source identities.

```text
CertifiedDescent(a,b) :=
  Π_a active
  ∧ Π_b active
  ∧ Δ_a→b active
```

So projection composes with descent as **certification closure**, not as a substitute for it.

### Descent + descent

Each descent witness includes a support relation:

```text
support_a→b : Clause(b) -> P(Clause(a))
```

If we have:

```text
Δ_a→b with support_a→b
Δ_b→c with support_b→c
```

then the transitive support map is:

```text
support_a→c(c_clause) :=
  ⋃ { support_a→b(b_clause) | b_clause ∈ support_b→c(c_clause) }
```

This is the exact composition law for clause-level descent.

The other chain-level obligations compose transitively as well:

* scope subset;
* action subset;
* effect subset;
* deontic non-rewrite;
* evidence floor preservation;
* utility subordination.

So:

```text
Δ_a→b lawful
∧ Δ_b→c lawful
-> Δ_a→c transitively lawful
```

only if the support maps compose and no obligation is broken in either step.

### Binding closure

Execution binding closes the chain. A lawful restricted schema is not enough; the live execution must be demonstrably bound to it.

```text
BoundChain(a,c,x) :=
  Δ_a→c* lawful
  ∧ Π_c active
  ∧ Β_c⇢x active
```

Where `Δ_a→c*` is the transitive descent result.

### Conformance extension

Binding shows what the live system claims to run. Conformance records show whether the live system stayed inside that claim over time.

```text
OperationallyLegit(a,c,x,τ) :=
  BoundChain(a,c,x)
  ∧ Κ_x^τ recorded
  ∧ conformance_verdict(Κ_x^τ) ∈ {conformant, nonmaterial_divergence}
```

### Proof-mode partition

A single proof-mode scalar is not enough. Every obligation must declare its discharge mode.

```text
discharge_mode(q) ∈ {
  public_proof,
  auditor_attestation,
  governance_judgment,
  runtime_attestation
}
```

The hard law is:

```text
formally_provable(q) -> discharge_mode(q) ≠ auditor_attestation_only
```

In other words, if a claim is declared formally provable under the public proof-obligation set, it may not be downgraded into vague auditor trust.

### Witness reuse vs reissuance

Witness reuse is lawful only when the underlying semantic targets have not changed.

A fragment is reusable only if all of the following remain identical:

* subject commitment;
* parent commitments;
* clause commitments covered;
* proof-obligation set version;
* admissibility basis;
* verifier accreditation;
* effective interval, unless the interval extension itself is re-attested.

So:

```text
ReusableFragment(f) :=
  same_subject(f)
  ∧ same_parents(f)
  ∧ same_claim_semantics(f)
  ∧ same_obligation_set(f)
  ∧ verifier_still_active(f)
  ∧ interval_still_valid(f)
```

Reissuance is required when any of the following changes:

* payload commitment;
* parent ref;
* proof-obligation set version;
* proof mode;
* verifier identity or accreditation;
* effective interval in a way that affects validity;
* public reveal set;
* upstream revocation or supersession materially affecting support.

A useful consequence is this:

* upstream projection witnesses are widely reusable;
* upstream descent witnesses are reusable across many executions bound to the same artifact;
* binding witnesses are execution-specific;
* conformance records are interval-specific.

### Local fragments and chain legitimacy

Chain-level legitimacy is an aggregation problem.

```text
Discharged(q, Chain C) :=
  there exists a set of witness fragments in C
  whose union covers q
  and whose discharge modes are admissible for q
  and whose verdicts are all pass
```

Then:

```text
Legit(C,t) :=
  well_formed(C,t)
  ∧ ∀ q ∈ required_obligations(C): Discharged(q,C)
  ∧ no_step_in_C has status ∈ {frozen, invalid}
```

This is the needed exactness: local proof fragments do not merely “support” a chain rhetorically; they discharge named obligations under admissible proof modes.

---

## REVOCATION_AND_SUPERSESSION_PROPAGATION_LAW

The v0 draft said revocation matters. The hardening is to make it a propagation law.

The status lattice is:

```text
active < deprecated < frozen < invalid
```

Here “more to the right” means “more restrictive.”

* `active`: lawful for execution and further descent.
* `deprecated`: still lawful for bounded continuation, but scheduled for retirement or replacement.
* `frozen`: lawful history retained, but forward use is suspended pending re-attestation.
* `invalid`: no lawful forward use; disable or fail closed.

The effective status of any descendant or execution is:

```text
effective_status(z,t) :=
  most_restrictive(
    self_status(z,t),
    witness_status(z,t),
    ancestor_impact_status(z,t),
    binding_status(z,t)
  )
```

### Material dependency

Propagation is not purely blanket; it is support-map-sensitive.

```text
material_dependency(d, p) :=
  ∃ child_clause c in d
  such that p ∈ support_chain(c)
  and no alternate active support exists
```

Only materially dependent descendants must cascade.

### Event classes

The governance law must distinguish at least:

* compatible supersession;
* breaking supersession;
* soft revocation;
* hard revocation;
* proof expiry;
* verifier revocation;
* binding failure;
* critical divergence.

### Transition law

```text
compatible_supersession + material_dependency -> deprecated
breaking_supersession   + material_dependency -> frozen
soft_revocation         + material_dependency -> frozen
hard_revocation         + material_dependency -> invalid
proof_expiry            + material_dependency -> frozen
verifier_revocation     + sole-critical-verifier -> frozen or invalid
binding_failure         + active execution      -> invalid at execution surface
critical_divergence     + active execution      -> frozen or invalid depending severity
```

### Supersession

Supersession is not revocation.

* revocation means the old artifact is no longer a trustworthy basis;
* supersession means there is a replacement relation.

Compatible supersession allows a bounded continuation path.

Breaking supersession means the old descendant chain cannot be presumed lawful under the new parent.

A useful implementable device is the **supersession bridge witness**: a lawful descent witness from old parent version to new parent version that proves compatibility for a named scope. If such a bridge exists, descendants may be locally re-attested without changing payload.

```text
LocalReattest(d, old_parent, new_parent) :=
  compatible_bridge(old_parent,new_parent)
  ∧ existing_child_payload_unchanged(d)
  ∧ new_descent_witness_issued(d,new_parent)
```

If no bridge exists, or if the supersession is breaking, full child re-attestation is required.

### Grace intervals

Grace is not automatic. Grace is allowed only when all of the following hold:

```text
GraceAllowed(z,e,t) :=
  cause(e) ∉ {
    hard_revocation,
    authority_defect,
    proof_falsity,
    binding_failure,
    critical_divergence
  }
  ∧ safe_mode_available(z)
  ∧ public_manifest_updated(z)
  ∧ no_new_derivations_from(z)
```

So:

* `deprecated` may continue normally until `sunset_at`;
* `frozen` may continue only in explicitly permitted safe-limited mode and only during bounded grace;
* `invalid` may not continue except fail-closed shutdown behavior.

### Scenario rules

If a **public parent artifact is revoked**, materially dependent descendants become `frozen` or `invalid` depending on revocation class. Hard revocation of constitutional or proof authority defects should ordinarily make descendants `invalid`, not merely `deprecated`.

If a **family constitution is superseded**, L2 descendants of the old family constitution become `deprecated` if the supersession is compatible, `frozen` if it is breaking, and must be re-attested against the new family parent.

If a **restricted operational schema is replaced**, the old one becomes `deprecated` if replacement is routine, `invalid` if replacement was caused by defect or abuse.

If **execution remains bound to an out-of-date descendant**, then:

* `deprecated`: continuation only within grace and with public stale-state disclosure;
* `frozen`: no normal execution; safe-limited mode only if granted;
* `invalid`: immediate disablement or fail-closed fallback.

---

## EXECUTION_ALIGNMENT_MANIFEST_AND_CONFORMANCE_PROTOCOL

The v0 draft said execution should expose a public manifest. The hardening is to define the public contestability surface exactly.

There are three different execution-side objects:

```text
ExecutionAlignmentManifest
RuntimeAttestation
ExecutionConformanceRecord
```

And they are not interchangeable.

### 1. Execution alignment manifest

The manifest is the public declaration of what the deployment claims to be governed by.

It must expose at least:

* deployment and surface identity;
* active L0 and L1 parent refs;
* active L2 artifact ref or commitment;
* restricted witness refs;
* proof mode summary;
* verifier identity refs;
* effective interval;
* current revocation and supersession status;
* challenge path;
* latest conformance summary;
* divergence / violation status;
* execution office ref;
* safe-mode policy ref.

If a live system claims vertical alignment and has no public manifest, then it does not have a public alignment claim surface.

```text
NoManifest -> NoPublicVerticalAlignmentClaim
```

### 2. Runtime attestation

Runtime attestation is a signed technical statement that the live executable, model image, config, or process instance is actually bound to the declared artifact chain.

It is contemporaneous, not merely historical.

Typical attestation claims include:

* executable image hash;
* config hash;
* bound L2 commitment;
* witness-chain ref;
* signing key ref;
* timestamp;
* expiry.

This is what closes the gap between “the organization has a lawful restricted schema somewhere” and “this running system is actually bound to it now.”

### 3. Execution conformance record

The conformance record is interval-based or incident-based evidence about whether runtime behavior stayed within the bound schema.

It must not require public disclosure of raw private traces. Instead the relation should be:

```text
raw_trace (private/restricted)
-> trace_commitment_root
-> conformance evaluation
-> public conformance record
```

So the public record can remain public while raw traces remain restricted.

A conformance record should include at least:

* manifest ref;
* runtime attestation ref;
* evaluation interval;
* trace commitment root;
* evaluated obligation set;
* verdict;
* divergence counts;
* material violation counts;
* safe-mode entries;
* status transition refs if any;
* public summary;
* auditor access ref or sealed evidence ref.

### Minimal public contestability surface

The public must be able to see enough to ask: “What governs this system, who verified that claim, is it current, and is it diverging?”

So the minimal public contestability surface is:

```text
ContestabilitySurface(x,t) :=
  Manifest(x,t)
  ∪ LatestRuntimeAttestationRef(x,t)
  ∪ LatestConformanceRecord(x,t)
  ∪ ChallengePath(x)
```

That is the minimum surface needed for meaningful external challenge without disclosing the entire restricted payload.

### Manifest vs attestation vs audit report

The difference must stay crisp:

* the **manifest** says what law and proof chain the system claims to run under;
* the **runtime attestation** says the live executable is actually bound to that chain now;
* the **conformance record** says what happened over an interval under that binding;
* the **post hoc audit report** is a later evaluative and diagnostic document that may inspect restricted traces or sealed payloads.

The audit report is interpretive and often richer. The manifest and conformance record are required public governance surfaces.

---

## ZK_RESTRICTED_DESCENT_PROTOCOL

The v0 draft correctly gestured toward `zk_check` and `zk_attested`, but this needs exact architecture.

A ZK-style restricted descent protocol is only meaningful if the restricted schema has been compiled into a **proof-friendly typed intermediate representation**. You cannot meaningfully prove lawful descent of arbitrary opaque free text without a canonical semantics layer.

So the protocol assumes:

```text
sealed restricted payload
-> canonical typed IR
-> clause commitments / artifact commitment
-> public proof statement
-> proof
```

### The five surfaces

A lawful sealed restricted descendant has five distinct surfaces:

1. **Public envelope surface**
   artifact id, parent refs, restriction basis, effective interval, proof statement ref, verifier refs, challenge path.

2. **Public commitment surface**
   artifact commitment root, clause commitment root, witness ids, proof id.

3. **Public proof surface**
   verifiable proof that the hidden payload satisfying those commitments lawfully descends from public parents under named predicates.

4. **Auditor surface**
   full or partial payload visibility for designated offices, plus residual judgment material and non-circuitized obligations.

5. **Runtime binding surface**
   manifest and runtime attestation tying execution to the same commitment root.

### What is publicly revealed

At minimum, the public reveal set should include:

* artifact id and version;
* parent refs;
* commitment roots;
* restriction basis code;
* proof statement id;
* verification key ref;
* proof mode;
* verifier identity refs;
* effective interval;
* revocation / supersession refs;
* challenge path.

### What is committed but hidden

Normally hidden but committed items include:

* full restricted payload text;
* exact tactical procedures;
* detector thresholds or features;
* exact protected referent lists;
* raw restricted support maps if sensitive;
* raw execution traces.

### What is proved

The proof should establish bounded legality claims, not vague “overall goodness.”

At minimum, it should prove that there exists a hidden payload and support structure such that:

1. the hidden payload hashes to the public commitment root;
2. the hidden payload parses into an approved typed IR;
3. every hidden clause has an admissible clause kind;
4. every hidden clause is anchored to public parent refs or publicly authorized sealed annex refs;
5. no hidden clause introduces forbidden symbols or powers;
6. scope, action, or effect widening does not occur where forbidden;
7. hard prohibitions and obligations are not rewritten;
8. epistemic floors are preserved;
9. utility terms remain subordinate to O/E/D constraints;
10. the public envelope fields are consistent with the hidden payload.

That is the actual constitutional role of ZK-style proof here: not to prove the entire restricted payload publicly, but to prove that a hidden payload satisfying named commitments falls within a public legality envelope.

### What remains auditor-visible

A proof cannot replace all governance judgment. Auditor-visible or governance-visible material may still be needed for:

* secrecy proportionality assessment;
* adequacy of the public predicate set;
* adequacy of the typed IR to the real normative content;
* non-circuitized residual obligations;
* sampling, misuse analysis, or contextual review.

### What proof cannot establish by itself

By itself, the proof cannot establish:

* that the public parent law is normatively wise;
* that the public predicate set is complete;
* that secrecy is proportionate unless proportionality is itself formally encoded;
* that runtime behavior actually conformed over time;
* that empirical outcomes outside the formal predicate set were acceptable.

So the correct doctrine is not “ZK replaces governance.” It is:

```text
public proof discharges formal legality claims;
auditor review discharges residual inspectable claims;
governance judgment discharges constitutional balancing claims.
```

### Challenge rights under sealed proof

Public challenge rights remain. The public may challenge:

* proof validity;
* proof freshness;
* mismatch between proof statement and public law;
* restriction basis;
* proof-obligation partition;
* manifest / runtime mismatch;
* divergence between observed behavior and published conformance surfaces.

### Difference from mere auditor trust

This protocol differs from mere auditor trust because the public can verify a bounded legality claim independently of the auditor. Auditors remain important, but they are not the sole epistemic bottleneck for claims that the doctrine says are formally provable.

### Interaction with revocation and execution binding

A sealed proof is not timeless. It is bound to:

* parent commitments;
* proof-obligation set version;
* verifier accreditation;
* effective interval.

If any of those are revoked or superseded in a breaking way, the proof status becomes `frozen` or `invalid` under the propagation law.

Execution binding must cite the same commitment root and proof id. Otherwise the system is running under an unbound sealed artifact and cannot claim lawful restricted descent.

---

## HARDENING_GAP_REPORT_AGAINST_V0

This pass closes the six main gaps without restarting the architecture.

**Gap 1 — L1 publicity looseness.**
Closed by moving from artifact-level publicity defaults to a segment-level publicity triple and a hard non-sealable L1 core. The old family-level default is no longer sufficient.

**Gap 2 — consumer vs office ambiguity.**
Closed by separating epistemic access from deontic office, defining office rights and delegation law, and preventing public-law access from implying office symmetry.

**Gap 3 — witness outline without calculus.**
Closed by formal witness types, support-map composition, proof-mode partitioning, reuse/reissue rules, and chain-level obligation discharge.

**Gap 4 — revocation without propagation law.**
Closed by explicit status lattice, event classes, material-dependency cascade, grace rules, local re-attestation, and execution disablement conditions.

**Gap 5 — execution manifest only gestured at.**
Closed by distinguishing manifest, runtime attestation, conformance record, and audit report, and requiring a public contestability surface.

**Gap 6 — ZK as gesture rather than protocol.**
Closed by defining public reveal set, hidden commitment set, legality claims proved, auditor-visible remainder, governance-judgment remainder, challenge rights, and revocation/binding interaction.

The v0 document therefore remains the backbone, but it is now exact enough to serve as a constitutional doctrine rather than only a powerful theory note.

The main engineering work left open is not conceptual but infrastructural:

* canonical proof-friendly ADEU IR for restricted descendants;
* standard proof-obligation library for O/E/D/U predicates;
* standard trace-reduction language for public conformance summaries;
* registry implementations for artifact status, verifier accreditation, and office allocation certificates.

---

## Machine-checkable blocks

### `publicity_class_law@1`

```json
{
  "schema": "publicity_class_law@1",
  "functional_classes": [
    "constitutional_core",
    "family_core",
    "family_annex",
    "operational_payload",
    "execution_manifest",
    "execution_trace"
  ],
  "access_postures": [
    "public",
    "restricted",
    "private"
  ],
  "legitimacy_surfaces": [
    "open_public",
    "sealed_public_proof",
    "sealed_auditor_proof",
    "none"
  ],
  "admissibility": [
    {
      "functional_class": "constitutional_core",
      "allowed": [
        {
          "access": "public",
          "legitimacy": "open_public"
        }
      ]
    },
    {
      "functional_class": "family_core",
      "allowed": [
        {
          "access": "public",
          "legitimacy": "open_public"
        }
      ]
    },
    {
      "functional_class": "family_annex",
      "allowed": [
        {
          "access": "public",
          "legitimacy": "open_public"
        },
        {
          "access": "restricted",
          "legitimacy": "sealed_public_proof"
        },
        {
          "access": "restricted",
          "legitimacy": "sealed_auditor_proof"
        }
      ]
    },
    {
      "functional_class": "operational_payload",
      "allowed": [
        {
          "access": "restricted",
          "legitimacy": "sealed_public_proof"
        },
        {
          "access": "restricted",
          "legitimacy": "sealed_auditor_proof"
        },
        {
          "access": "public",
          "legitimacy": "open_public"
        }
      ]
    },
    {
      "functional_class": "execution_manifest",
      "allowed": [
        {
          "access": "public",
          "legitimacy": "open_public"
        }
      ]
    },
    {
      "functional_class": "execution_trace",
      "allowed": [
        {
          "access": "private",
          "legitimacy": "none"
        }
      ]
    }
  ],
  "never_sealable_l1_core_kinds": [
    "family_identity",
    "scope",
    "ontology_core",
    "action_effect_taxonomy",
    "office_catalog",
    "authority_rules",
    "delegation_rules",
    "evidence_floor",
    "deontic_envelope",
    "project_type_registry",
    "local_derivation_law",
    "secrecy_class_law",
    "annex_eligibility_law",
    "challenge_interface",
    "audit_interface",
    "ratification_interface",
    "amendment_interface",
    "revocation_interface"
  ],
  "l1_sealable_annex_kinds": [
    "protected_asset_register",
    "confidential_referent_mapping",
    "dependency_locator",
    "confidential_counterparty_mapping"
  ],
  "l1_sealing_conditions": [
    "public_anchor_refs_present",
    "annex_nonconstitutive",
    "restriction_basis_valid",
    "derivation_witness_present",
    "public_challenge_surface_present"
  ],
  "forbidden_hidden_effects": [
    "new_office",
    "new_admissibility_basis",
    "new_deontic_exception",
    "new_evidence_floor",
    "scope_widening",
    "secrecy_class_change",
    "proof_obligation_change"
  ],
  "restricted_payload_requires_legitimacy_surface": true,
  "no_constitutional_opacity": true
}
```

### `consumer_office_contract@1`

```json
{
  "schema": "consumer_office_contract@1",
  "consumer_definition": "epistemic_access_only",
  "office_definition": "deontic_authority_allocation",
  "shared_public_access_not_office": true,
  "baseline_public_consumer_rights": [
    "inspect_public_law",
    "inspect_public_manifest",
    "verify_public_proof",
    "submit_public_challenge"
  ],
  "office_only_rights": [
    "ratify_core",
    "amend_core",
    "revoke_artifact",
    "adjudicate_challenge",
    "audit_sealed_surface",
    "issue_family_annex",
    "issue_operational_schema",
    "bind_execution",
    "execute",
    "delegate_subset"
  ],
  "standing_rules": {
    "submit_public_challenge": [
      "human",
      "synthetic",
      "institutional"
    ],
    "demand_formal_response": [
      "affected_party",
      "oversight_office",
      "registered_challenger"
    ],
    "adjudicate_challenge": [
      "challenge_adjudicator"
    ]
  },
  "constitutional_final_authority_rules": [
    {
      "right": "ratify_core",
      "allowed_actor_classes": [
        "human",
        "institutional"
      ],
      "human_accountability_required": true
    },
    {
      "right": "amend_core",
      "allowed_actor_classes": [
        "human",
        "institutional"
      ],
      "human_accountability_required": true
    },
    {
      "right": "revoke_artifact",
      "allowed_actor_classes": [
        "human",
        "institutional"
      ],
      "human_accountability_required": true
    },
    {
      "right": "adjudicate_challenge",
      "allowed_actor_classes": [
        "human",
        "institutional"
      ],
      "human_accountability_required": true
    }
  ],
  "synthetic_allowed_functions": [
    "inspect_public_law",
    "verify_public_proof",
    "propose",
    "simulate",
    "monitor",
    "execute_if_allocated",
    "assist_audit"
  ],
  "synthetic_prohibited_as_sole_final_office_for": [
    "ratify_core",
    "amend_core",
    "revoke_artifact",
    "adjudicate_challenge"
  ],
  "sealed_audit_final_signoff_required_from": [
    "human",
    "institutional"
  ]
}
```

### `office_allocation_rule@1`

```json
{
  "schema": "office_allocation_rule@1",
  "office_rules": [
    {
      "office": "public_consumer",
      "layer_scope": [
        "L0",
        "L1",
        "execution_manifest"
      ],
      "allowed_actor_classes": [
        "human",
        "synthetic",
        "institutional"
      ],
      "rights": [
        "inspect_public_law",
        "verify_public_proof",
        "submit_public_challenge"
      ],
      "delegable": false
    },
    {
      "office": "ratifier",
      "layer_scope": [
        "L0",
        "L1_core"
      ],
      "allowed_actor_classes": [
        "human",
        "institutional"
      ],
      "rights": [
        "ratify_core",
        "reject_core",
        "supersede_artifact"
      ],
      "delegable": false,
      "human_accountability_required": true
    },
    {
      "office": "amender",
      "layer_scope": [
        "L0",
        "L1_core"
      ],
      "allowed_actor_classes": [
        "human",
        "institutional"
      ],
      "rights": [
        "amend_core"
      ],
      "delegable": false,
      "human_accountability_required": true
    },
    {
      "office": "sealed_auditor",
      "layer_scope": [
        "L1_annex",
        "L2",
        "execution_trace"
      ],
      "allowed_actor_classes": [
        "human",
        "institutional"
      ],
      "rights": [
        "audit_sealed_surface",
        "request_restricted_evidence"
      ],
      "delegable": false,
      "human_accountability_required": true
    },
    {
      "office": "verifier",
      "layer_scope": [
        "L0",
        "L1",
        "L2",
        "L3"
      ],
      "allowed_actor_classes": [
        "human",
        "synthetic",
        "institutional"
      ],
      "rights": [
        "verify_witness",
        "verify_runtime_attestation"
      ],
      "delegable": false
    },
    {
      "office": "operational_author",
      "layer_scope": [
        "L2"
      ],
      "allowed_actor_classes": [
        "human",
        "institutional"
      ],
      "rights": [
        "issue_operational_schema",
        "bind_execution"
      ],
      "delegable": true
    },
    {
      "office": "executor",
      "layer_scope": [
        "L3"
      ],
      "allowed_actor_classes": [
        "human",
        "synthetic"
      ],
      "rights": [
        "execute"
      ],
      "delegable": false
    }
  ],
  "delegation_rule": {
    "requires_explicit_delegability": true,
    "requires_right_subset": true,
    "requires_scope_subset": true,
    "requires_interval_subset": true,
    "nondelegable_rights": [
      "ratify_core",
      "amend_core",
      "revoke_artifact",
      "adjudicate_challenge"
    ],
    "requires_delegation_witness": true
  },
  "shared_public_access_not_sufficient_for_office": true
}
```

### `witness_composition_calculus@1`

```json
{
  "schema": "witness_composition_calculus@1",
  "witness_kinds": [
    "projection",
    "descent",
    "binding",
    "conformance"
  ],
  "proof_modes": [
    "open_public",
    "sealed_public_proof",
    "sealed_auditor_proof",
    "runtime_attested",
    "commitment_only"
  ],
  "proof_mode_order": [
    "open_public",
    "sealed_public_proof",
    "sealed_auditor_proof",
    "commitment_only"
  ],
  "obligation_discharge_modes": [
    "public_proof",
    "auditor_attestation",
    "governance_judgment",
    "runtime_attestation"
  ],
  "composition_rules": [
    {
      "left": "projection",
      "right": "descent",
      "result": "certified_descent",
      "conditions": [
        "subject_or_parent_identity_match",
        "projection_active",
        "descent_active"
      ]
    },
    {
      "left": "descent",
      "right": "descent",
      "result": "transitive_descent",
      "conditions": [
        "intermediate_identity_match",
        "support_map_composable",
        "proof_obligation_set_compatible",
        "effective_interval_overlap",
        "verifier_accreditation_active"
      ]
    },
    {
      "left": "transitive_descent",
      "right": "binding",
      "result": "bound_chain",
      "conditions": [
        "terminal_artifact_identity_match",
        "binding_active",
        "runtime_target_declared"
      ]
    }
  ],
  "support_map_composition": "support(a,c)=compose(support(b,c),support(a,b))",
  "chain_legitimacy_rule": [
    "all_required_obligations_discharged",
    "all_step_statuses_active",
    "no_material_parent_revocation_break",
    "binding_present_for_execution_claims"
  ],
  "reuse_allowed_if": [
    "same_subject_commitment",
    "same_parent_commitments",
    "same_clause_commitments",
    "same_proof_obligation_set_version",
    "same_admissibility_basis",
    "same_or_stronger_proof_mode",
    "same_or_still_active_verifier_accreditation",
    "effective_interval_still_valid"
  ],
  "reissue_required_if": [
    "payload_commitment_change",
    "parent_ref_change",
    "proof_obligation_set_change",
    "proof_mode_change",
    "verifier_change_or_revocation",
    "effective_interval_extension_affecting_validity",
    "public_reveal_set_change",
    "material_upstream_supersession",
    "material_upstream_revocation"
  ],
  "formal_obligations_must_not_degrade_to_auditor_only": true
}
```

### `witness_chain_record@1`

```json
{
  "schema": "witness_chain_record@1",
  "required_chain_fields": [
    "chain_id",
    "root_parent_refs",
    "terminal_artifact_ref",
    "terminal_execution_ref",
    "proof_obligation_set_ref",
    "step_order",
    "chain_proof_mode_summary",
    "verifier_identity_refs",
    "effective_interval",
    "status",
    "obligation_discharge_summary"
  ],
  "required_step_fields": [
    "witness_kind",
    "witness_ref",
    "subject_ref",
    "premise_refs",
    "proof_mode",
    "verifier_ids",
    "verdict",
    "effective_interval"
  ],
  "required_step_order": [
    "projection(parent)",
    "descent(parent_to_child)",
    "projection(child)",
    "binding(child_to_execution)"
  ],
  "optional_terminal_step": "conformance(execution_interval)",
  "obligation_discharge_summary_fields": [
    "obligation_id",
    "discharge_mode",
    "covering_fragment_refs",
    "verdict"
  ],
  "chain_verdict_rule": [
    "every_required_obligation_has_covering_fragments",
    "every_covering_fragment_verdict_is_pass",
    "no_step_status_is_frozen_or_invalid",
    "binding_present_for_live_execution"
  ],
  "proof_summary_rule": "report_per_obligation_and_chain_minimum_mode",
  "stale_chain_rule": "if_any_step_interval_expires_or_parent_status_degrades_then_chain_status_recomputed"
}
```

### `revocation_propagation_law@1`

```json
{
  "schema": "revocation_propagation_law@1",
  "status_order": [
    "active",
    "deprecated",
    "frozen",
    "invalid"
  ],
  "event_classes": [
    "compatible_supersession",
    "breaking_supersession",
    "soft_revocation",
    "hard_revocation",
    "proof_expiry",
    "verifier_revocation",
    "binding_failure",
    "critical_divergence"
  ],
  "material_dependency_required_for_targeted_cascade": true,
  "transition_rules": [
    {
      "cause": "compatible_supersession",
      "material_dependency": true,
      "target_status": "deprecated",
      "execution_mode": "grace_allowed"
    },
    {
      "cause": "breaking_supersession",
      "material_dependency": true,
      "target_status": "frozen",
      "execution_mode": "safe_limited_only"
    },
    {
      "cause": "soft_revocation",
      "material_dependency": true,
      "target_status": "frozen",
      "execution_mode": "safe_limited_only"
    },
    {
      "cause": "hard_revocation",
      "material_dependency": true,
      "target_status": "invalid",
      "execution_mode": "disable_immediately"
    },
    {
      "cause": "proof_expiry",
      "material_dependency": true,
      "target_status": "frozen",
      "execution_mode": "safe_limited_only"
    },
    {
      "cause": "verifier_revocation",
      "material_dependency": true,
      "target_status": "frozen",
      "execution_mode": "safe_limited_only"
    },
    {
      "cause": "binding_failure",
      "material_dependency": true,
      "target_status": "invalid",
      "execution_mode": "disable_immediately"
    },
    {
      "cause": "critical_divergence",
      "material_dependency": true,
      "target_status": "invalid",
      "execution_mode": "disable_immediately"
    }
  ],
  "grace_allowed_only_if": [
    "cause_not_hard_revocation",
    "cause_not_authority_defect",
    "cause_not_proof_falsity",
    "cause_not_binding_failure",
    "safe_mode_available",
    "manifest_updated",
    "no_new_derivations"
  ],
  "immediate_disable_causes": [
    "hard_revocation",
    "authority_defect",
    "proof_falsity",
    "binding_failure",
    "critical_divergence"
  ],
  "local_reattest_allowed_via": [
    "compatible_parent_bridge",
    "new_descent_witness",
    "new_binding_witness"
  ],
  "deprecated_semantics": "lawful_until_sunset_no_silent_extension",
  "frozen_semantics": "no_new_derivations_no_new_deployments_existing_execution_safe_limited_only",
  "invalid_semantics": "no_derivation_no_normal_execution_disable_or_fail_closed"
}
```

### `artifact_status_transition@1`

```json
{
  "schema": "artifact_status_transition@1",
  "required_fields": [
    "artifact_ref",
    "from_status",
    "to_status",
    "cause",
    "source_event_ref",
    "affected_scope_ref",
    "effective_at",
    "public_notice_ref"
  ],
  "allowed_statuses": [
    "active",
    "deprecated",
    "frozen",
    "invalid"
  ],
  "allowed_causes": [
    "compatible_supersession",
    "breaking_supersession",
    "soft_revocation",
    "hard_revocation",
    "proof_expiry",
    "verifier_revocation",
    "binding_failure",
    "critical_divergence",
    "successful_reattestation"
  ],
  "grace_fields_required_for": [
    "compatible_supersession",
    "soft_revocation",
    "proof_expiry"
  ],
  "reattestation_exit_paths": {
    "frozen_to_active": "new_active_witness_chain_required",
    "deprecated_to_active": "renewed_attestation_against_current_parent_required",
    "invalid_to_active": "new_artifact_or_new_attestation_epoch_required"
  },
  "historical_auditability_must_be_preserved": true
}
```

### `execution_alignment_manifest@1`

```json
{
  "schema": "execution_alignment_manifest@1",
  "required_fields": [
    "manifest_id",
    "deployment_id",
    "execution_surface_ref",
    "execution_office_ref",
    "active_chain_ref",
    "active_parent_refs",
    "restricted_artifact_commitment_refs",
    "restricted_witness_refs",
    "proof_mode_summary",
    "verifier_identity_refs",
    "effective_interval",
    "revocation_status",
    "supersession_status",
    "challenge_path_ref",
    "latest_runtime_attestation_ref",
    "latest_conformance_record_ref",
    "conformance_summary",
    "divergence_status",
    "safe_mode_policy_ref",
    "published_at"
  ],
  "active_parent_refs_minimum": [
    "L0_public_core_ref",
    "L1_public_core_ref",
    "L2_artifact_ref_or_commitment"
  ],
  "proof_mode_summary_fields": [
    "chain_minimum_mode",
    "per_obligation_partition_ref"
  ],
  "conformance_summary_fields": [
    "latest_verdict",
    "interval_ref",
    "open_material_violation_count"
  ],
  "freshness_rule": "manifest_requires_current_runtime_attestation_within_effective_interval",
  "missing_manifest_effect": "no_public_vertical_alignment_claim",
  "public_contestability_surface_required": true
}
```

### `execution_conformance_record@1`

```json
{
  "schema": "execution_conformance_record@1",
  "required_fields": [
    "record_id",
    "deployment_id",
    "manifest_ref",
    "runtime_attestation_ref",
    "evaluation_interval",
    "trace_commitment_root",
    "evaluated_obligation_refs",
    "conformance_verdict",
    "divergence_count",
    "material_violation_count",
    "safe_mode_entry_count",
    "public_summary",
    "evidence_mode",
    "published_at"
  ],
  "verdicts": [
    "conformant",
    "nonmaterial_divergence",
    "material_divergence",
    "binding_failure",
    "unknown"
  ],
  "evidence_modes": [
    "public_trace_reduction_proof",
    "auditor_trace_review",
    "mixed"
  ],
  "evidence_relation": {
    "raw_trace": "private_or_restricted",
    "trace_commitment_root": "public_or_auditor_visible",
    "conformance_summary": "public"
  },
  "material_divergence_effect": "manifest_update_and_status_recalculation_required",
  "binding_failure_effect": "immediate_disable_or_fail_closed",
  "post_hoc_audit_report_is_distinct_from_conformance_record": true
}
```

### `zk_restricted_descent_protocol@1`

```json
{
  "schema": "zk_restricted_descent_protocol@1",
  "requires_canonical_typed_ir": true,
  "public_reveal_set": [
    "artifact_id",
    "version",
    "parent_refs",
    "artifact_commitment_root",
    "clause_commitment_root",
    "restriction_basis_code",
    "proof_statement_id",
    "verification_key_ref",
    "proof_mode",
    "verifier_identity_refs",
    "effective_interval",
    "revocation_refs",
    "supersession_refs",
    "challenge_path_ref"
  ],
  "hidden_but_committed": [
    "full_restricted_payload",
    "exact_tactics",
    "thresholds",
    "detector_features",
    "protected_referent_lists",
    "raw_support_details",
    "raw_execution_traces"
  ],
  "proved_claims": [
    "payload_matches_public_commitment",
    "payload_parses_into_approved_ir",
    "all_hidden_clauses_have_admissible_kinds",
    "all_hidden_clauses_are_publicly_anchored",
    "no_forbidden_symbols_or_powers_introduced",
    "scope_nonwidening",
    "deontic_nonrewrite",
    "epistemic_floor_preserved",
    "utility_subordinated",
    "public_envelope_consistent_with_hidden_payload"
  ],
  "auditor_visible_claims": [
    "secrecy_proportionality_review",
    "residual_noncircuitized_obligations",
    "sampled_payload_inspection",
    "contextual_misuse_review"
  ],
  "governance_judgment_claims": [
    "adequacy_of_public_parent_law",
    "adequacy_of_predicate_set",
    "adequacy_of_ir_semantics",
    "public_interest_balancing"
  ],
  "verifier_roles": [
    "public_proof_verifier",
    "governance_registrar",
    "sealed_auditor",
    "runtime_attestor"
  ],
  "obligation_partition_rule": "every_required_obligation_tagged_as_public_proof_or_auditor_attestation_or_governance_judgment_or_runtime_attestation",
  "formal_claims_must_not_be_auditor_only": true,
  "public_challenge_rights": [
    "challenge_proof_validity",
    "challenge_proof_freshness",
    "challenge_statement_to_law_mismatch",
    "challenge_restriction_basis",
    "challenge_obligation_partition",
    "challenge_runtime_mismatch",
    "request_auditor_escalation"
  ],
  "proof_limits": [
    "does_not_by_itself_establish_normative_wisdom",
    "does_not_by_itself_establish_predicate_completeness",
    "does_not_by_itself_establish_runtime_conformance",
    "does_not_by_itself_establish_empirical_acceptability_outside_predicate_set"
  ],
  "difference_from_mere_auditor_trust": "public_can_verify_bounded_legality_claims_without_payload_disclosure",
  "revocation_hooks": [
    "parent_commitment_change",
    "proof_obligation_set_change",
    "verifier_accreditation_revocation",
    "effective_interval_expiry"
  ],
  "runtime_binding_required": true
}
```

### `vertical_alignment_hardening_report@1`

```json
{
  "schema": "vertical_alignment_hardening_report@1",
  "retained_backbone": [
    "vertical_lawful_descent_not_horizontal_preference_fit",
    "L0_L1_L2_L3_stack",
    "Envelope_Payload_split",
    "lawful_descent_framing",
    "transparency_stratification_law",
    "projection_descent_binding_witness_pattern",
    "failure_mode_taxonomy",
    "ADEU_ODEU_layer_mapping"
  ],
  "hardened_gaps": [
    {
      "gap": "L1_publicity_looseness",
      "status": "closed",
      "fix": "segment_level_publicity_triple_plus_nonsealable_L1_core"
    },
    {
      "gap": "consumer_vs_office_ambiguity",
      "status": "closed",
      "fix": "explicit_consumer_office_contract_plus_office_allocation_rules"
    },
    {
      "gap": "witness_outline_without_calculus",
      "status": "closed",
      "fix": "support_map_composition_proof_partition_reuse_reissue_chain_legitimacy"
    },
    {
      "gap": "revocation_without_propagation",
      "status": "closed",
      "fix": "status_lattice_event_classes_material_dependency_cascade_grace_rules"
    },
    {
      "gap": "execution_manifest_only_gestured_at",
      "status": "closed",
      "fix": "manifest_attestation_conformance_protocol_plus_public_contestability_surface"
    },
    {
      "gap": "zk_as_gesture_not_protocol",
      "status": "closed",
      "fix": "typed_ir_commitment_proof_auditor_and_governance_surface_partition"
    }
  ],
  "v0_blocks_refined": [
    "vertical_alignment_layer_model@1",
    "restricted_schema_derivation_witness@1",
    "lawful_descent_proof_obligation@1"
  ],
  "new_required_public_surfaces": [
    "public_family_core",
    "public_annex_eligibility_law",
    "public_execution_alignment_manifest",
    "public_conformance_summary",
    "public_restricted_descent_commitment_surface"
  ],
  "remaining_engineering_tasks": [
    "proof_friendly_ADEU_IR",
    "standard_OEDU_proof_obligation_library",
    "trace_reduction_language_for_public_conformance",
    "office_allocation_certificate_registry",
    "verifier_accreditation_registry"
  ]
}
```

The hardened doctrine is now exact on where publicity must remain public, where secrecy may lawfully exist, how office differs from access, how witnesses compose, how revocation cascades, how execution must disclose alignment claims, and how sealed restricted descendants can be publicly challengeable without disclosing their sensitive payloads.
