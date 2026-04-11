Below is a constitutional model of alignment as vertical governance, not a preference-alignment essay. I am taking ADEU from the repo’s public materials as a docs-governed, typed, deterministic, fail-closed system organized by ontology, epistemics, deontics, and utility, and I am preserving the repo policy’s public invariants that the human component remains structurally internal, that integration must be legible in O/E/D/U terms, and that auditability and governance preservation are non-negotiable. ([GitHub][1])

I also build on two technical moves already visible in the repo’s support drafts: first, “lawful specialization” needs explicit bridge witnesses and non-widening certificates rather than slogans; second, the compiler cannot be an invisible constitutional editor, so source-to-schema projection witnesses are required. The schema-meta-core draft’s “stable envelope” idea is especially important here: legitimacy attaches primarily to identity, authority, scope, lineage, and proof surfaces, not only to full disclosure of payload internals. ([GitHub][2])

## VERTICAL_ALIGNMENT_ARCHITECTURE

Model every governed artifact as:

```text
Artifact a := <Envelope(a), Payload(a)>

Envelope(a) :=
  {
    artifact_id,
    schema_id,
    layer,
    kind,
    version,
    semantic_hash,
    authority_basis,
    settlement_posture,
    publicity_class,
    scope,
    source_refs,
    parent_refs,
    witness_refs,
    effective_interval,
    revocation_status
  }

Payload(a) := layer-specific content
```

`Envelope(a)` is the stable public or attestable governance object. `Payload(a)` may be public, restricted, or sealed depending on where misuse-risk concentrates. This lets legitimacy track the governance/evidence envelope even when some operational content is confidential. ([GitHub][3])

I will use four macro-layers:

**L0 — PUBLIC META-GOVERNANCE LAYER.**
This is the public law of schema production. It contains public principles, public meta-schemas, admissibility criteria, derivation law, secrecy classes, proof-obligation grammar, amendment rules, and public challenge rights. Nothing here may be constitutionally opaque.

**L1 — SCHEMA FAMILY / DOMAIN CONSTITUTION LAYER.**
This contains domain constitutions: domain ontologies, role vocabularies, action/effect catalogs, evidence floors, family-local constraints, project-type templates, and family-local override rules. This layer is public by default because downstream actors need to know what kinds of descendants may lawfully exist.

**L2 — RESTRICTED OPERATIONAL SCHEMA LAYER.**
This contains tactics, thresholds, detector features, routing logic, model overlays, escalation procedures, enforcement playbooks, and other misuse-sensitive operational artifacts. This is where secrecy is often legitimate, because misuse and evasion pressure usually concentrates here.

**L3 — EXECUTION LAYER.**
This contains live deployments, agents, operators, sessions, tools, logs, traces, user-facing action surfaces, and conformance reports. Visibility is mixed: public manifests and aggregate conformance should be visible; privacy- or security-sensitive raw traces may remain restricted.

Do not confuse these macro-layers with the lower-level packet calculus in the WCPGC support docs. Those docs use constitution / role / task / runtime packets, plus task residuals, bridge witnesses, and overlays. That packet stack can live inside L1-L3. Vertical alignment sits above it and governs whether those packetized descendants are lawful in the first place. ([GitHub][4])

The legal derivation operators are:

```text
Allowed:
  concretize
  restrict
  sequence
  allocate
  strengthen_evidence
  seal_sensitive_detail
  locally_defeat_default   (only when upper law explicitly admits it)

Forbidden under ordinary descent:
  rewrite_parent
  widen_permission
  lower_evidence_floor
  invent_governing_symbol
  runtime_to_law_laundering
  utility_overrides_deontics
  hidden_amendment
```

Formal descent law:

```text
lawful_descent(u, l, w) :=
  projection_ok(l)
  ∧ admissible_kind(kind(l), kind(u))
  ∧ ontology_map_total(u, l, w)
  ∧ scope(l) ⊆ delegated_scope(u)
  ∧ deontic_nonrewrite(u, l, w)
  ∧ epistemic_floor_preserved(u, l, w)
  ∧ utility_subordinated(l, u)
  ∧ transparency_justified(l, w)
  ∧ identity_pinned(l, w)
  ∧ verifier_check(w) = pass
```

Formal vertical alignment:

```text
VerticalAligned(x) :=
  ∃ M, F, R, PM, PF, PR, W01, W12, B :
    M ∈ L0 ∧ F ∈ L1 ∧ R ∈ L2 ∧ x ∈ L3
    ∧ publicity(M) = public
    ∧ projection_valid(PM, M)
    ∧ projection_valid(PF, F)
    ∧ projection_valid(PR, R)
    ∧ lawful_descent(M, F, W01)
    ∧ lawful_descent(F, R, W12)
    ∧ execution_binding(R, x, B)
    ∧ runtime_conformance(x, R)
```

So alignment is not primarily `human ↔ model`. It is `public law → family constitution → operational schema → execution surface`, with witnesses at each step.

This distinguishes vertical alignment from human-preference alignment, because the target is lawful descent rather than direct fit to local utility; from AI obedience, because a system may refuse unlawful commands; from behavioral safety-only framing, because upstream schema production matters as much as edge behavior; from market personalization, because personalization is lawful only inside a public envelope; and from institution-free alignment narratives, because without a body that emits and validates public reasoning goods there is no stable source of law.

## REASONING_PUBLIC_GOODS_THEORY

A reasoning public good artifact is a public artifact whose primary function is to enable lawful downstream reasoning across multiple consumers and multiple domains.

Formally:

```text
reasoning_public_good(g) :=
  publicity(g) = public
  ∧ nonrivalrous(g)
  ∧ reusable(g)
  ∧ inspectable(g)
  ∧ versioned(g)
  ∧ upstream_enabling(g)
  ∧ consumer_classes(g) ⊇ {human, synthetic}
  ∧ governs_schema_production(g)
```

The important properties are these:

Non-rivalrous: one human or one model using the artifact does not reduce its availability to others.

Reusable: it is not a one-off tactic. It can govern many family constitutions, many operational descendants, and many execution surfaces.

Inspectable: it is contestable, auditable, and versioned. A public principle no one can inspect is not a public good; it is a claim of legitimacy without civic access.

Upstream-enabling: it sits before domain specialization and before execution. It makes lawful descendants possible.

Consumer-plural: both humans and synthetic systems can consume it. Humans consume it as ratifiers, challengers, auditors, designers, and operators. Synthetic systems consume it as parsable law, planning constraint, validator input, and execution envelope.

Dual-form: reasoning public goods should exist both as human-readable constitutional text and as machine-checkable schema or proof interface. Otherwise one class of consumer gains privileged access to the law itself.

Typical reasoning public goods are public principle bundles, public meta-schemas, admissibility registries, derivation laws, proof-obligation grammars, transparency laws, amendment procedures, and failure taxonomies.

The crucial distinction is this: reasoning public goods are upstream law, not downstream tactics. A public principle set is a public good. A secret abuse-signature threshold is not. A public witness grammar is a public good. A sealed enforcement playbook is not. Public law should be common; sensitive operations may be private.

Shared consumption does not imply symmetric role. Humans and synthetic agents can read the same public constitution while occupying different offices. Office is allocated downstream by L1 and L2, not by mere access to L0.

## REASONING_GOVERNANCE_FUNCTION

Reasoning governance is the institutional function responsible for the supply chain of law-like reasoning artifacts.

It is not merely moderation or compliance. Moderation asks whether a downstream act should be blocked. Reasoning governance asks whether the schemas that could authorize downstream acts are themselves legitimate, whether they were lawfully produced, whether they descend lawfully, whether secrecy is justified, and whether execution remains bound to them.

Formally:

```text
ReasoningGovernance :=
  <emit,
   ratify,
   register,
   compile,
   validate_projection,
   validate_descent,
   attest_restricted,
   provision_public,
   monitor_conformance,
   repair,
   revoke,
   amend>
```

Its duties are:

Emit and ratify public reasoning goods.
It maintains the public meta-governance layer.

Compile source to typed schema.
This is where prose becomes machine-checkable law. It must produce projection witnesses.

Validate lawful descent.
This is where family constitutions and restricted operational schemas are checked as lawful descendants of public law.

Provision public goods to heterogeneous reasoners.
The same public artifacts must be available to humans and models in forms each can consume.

Attest restricted descendants.
Secrecy is not self-authenticating; a governance body must verify and publish lawful restrictedness.

Monitor runtime conformance.
Deployments must remain bound to the schemas they claim to enact.

Repair, revoke, and amend.
Versioning is semantic, not cosmetic. Revocation of an upper artifact propagates downward until descendants are re-attested.

Institutional shell can vary. It may be a public authority, internal constitutional board, consortium, or hybrid. The functional obligations do not vary.

## TRANSPARENCY_STRATIFICATION_LAW

Because legitimacy attaches to the governance/evidence envelope rather than the full payload, and because witness surfaces can expose normalized legality without exposing raw hidden reasoning, transparency should be stratified by constitutional function rather than by maximal disclosure. ([GitHub][3])

**Law T0 — No Secret Constitution.**
Anything that defines admissibility, derivation law, secrecy classes, proof obligations, amendment power, or public challenge rights must be public.

**Law T1 — Public Meta-Law.**
L0 is public as a matter of legitimacy, not convenience. Public principles, public meta-schemas, admissibility criteria, derivation verbs, failure taxonomies, and witness grammars are reasoning public goods and must remain inspectable.

**Law T2 — Public Family Core, Restricted Family Annexes.**
L1 is public by default. Domain ontology, role types, evidence floors, deontic envelopes, project types, and allowed secrecy classes must be public. Risk-sensitive annexes may be sealed only if they do not themselves alter admissibility or public rights.

**Law T3 — Operational Confidentiality Is Lawful Only as Descended Confidentiality.**
L2 may be restricted where disclosure materially increases misuse, evasion, privacy loss, or attack capability. Typical legitimate secrets are thresholds, detector features, exploit maps, exact enforcement routes, privileged prompts, credential-bearing materials, and sensitive escalation playbooks.

**Law T4 — Sealed-But-Provably-Derived Is a Publicity State, Not a Source of Authority.**
A sealed artifact has no independent legitimacy. It is lawful only as a provably derived descendant of higher public law.

**Law T5 — Execution Visibility Must Preserve Contestability.**
L3 may keep raw traces restricted for privacy or security, but every deployment should expose a public alignment manifest: active L0/L1 refs, L2 witness refs, proof mode, version, effective interval, revocation status, and challenge path.

So the architectural split is:

Public: constitutive law.
Restricted: misuse-sensitive operational payload.
Sealed but provably derived: restricted artifacts plus public commitments, parentage, proof mode, and challenge surfaces.

Constitutional opacity is forbidden. Operational confidentiality is permitted. Sealed descent is the bridge.

## RESTRICTED_DERIVATION_LEGITIMACY_MODEL

A restricted operational schema remains legitimate only when secrecy is subordinate to witnessability.

I use a three-plane witness model. The repo’s support docs already motivate the first two parts of this pattern: projection witnesses prevent compiler smuggling, and bridge witnesses prevent lower-layer constitutional laundering. I extend the pattern to runtime binding. ([GitHub][2])

**Plane 1 — Projection witness.**
Binds source artifacts to typed schema. It proves that the compiler did not silently invent law.

**Plane 2 — Descent witness.**
Binds lower clauses to upper clauses, admissibility bases, and non-widening certificates. It proves lawful specialization.

**Plane 3 — Binding witness.**
Binds the live system to the sealed operational schema hash and version. It proves that the deployment is actually running the attested descendant.

Restricted legitimacy condition:

```text
LegitRestricted(R) :=
  publicity(R) ∈ {restricted, sealed_derived}
  ∧ projection_ok(R)
  ∧ descent_ok(R)
  ∧ restriction_basis_valid(R)
  ∧ public_minimum_surface(R)
  ∧ auditor_or_public_verification(R)
  ∧ runtime_binding_ok(R)
```

A lawful restricted schema needs three visibility surfaces.

**Public minimum surface**
This must expose at least:

```text
{
  restricted_schema_id,
  sealed_hash,
  parent_refs,
  admissibility_bases,
  restriction_basis,
  proof_mode,
  verifier_ids,
  effective_interval,
  revocation_status,
  challenge_ref
}
```

**Auditor surface**
This may reveal the full sealed schema, full support map, full projection witness, and full clause-level proofs to designated reviewers under bounded confidentiality.

**Runtime surface**
This binds the deployment to the sealed schema hash and emits conformance records and typed violations.

Whole-artifact hashing is necessary but insufficient. Clause-level support is required. Otherwise an unlawful clause can hide inside an otherwise lawful bundle.

The proof obligations are:

1. **Projection coverage.** Every source fragment is accounted for as accepted, rejected, or ambiguous. Accepted fragments cannot retain unresolved layer ambiguity.
2. **Identity pinning.** Lower schema hash, version, parents, and effective interval are fixed and recorded.
3. **Ontology map totality.** Every governance-relevant lower symbol maps to public or family-authorized upper vocabulary.
4. **Scope subset.** Lower scope is equal to or narrower than delegated upper scope.
5. **Deontic non-rewrite.** Upper hard obligations and prohibitions cannot be erased by descent.
6. **Permission non-widening.** Lower permissions may narrow; they may widen only through explicit public delegation law.
7. **Epistemic floor preservation.** Lower evidence, provenance, and uncertainty requirements cannot undercut upper minima without explicit authorization.
8. **Utility subordination.** Local optimization terms must be declared and cannot override ontology, epistemics, or deontics.
9. **Restriction basis validity.** The reason for secrecy must itself be in the public secrecy-class law.
10. **Runtime binding and conformance.** The live system must attest to the sealed schema and emit conformance evidence.

Public proof can be realized at different strengths. The strongest mode is public cryptographic verification. A workable intermediate mode is public commitments plus independent auditor attestations plus runtime attestation. Anything weaker is administrative trust, not proof.

This also resolves the “same public meta-schema, different roles” issue. Both a human auditor and a synthetic executor can consume the same L0 law. What differs is not access to law but L1/L2 office allocation. Public law is shared; authority is role-scoped.

## FAILURE_MODE_TAXONOMY

Failure is diagnosed by broken supply-chain invariants, not only by bad behavior at the edge.

1. **Direct local utility capture.**
   Symptom: L2 or L3 optimizes engagement, throughput, convenience, or operator comfort as if that were the law.
   Broken invariant: utility subordination.
   Repair: force explicit utility envelopes and proof that U stays inside O/E/D.

2. **Hidden schema capture.**
   Symptom: actual governing rules live in uncatalogued prompts, weights, folk practices, or operator lore.
   Broken invariant: no secret constitution.
   Repair: register every governing artifact and bind execution to declared refs.

3. **Arbitrary restricted operational drift.**
   Symptom: secret operational behavior changes without new witness, new hash, or new version lineage.
   Broken invariant: identity pinning.
   Repair: sealed hash registry plus runtime attestation.

4. **Public-principle theater with opaque unlawful middle layers.**
   Symptom: public values remain polished rhetoric while the real operational layer widens permissions or invents exceptions.
   Broken invariant: lawful descent.
   Repair: clause-level descent witnesses and non-widening checks.

5. **Inability to audit derivation.**
   Symptom: no one can tell whether an artifact comes from lawful source interpretation or compiler improvisation.
   Broken invariant: projection witness requirement.
   Repair: source-to-schema projection manifests with full fragment accounting.

6. **Compiler smuggling.**
   Symptom: source text says one thing, emitted packets say another, but the compiler leaves no visible trail.
   Broken invariant: source coverage and ambiguity discipline.
   Repair: fail-closed projection witness.

7. **Runtime-to-law contamination.**
   Symptom: telemetry, habits, or feasibility facts silently become permissions or de facto norms.
   Broken invariant: runtime fact firewall.
   Repair: require explicit amendment or authorized defeat law before runtime can change normative status.

8. **Ontology smuggling.**
   Symptom: restricted descendants invent new governing categories, exception roles, or risk classes not licensed above.
   Broken invariant: ontology map totality.
   Repair: symbol mapping and authorized family vocabulary extensions only.

9. **Role collapse / false symmetry.**
   Symptom: because humans and AI share public meta-schemas, the system treats them as interchangeable offices; the human becomes a button, or the model becomes a constitutional author.
   Broken invariant: office allocation and human internalism.
   Repair: explicit role and authority separation in L1/L2.

10. **Proof theater.**
    Symptom: there are “certificates,” but no one can verify them, trace them, or bind them to runtime.
    Broken invariant: witness verifiability.
    Repair: signed proofs, public verifier identity, and execution binding.

11. **Trust collapse.**
    Symptom: the public sees secrecy without lawful parentage, proof mode, or challenge path.
    Broken invariant: constitutional publicity and contestability.
    Repair: public envelope disclosure even where payload remains sealed.

## ADEU_VERTICAL_ALIGNMENT_MAPPING

The repo’s public README defines ADEU as ontology, epistemics, deontics, and utility. I treat **ODEU** here as the ordered interpretive pass through the same four lanes: first settle ontology, then epistemics, then deontics, then utility. Utility therefore operates last, inside the envelope left by the other three. ([GitHub][1])

| Layer                  | Ontology                                                                                        | Epistemics                                                                                 | Deontics                                                                                          | Utility                                                                                |
| ---------------------- | ----------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------- |
| Meta-governance        | Defines artifact kinds, layer identities, scope vocabularies, derivation verbs, secrecy classes | Defines warrant classes, ambiguity rules, proof obligations, audit law, verifier standards | Defines authority boundaries, admissibility, amendment, challenge, revocation, transparency law   | Preserves reasoning commons, coherence, public trust, and long-range governability     |
| Family constitution    | Defines domain entities, roles, actions, effects, project types, family-local vocabularies      | Defines domain evidence floors, provenance rules, uncertainty markers, admissible sources  | Defines domain obligations, prohibitions, permissions, overrides, escalation eligibility          | Defines domain missions and performance aims bounded by domain O/E/D                   |
| Restricted operational | Defines tactical states, detector symbols, thresholds, routing surfaces, operational overlays   | Defines internal signals, confidence thresholds, case evidence use, secrecy-class handling | Defines concrete procedures, sanctions, interventions, escalations, failovers, exception handling | Optimizes speed, coverage, cost, and local effectiveness inside inherited O/E/D bounds |
| Execution              | Defines live deployments, sessions, traces, tool states, user-facing surfaces                   | Defines telemetry, logs, conformance evidence, incident records, runtime uncertainty       | Enacts actual allow/deny/route/escalate actions and records typed violations                      | Realizes service outcomes, safety yield, response time, and resource consumption       |

The practical ODEU rule at every layer is:

```text
O settles what the objects and boundaries are.
E settles what counts as warranted.
D settles what is permitted, forbidden, or obligatory.
U ranks options only within the remaining O/E/D-feasible set.
```

That ordering is what prevents direct utility capture from becoming a hidden constitution.

## MACHINE-CHECKABLE BLOCKS

These are compact seed schemas, not exhaustive production validators.

### reasoning_public_good@1

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "reasoning_public_good@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "artifact_id",
    "kind",
    "publicity",
    "consumer_classes",
    "governed_axes",
    "upstream_layers",
    "inspectable",
    "reusable",
    "non_rivalrous"
  ],
  "properties": {
    "schema": { "const": "reasoning_public_good@1" },
    "artifact_id": { "type": "string" },
    "kind": {
      "enum": [
        "public_principle_bundle",
        "public_meta_schema",
        "admissibility_registry",
        "derivation_law",
        "proof_interface",
        "failure_taxonomy",
        "amendment_rule"
      ]
    },
    "publicity": { "const": "public" },
    "consumer_classes": {
      "type": "array",
      "uniqueItems": true,
      "items": { "enum": ["human", "synthetic", "institutional"] }
    },
    "governed_axes": {
      "type": "array",
      "uniqueItems": true,
      "items": { "enum": ["O", "E", "D", "U"] }
    },
    "upstream_layers": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "meta_governance",
          "family_constitution",
          "restricted_operational",
          "execution"
        ]
      }
    },
    "inspectable": { "const": true },
    "reusable": { "const": true },
    "non_rivalrous": { "const": true }
  }
}
```

### reasoning_governance_schema@1

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "reasoning_governance_schema@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "body_id",
    "public_registry_ref",
    "challenge_process_ref",
    "amendment_process_ref",
    "functions",
    "verification_modes",
    "fail_closed_on_missing_witness"
  ],
  "properties": {
    "schema": { "const": "reasoning_governance_schema@1" },
    "body_id": { "type": "string" },
    "public_registry_ref": { "type": "string" },
    "challenge_process_ref": { "type": "string" },
    "amendment_process_ref": { "type": "string" },
    "signature_key_ref": { "type": "string" },
    "functions": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "emit",
          "ratify",
          "register",
          "compile",
          "validate_projection",
          "validate_descent",
          "attest_restricted",
          "provision_public",
          "monitor_conformance",
          "repair",
          "revoke",
          "amend"
        ]
      }
    },
    "verification_modes": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "public_check",
          "auditor_check",
          "runtime_attestation",
          "zk_check"
        ]
      }
    },
    "fail_closed_on_missing_witness": { "type": "boolean" }
  }
}
```

### vertical_alignment_layer_model@1

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "vertical_alignment_layer_model@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "layer_order",
    "allowed_descent_ops",
    "forbidden_descent_ops",
    "mandatory_witnesses",
    "publicity_defaults"
  ],
  "properties": {
    "schema": { "const": "vertical_alignment_layer_model@1" },
    "layer_order": {
      "type": "array",
      "prefixItems": [
        { "const": "meta_governance" },
        { "const": "family_constitution" },
        { "const": "restricted_operational" },
        { "const": "execution" }
      ],
      "minItems": 4,
      "maxItems": 4
    },
    "allowed_descent_ops": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "concretize",
          "restrict",
          "sequence",
          "allocate",
          "strengthen_evidence",
          "seal",
          "locally_defeat_default"
        ]
      }
    },
    "forbidden_descent_ops": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "rewrite_parent",
          "widen_permission",
          "lower_evidence_floor",
          "invent_governing_symbol",
          "runtime_to_law_laundering",
          "utility_overrides_deontics",
          "hidden_amendment"
        ]
      }
    },
    "mandatory_witnesses": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "projection_witness",
          "descent_witness",
          "binding_witness",
          "conformance_record"
        ]
      }
    },
    "publicity_defaults": {
      "type": "object",
      "additionalProperties": false,
      "required": [
        "meta_governance",
        "family_constitution",
        "restricted_operational",
        "execution"
      ],
      "properties": {
        "meta_governance": { "const": "public" },
        "family_constitution": { "enum": ["public", "sealed_derived"] },
        "restricted_operational": { "enum": ["restricted", "sealed_derived"] },
        "execution": { "const": "mixed" }
      }
    }
  }
}
```

### transparency_stratification_rule@1

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "transparency_stratification_rule@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "public_mandates",
    "restricted_allowances",
    "sealed_requirements",
    "forbidden_secret_targets"
  ],
  "properties": {
    "schema": { "const": "transparency_stratification_rule@1" },
    "public_mandates": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "public_principles",
          "public_meta_schemas",
          "admissibility_criteria",
          "derivation_law",
          "proof_obligation_set",
          "challenge_rights",
          "amendment_power",
          "active_parent_refs"
        ]
      }
    },
    "restricted_allowances": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "tactics",
          "thresholds",
          "detector_features",
          "exploit_maps",
          "credential_material",
          "sensitive_enforcement_procedure",
          "privacy_sensitive_trace"
        ]
      }
    },
    "sealed_requirements": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "hash_commitment",
          "parent_refs",
          "restriction_basis",
          "proof_mode",
          "verifier_identity",
          "challenge_ref",
          "revocation_status",
          "effective_interval"
        ]
      }
    },
    "forbidden_secret_targets": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "admissibility_criteria",
          "derivation_law",
          "proof_obligation_set",
          "amendment_power",
          "challenge_rights",
          "secrecy_classification_law"
        ]
      }
    }
  }
}
```

### restricted_schema_derivation_witness@1

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "restricted_schema_derivation_witness@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "witness_id",
    "lower_artifact_commitment",
    "upper_artifact_refs",
    "restriction_basis",
    "proof_mode",
    "support_map",
    "verifier_refs"
  ],
  "properties": {
    "schema": { "const": "restricted_schema_derivation_witness@1" },
    "witness_id": { "type": "string" },
    "lower_artifact_commitment": { "type": "string" },
    "upper_artifact_refs": {
      "type": "array",
      "minItems": 1,
      "items": { "type": "string" }
    },
    "restriction_basis": {
      "enum": [
        "misuse_risk",
        "evasion_risk",
        "privacy_risk",
        "credential_risk",
        "security_risk",
        "institutional_sensitivity"
      ]
    },
    "proof_mode": {
      "enum": [
        "public_redacted",
        "auditor_attested",
        "zk_attested"
      ]
    },
    "support_map": {
      "type": "array",
      "minItems": 1,
      "items": {
        "type": "object",
        "additionalProperties": false,
        "required": [
          "lower_clause_commitment",
          "upper_clause_refs",
          "admissibility_basis",
          "nonwidening_certificate_kind"
        ],
        "properties": {
          "lower_clause_commitment": { "type": "string" },
          "upper_clause_refs": {
            "type": "array",
            "minItems": 1,
            "items": { "type": "string" }
          },
          "admissibility_basis": {
            "enum": [
              "kind_admissibility",
              "role_local_default",
              "task_hard_ordering",
              "permission_subset",
              "default_defeat",
              "family_local_extension",
              "evidence_strengthening"
            ]
          },
          "nonwidening_certificate_kind": {
            "enum": [
              "action_subset",
              "effect_subset",
              "scope_subset",
              "order_restriction",
              "evidence_floor_preserved",
              "utility_subordination",
              "ontology_map_total"
            ]
          }
        }
      }
    },
    "verifier_refs": {
      "type": "array",
      "minItems": 1,
      "items": { "type": "string" }
    },
    "public_reveal_set": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "commitment",
          "parents",
          "restriction_basis",
          "proof_mode",
          "verifiers",
          "effective_interval",
          "challenge_ref"
        ]
      }
    }
  }
}
```

### lawful_descent_proof_obligation@1

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "lawful_descent_proof_obligation@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "obligation_id",
    "from_layer",
    "to_layer",
    "required_checks",
    "verdict"
  ],
  "properties": {
    "schema": { "const": "lawful_descent_proof_obligation@1" },
    "obligation_id": { "type": "string" },
    "from_layer": {
      "enum": [
        "meta_governance",
        "family_constitution",
        "restricted_operational"
      ]
    },
    "to_layer": {
      "enum": [
        "family_constitution",
        "restricted_operational",
        "execution"
      ]
    },
    "required_checks": {
      "type": "array",
      "uniqueItems": true,
      "items": {
        "enum": [
          "projection_coverage",
          "kind_admissibility",
          "ontology_map_total",
          "scope_subset",
          "deontic_nonrewrite",
          "permission_nonwidening",
          "epistemic_floor",
          "utility_subordination",
          "restriction_basis_valid",
          "identity_pinned",
          "verifier_signature",
          "runtime_binding"
        ]
      }
    },
    "verdict": { "enum": ["pass", "fail", "inconclusive"] },
    "failed_checks": {
      "type": "array",
      "uniqueItems": true,
      "items": { "type": "string" }
    },
    "evidence_refs": {
      "type": "array",
      "items": { "type": "string" }
    }
  }
}
```

### vertical_alignment_failure_report@1

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "vertical_alignment_failure_report@1",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "schema",
    "failure_id",
    "failure_class",
    "layer_of_origin",
    "broken_invariants",
    "severity",
    "status",
    "required_repairs"
  ],
  "properties": {
    "schema": { "const": "vertical_alignment_failure_report@1" },
    "failure_id": { "type": "string" },
    "failure_class": {
      "enum": [
        "local_utility_capture",
        "hidden_schema_capture",
        "restricted_operational_drift",
        "public_principle_theater",
        "derivation_audit_void",
        "compiler_smuggling",
        "runtime_to_law_laundering",
        "ontology_smuggling",
        "role_collapse",
        "proof_theater",
        "trust_collapse"
      ]
    },
    "layer_of_origin": {
      "enum": [
        "meta_governance",
        "family_constitution",
        "restricted_operational",
        "execution"
      ]
    },
    "broken_invariants": {
      "type": "array",
      "minItems": 1,
      "uniqueItems": true,
      "items": {
        "enum": [
          "constitutional_publicity",
          "projection_witness_required",
          "lawful_descent_required",
          "no_secret_constitution",
          "epistemic_floor",
          "deontic_nonrewrite",
          "utility_subordination",
          "runtime_binding",
          "auditability",
          "human_internalism"
        ]
      }
    },
    "severity": { "enum": ["low", "medium", "high", "critical"] },
    "status": { "enum": ["open", "contained", "repaired", "revoked"] },
    "required_repairs": {
      "type": "array",
      "minItems": 1,
      "items": { "type": "string" }
    }
  }
}
```

This yields a vertical-alignment doctrine in which public reasoning goods govern the law of downstream reasoning, restricted operational schemas can remain legitimate without full disclosure, and alignment becomes a property of witness-carrying lawful descent rather than a thin horizontal fit between a user and a model.

[1]: https://github.com/LexLattice/adeu-studio "https://github.com/LexLattice/adeu-studio"
[2]: https://github.com/LexLattice/adeu-studio/blob/main/docs/support/DRAFT_WCPGC_STRICT_V0_PROFILE_v0.md "https://github.com/LexLattice/adeu-studio/blob/main/docs/support/DRAFT_WCPGC_STRICT_V0_PROFILE_v0.md"
[3]: https://github.com/LexLattice/adeu-studio/blob/main/docs/DRAFT_SCHEMA_META_CORE_v0.md "https://github.com/LexLattice/adeu-studio/blob/main/docs/DRAFT_SCHEMA_META_CORE_v0.md"
[4]: https://github.com/LexLattice/adeu-studio/blob/main/docs/support/DRAFT_WCPGC_CORE_FRAMEWORK_v0.md "https://github.com/LexLattice/adeu-studio/blob/main/docs/support/DRAFT_WCPGC_CORE_FRAMEWORK_v0.md"
