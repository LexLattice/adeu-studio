## 1. Executive conclusion

The best fit is **Candidate 3: hybrid core plus overlays**.

The corpus does **not** support a single flat meta-schema in the sense of one uniform field grammar. But it also does **not** behave like a pile of unrelated schema families. What it evidences is:

* a **stable ADEU artifact envelope** around identity, lineage anchors, governance posture, boundedness, evidence/derivation, and settlement, and
* a small number of **irreducible carrier forms** inside that envelope, plus
* **lineage-specific anchor vocabularies** for ARC, architecture, meta-loop, UX, synthetic-pressure, policy/runtime, and legacy validator strata.

So the latent structure is:

**one common core + explicit carrier overlays + explicit lineage overlays + narrow residuals for legacy/open-map drift.**

That is the smallest abstraction I found that is still genuinely explanatory and still plausibly lossless at the schema-definition level.

---

## 2. Corpus overview

I treated the **schema definitions** as the primary corpus:

* `packages/*/schema/*.json`
* `spec/*.schema.json`
* `packages/urm_runtime/src/.../instruction_policy.schema.json`

I used docs only secondarily, and I used ARC fixture rejection cases in `apps/api/fixtures/arc_agi/..._reject_*.json` only to interpret which distinctions are governance-significant.

After deduplicating mirrored `spec/` and package schemas by normalized content, the corpus is:

* **179 schema files**
* **101 unique schema definitions**

A few broad corpus facts matter:

* **99/101** root schemas are closed objects (`additionalProperties: false`)
* **86/101** use local `$defs`
* **93/101** carry a top-level `schema` discriminator
* **3** older schemas use `schema_version` instead
* **5** legacy schemas have neither `schema` nor `schema_version`
* top-level **id-like slots** appear in **83**
* top-level **ref-like slots** appear in **64**
* top-level **hash-like slots** appear in **53**

That already rules out “arbitrary JSON blobs.” The corpus is strongly typed, closed-world, and anchor-heavy.

### Family clustering summary

I did **not** rely only on filename prefixes. The real grouping came from root field vocabularies, repeated `$defs`, anchor tuples, and governance posture. A simple token-overlap clustering over property names and `$defs` recovered the following broad lineages:

| Lineage cluster                | Count | Coherence signal                                                                                                            |
| ------------------------------ | ----: | --------------------------------------------------------------------------------------------------------------------------- |
| ARC operational                |    12 | `task_packet_id/ref`, `observation_frame_id/ref`, `evidence_refs`, settlement/authority fixtures                            |
| Architecture analysis          |    18 | `authority_boundary_policy`, `intent_packet_id`, `source_set/source_set_hash`, `architecture_id`, `semantic_hash`           |
| Meta-loop                      |     9 | all share `intent_packet_id`, `reference_instance_id`, `reference_loop_family`                                              |
| UX surface                     |    10 | all share `reference_surface_family`; most share `approved_profile_id`, `authority_boundary_policy`, `supporting_artifacts` |
| Synthetic pressure mismatch    |     7 | all share `contract_source`, `target_arc`, `target_path`; most share registry fixture trio                                  |
| Core IR / integrity / advice   |    20 | source-text/hash posture, integrity artifacts, payload/projection families                                                  |
| Policy/runtime/evidence        |    16 | policy hash / activation / decision / evidence forms                                                                        |
| Legacy IR / validator / puzzle |     8 | weak common discriminator; channel/solver-oriented                                                                          |
| Commitments                    |     1 | singleton, structurally closest to core structural IR                                                                       |

### Initial observations

The important observations are these:

1. **The stable thing is the envelope, not the inner payload.**
   Identity, refs, hashes, authority boundaries, evidence, derivation, settlement, and closure recur much more consistently than any one inner content shape.

2. **Explicit O/E/D/U is not the universal surface grammar.**
   It is explicit in structural-model families such as `adeu.ir`, `adeu_core_ir`, `adeu_architecture_semantic_ir`, and `ux_morph_ir`. But most later operational schemas surface ADEU more through **authority/evidence/settlement/boundedness** than through explicit O/E/D/U fields.

3. **Different lineages use different canonical anchor tuples.**
   Examples:

   * ARC: `task_packet_id/ref`, `observation_frame_id/ref`, `hypothesis_frame_id/ref`, `rollout_trace_id/ref`
   * Architecture: `intent_packet_id`, `analysis_request_id/ref`, `settlement_frame_id/ref`, `architecture_id`, `semantic_hash`, `source_set_hash`
   * Meta-loop: `intent_packet_id`, `reference_instance_id`, `reference_loop_family`, `reference_anchor`
   * UX: `approved_profile_id`, `reference_instance_id`, `reference_surface_family`
   * Synthetic pressure mismatch: `registry_id`, `registry_schema`, `registry_reference_fixture`, `target_arc`, `target_path`
   * Policy/runtime: `policy_hash`, `schema_id`, `activation_seq`, `request_hash`, `formula_hash`

4. **Governance fields are not decorative.**
   ARC reject fixtures explicitly encode failures like `non_authoritative_posture`, `deontic_outside_envelope`, `settlement_posture_erasure`, `post_hoc_reconstruction`, `retroactive_selection_swap`, and `hidden_branching_laundering`. That is strong evidence that authority posture, lineage monotonicity, settlement posture, and evidence completeness are core ADEU semantics, not naming noise.

5. **There is real drift.**
   The older `adeu_ir` / validator / puzzle stratum lacks the stronger discriminator and overlay discipline of later families. There are also narrow open-map holes (`metadata`, `details`, `options`, `semantic_policy_json`, `proposed_action_payload`, etc.).

---

## 3. Extracted role-forms

These are the recurring higher-order role-forms I believe are actually present.

### Packet

A bounded unit of intent, input, advice, or domain setup.

Evidence:

* `adeu_arc_task_packet`
* `adeu_architecture_intent_packet`
* `meta_testing_intent_packet`
* `ux_domain_packet`
* `adeu_normative_advice_packet`

### Frame

A structured partial model under an explicit interpretive posture.

Evidence:

* `adeu_arc_observation_frame`
* `adeu_arc_hypothesis_frame`
* `adeu_architecture_ontology_frame`
* `adeu_architecture_analysis_settlement_frame`

### Request

A bounded solicitation for analysis, validation, or oracle judgment.

Evidence:

* `adeu_architecture_analysis_request`
* `adeu_architecture_oracle_request`
* `synthetic_pressure_mismatch_oracle_request`
* `adeu.validator_request`

### Resolution

A reply or adjudicated answer bound to a request.

Evidence:

* `adeu_architecture_oracle_resolution`
* `synthetic_pressure_mismatch_oracle_resolution`

### Trace

An ordered execution/checkpoint lineage.

Evidence:

* `adeu_arc_rollout_trace`
* `adeu_architecture_checkpoint_trace`
* `meta_loop_run_trace`
* `synthetic_pressure_mismatch_checkpoint_trace`

### Record

A run/lifecycle artifact summarizing execution or evaluation state.

Evidence:

* `adeu_arc_reasoning_run_record`
* `adeu_arc_local_eval_record`
* `adeu_arc_submission_execution_record`
* `adeu_arc_three_puzzle_harness_record`

### Curated set

A family of collection forms where the semantics are materialization, ordering, registry, or emitted-set capture.

Subkinds:

* **bundle**: `adeu_arc_puzzle_input_bundle`, `adeu_arc_behavior_evidence_bundle`
* **manifest**: `adeu_arc_scorecard_manifest`, `adeu_architecture_analysis_run_manifest`, `adeu_architecture_projection_manifest`, `meta_control_update_manifest`
* **registry/catalog**: `synthetic_pressure_mismatch_rule_registry`, `policy_registry`, `meta_module_catalog`
* **table/glossary/snapshot**: `v36a_first_family_approved_profile_table`, `v36a_same_context_reachability_glossary`, `connector_snapshot`

### Adjudication

Reports, diagnostics, evidence packets, explainers, and similar verdict-bearing forms.

Evidence:

* `adeu_architecture_conformance_report`
* `adeu_architecture_alignment_report`
* `meta_loop_conformance_report`
* `meta_loop_drift_diagnostics`
* `ux_conformance_report`
* `semantic_depth_report`
* `semantics_diagnostics`
* `policy_explain`
* `proof_evidence`
* `validator_evidence_packet`

### Contract / policy

Normative gate surfaces.

Evidence:

* `meta_loop_sequence_contract`
* `ux_interaction_contract`
* `instruction_policy`
* `adeu_integrity_cycle_policy`
* `policy_connector_exposure_mapping.v1`
* `policy_incident_redaction_allowlist.v1`

### Structural model

IR, graph, payload, delta, projection, or plan carriers.

Evidence:

* `adeu_core_ir`
* `adeu_architecture_semantic_ir`
* `adeu_architecture_boundary_graph`
* `adeu_architecture_ir_delta`
* `ux_morph_ir`
* `ux_surface_projection`
* `adeu_read_surface_payload`
* `adeu_brokered_reflexive_payload`
* `adeu_brokered_reflexive_execution_plan`

### Operational coordination microforms

Small runtime coordination artifacts.

Evidence:

* `policy_activation_log`
* `scheduler_dispatch_token`

These role-forms are **not mutually exclusive as names**, but in practice most schemas have one dominant carrier role.

---

## 4. Candidate 1: maximal unification

### Abstract model

This candidate assumes the whole corpus is evidence of **one deep ADEU artifact schema**.

The smallest non-cheating version I could derive is roughly:

* **Header**

  * discriminator (`schema` / `schema_version`)
  * closure mode
  * local named defs
* **Anchors**

  * ids
  * refs
  * hashes
  * seq/time anchors
* **Governance**

  * authority encoding
  * boundedness/scope
  * settlement encoding
  * advisory/authoritative posture
* **Lineage / evidence**

  * source bindings
  * evidence bindings
  * derivation bindings
* **Content planes**
  one unified artifact may expose one or more of:

  * intake/frame plane
  * trace/record plane
  * curated-set plane
  * adjudication plane
  * contract/policy plane
  * structural-model plane

### Strengths

* Best at surfacing the strongest shared ADEU intuition: **every artifact is a governed boundary object**.
* Explains why architecture, meta-loop, and UX partially cluster together despite different prefixes.
* Maximally compressive in theory.

### Weaknesses

* It only works by making the inner carrier planes highly optional.
* Once you do that, the model starts to look like a **typed artifact AST**, not a clean meta-schema.
* Governance encodings that are genuinely different get flattened:

  * architecture `AuthorityBoundaryPolicy`
  * UX `UXAuthorityBoundaryPolicy`
  * ARC authority source/scope/validity quartet
  * synthetic `contract_source`
* Lean formalization would inherit many impossible states from the mega-record.

### Round-trip assessment

At the schema-definition level, this candidate is **conditionally lossless**, but only if it keeps:

* exact named local defs,
* exact field names,
* explicit content-plane assignment,
* narrow open-map residuals.

Representative audit:

* `adeu_arc_task_packet` → round-trips cleanly.
* `adeu_architecture_analysis_request` → round-trips cleanly.
* `policy_registry` → round-trips cleanly except for open `semantic_policy_json`.
* `meta_loop_sequence_contract` → only round-trips cleanly if “contract/gate sequence grammar” is preserved as its own sublanguage.
* `ux_interaction_contract` → same problem, but with a different contract grammar.
* `adeu_core_ir` → forces a structural-model sublanguage.
* `adeu.validator_result` → forces legacy/open-map residuals.

So Candidate 1 is **lossless only by growing large enough to nearly become a schema-of-schemas**. That makes it a useful diagnostic baseline, not the best final answer.

---

## 5. Candidate 2: conservative multi-family

### Abstract model

This candidate assumes there is **no single stable meta-schema**, only several irreducible lineage families.

The cleanest conservative split is:

* ARC operational family
* Architecture analysis family
* Meta-loop family
* UX family
* Synthetic pressure mismatch family
* Core structural / integrity family
* Policy/runtime family
* Legacy validator / puzzle family
* Commitments singleton family

Each family gets its own meta-schema, with its own anchor vocabulary, governance encoding, and allowed role-forms.

### Strengths

* Highest local fidelity.
* Very honest about genuine lineage differences.
* Easy to round-trip because each family keeps its own native grammar.

### Weaknesses

* It under-explains the cross-corpus ADEU convergence.
* It duplicates the same ideas repeatedly:
  identity, refs, hashes, authority limits, evidence anchors, settlement, derivation.
* It treats repo history as ontology too quickly.
* It is weak for repo self-description because it cannot say clearly what makes all these artifacts “ADEU-style.”

### Round-trip assessment

This candidate is **straightforwardly lossless** on representative schemas:

* `adeu_arc_scorecard_manifest` → ARC family schema
* `adeu_architecture_analysis_request` → Architecture family schema
* `meta_loop_sequence_contract` → Meta-loop family schema
* `ux_interaction_contract` → UX family schema
* `policy_registry` → Policy/runtime family schema
* `adeu_core_ir` → Core structural family schema
* `adeu.validator_result` → Legacy validator family schema

The problem is not losslessness. The problem is **explanatory under-compression**. It preserves too much separation and misses the obvious shared ADEU envelope.

---

## 6. Candidate 3: hybrid core plus overlays

### Abstract model

This candidate says:

* there is a stable **core envelope**
* there are a small number of explicit **carrier overlays**
* there are explicit **lineage overlays** for irreducible anchor/governance vocabularies

That model is:

```text
Artifact :=
  CoreEnvelope
  + CarrierOverlay
  + LineageOverlay
  + LocalTypeDefs
  + NarrowResidualOpenMaps
```

### Universal core envelope

The core that is actually evidenced across the corpus is:

* **discriminator**

  * `schema` or `schema_version`
* **closure / typing**

  * closed root object by default
  * local named defs
* **anchors**

  * ids
  * refs
  * hashes
  * timestamps / sequence anchors
* **governance envelope**

  * authority boundary or authority basis encoding
  * boundedness / scope
  * settlement posture
  * advisory vs authoritative posture
* **evidence / lineage**

  * source bindings
  * evidence bindings
  * derivation / compilation provenance

### Carrier overlays

These are the smallest carrier classes that cover the corpus:

1. **IntakeFrame**
   subkinds: packet, frame, request, candidate

2. **TraceRecord**
   subkinds: trace, record, log, token

3. **CuratedSet**
   subkinds: bundle, manifest, registry, catalog, table, glossary, snapshot

4. **Adjudication**
   subkinds: report, diagnostics, resolution, evidence, result, explain

5. **ContractGate**
   subkinds: contract, policy

6. **StructuralModel**
   subkinds: IR, graph, payload, delta, projection, plan

### Lineage overlays

These should be explicit, not implicit:

* **ARCOperational**
* **ArchitectureAnalysis**
* **MetaLoopControl**
* **UXSurface**
* **SyntheticPressureMismatch**
* **PolicyRuntime**
* **CoreStructuralIntegrity**
* **LegacyIRValidator**

`adeu_commitments_ir` fits best as a `CoreStructuralIntegrity` sublineage, not as a fully separate top-level ontology.

### Strengths

* Preserves the real shared ADEU envelope.
* Preserves the real role-form distinctions.
* Preserves lineage-specific governance vocabularies.
* Keeps residuals narrow and named.
* Best match for future repo self-description and Lean formalization.

### Weaknesses

* Requires maintaining a lineage-overlay registry.
* A few microforms remain awkward:
  `policy_activation_log`, `scheduler_dispatch_token`, `connector_snapshot`
* Legacy schemas still need an explicit compatibility overlay.

### Round-trip assessment

This is the best round-trip fit.

Representative mappings:

| Concrete schema                        | Hybrid mapping                                           | Lossless?                                                |
| -------------------------------------- | -------------------------------------------------------- | -------------------------------------------------------- |
| `adeu_arc_task_packet`                 | Core + `IntakeFrame(packet)` + `ARCOperational`          | Yes                                                      |
| `adeu_arc_scorecard_manifest`          | Core + `CuratedSet(manifest)` + `ARCOperational`         | Yes                                                      |
| `adeu_architecture_analysis_request`   | Core + `IntakeFrame(request)` + `ArchitectureAnalysis`   | Yes                                                      |
| `adeu_architecture_conformance_report` | Core + `Adjudication(report)` + `ArchitectureAnalysis`   | Yes                                                      |
| `meta_loop_sequence_contract`          | Core + `ContractGate(contract)` + `MetaLoopControl`      | Yes                                                      |
| `ux_interaction_contract`              | Core + `ContractGate(contract)` + `UXSurface`            | Yes                                                      |
| `adeu_core_ir`                         | Core + `StructuralModel(ir)` + `CoreStructuralIntegrity` | Yes                                                      |
| `policy_registry`                      | Core + `CuratedSet(registry)` + `PolicyRuntime`          | Yes, with named open-map slot for `semantic_policy_json` |
| `adeu.validator_result`                | Core-lite + `Adjudication(result)` + `LegacyIRValidator` | Yes, but requires explicit legacy/open-map residuals     |

This candidate gives **lossless schema-definition reconstruction with narrow residuals**, rather than broad catch-all payload escape hatches.

---

## 7. Comparative matrix

| Criterion                        | Candidate 1: maximal unification       | Candidate 2: conservative multi-family | Candidate 3: hybrid core + overlays |
| -------------------------------- | -------------------------------------- | -------------------------------------- | ----------------------------------- |
| Losslessness                     | Conditional high                       | High                                   | High                                |
| Non-triviality                   | Medium                                 | Medium                                 | High                                |
| Explanatory power                | Medium                                 | Medium-low                             | High                                |
| ADEU faithfulness                | Medium                                 | Medium-high                            | High                                |
| Governance fidelity              | Medium                                 | High                                   | High                                |
| Lineage/evidence preservation    | Medium                                 | High                                   | High                                |
| Simplicity                       | Superficially simple, actually bloated | Locally simple, globally fragmented    | Best balance                        |
| Compositionality                 | Medium-low                             | Low-medium                             | High                                |
| Lean translatability             | Medium-low                             | Medium                                 | High                                |
| Repo self-description usefulness | Medium                                 | Medium                                 | High                                |
| Residual burden                  | High                                   | Medium                                 | Low-medium                          |

---

## 8. Minimal recommended meta-schema

My best current proposal is:

```text
ArtifactCore
  discriminator
  closure_mode
  local_defs
  anchors:
    ids
    refs
    hashes
    seq_times
  governance:
    authority
    boundedness
    settlement
    advisory_status
  lineage:
    source_bindings
    evidence_bindings
    derivation_bindings

CarrierOverlay
  IntakeFrame
  TraceRecord
  CuratedSet
  Adjudication
  ContractGate
  StructuralModel

LineageOverlay
  ARCOperational
  ArchitectureAnalysis
  MetaLoopControl
  UXSurface
  SyntheticPressureMismatch
  PolicyRuntime
  CoreStructuralIntegrity
  LegacyIRValidator

ResidualOpenMaps
  named, explicit, narrow
```

### Explicit universal core

What I would treat as universal enough to put in the meta-schema core:

* discriminator
* closure/typing discipline
* anchor slots (`id`, `ref`, `hash`, `seq/time`)
* governance envelope
* evidence/lineage/derivation envelope

### Explicit overlays

The minimum explicit overlays I would expose:

* carrier overlay: one of six carrier classes
* lineage overlay: one of eight lineage vocabularies

### Explicit residuals

The main residuals are:

* **legacy discriminator drift**

  * `schema_version` instead of `schema`
  * or neither
* **named open maps**

  * `metadata`
  * `details`
  * `options`
  * `semantic_policy_json`
  * `proposed_action_payload`
  * a few similar holes
* **singleton or microform outliers**

  * `v40f_architecture_release_integration_evidence`
  * `policy_activation_log`
  * `scheduler_dispatch_token`
  * `connector_snapshot`

These residuals are real, but they are narrow enough that they do not invalidate the hybrid abstraction.

---

## 9. Mapping appendix

### ARC operational lineage

Maps to:

* carriers: `IntakeFrame`, `TraceRecord`, `CuratedSet`, `Adjudication`
* lineage overlay: `ARCOperational`

Key anchors:

* `task_packet_id/ref`
* `observation_frame_id/ref`
* `hypothesis_frame_id/ref`
* `action_proposal_id/ref`
* `rollout_trace_id/ref`
* `run_id`, `session_ref`

Key governance:

* authority basis/source/scope/validity
* deferred authority assertions
* settlement posture carry/checks
* competition/environment boundary

### Architecture analysis lineage

Maps to:

* carriers: `IntakeFrame`, `StructuralModel`, `TraceRecord`, `CuratedSet`, `Adjudication`
* lineage overlay: `ArchitectureAnalysis`

Key anchors:

* `analysis_request_id/ref`
* `intent_packet_id`
* `settlement_frame_id/ref`
* `architecture_id`
* `semantic_hash`
* `source_set/source_set_hash`

Key governance:

* `AuthorityBoundaryPolicy`
* deterministic adjudicator authoritative
* oracle advisory only
* projections may not mint authority

### Meta-loop lineage

Maps to:

* carriers: `IntakeFrame`, `ContractGate`, `TraceRecord`, `CuratedSet`, `Adjudication`
* lineage overlay: `MetaLoopControl`

Key anchors:

* `intent_packet_id`
* `reference_instance_id`
* `reference_loop_family`
* `reference_anchor`

Key governance:

* accepted-compilation threshold
* operational-influence threshold
* no hidden branch logic
* no prose-truth substitution

### UX lineage

Maps to:

* carriers: `IntakeFrame`, `ContractGate`, `StructuralModel`, `CuratedSet`, `Adjudication`
* lineage overlay: `UXSurface`

Key anchors:

* `approved_profile_id`
* `reference_instance_id`
* `reference_surface_family`

Key governance:

* `UXAuthorityBoundaryPolicy`
* implementation observable bindings
* stable provenance hooks
* no visual authority inflation

### Synthetic pressure mismatch lineage

Maps to:

* carriers: `IntakeFrame`, `TraceRecord`, `CuratedSet`, `Adjudication`
* lineage overlay: `SyntheticPressureMismatch`

Key anchors:

* `registry_id`
* `registry_schema`
* `registry_reference_fixture`
* `target_arc`
* `target_path`
* `checkpoint_id`

Key governance:

* `contract_source`
* derivation metadata
* rule-registry control
* oracle request/resolution route

### Core IR / integrity / advice lineage

Maps to:

* carriers: `StructuralModel`, `ContractGate`, `Adjudication`, `IntakeFrame`
* lineage overlay: `CoreStructuralIntegrity`

Key anchors:

* `source_text_hash`
* `concept_artifact_id`
* `core_ir_artifact_id`
* `bridge_manifest_hash`
* artifact refs

Key governance:

* integrity policy/conflict families
* advice/trust packet linkage
* occasional `advisory_only` posture in brokered reflexive forms

### Commitments lineage

Maps to:

* carrier: `StructuralModel`
* lineage overlay: `CoreStructuralIntegrity` sublineage

Key anchors:

* `source_set`
* `module_id/hash`
* `arc_id`

Key governance:

* locks
* evidence requirements
* declared effects
* compiler/diagnostics tie-in

### Policy/runtime/evidence lineage

Maps to:

* carriers: `ContractGate`, `CuratedSet`, `TraceRecord`, `Adjudication`
* lineage overlay: `PolicyRuntime`

Key anchors:

* `policy_hash`
* `schema_id`
* `profile_id`
* `activation_seq`
* `request_payload_hash`
* `request_hash/formula_hash`

Key governance:

* rules / lemma packs
* matched-rule reasoning
* required approval / decision code
* incident redaction policy

### Legacy IR / validator / puzzle lineage

Maps to:

* carriers: `StructuralModel`, `IntakeFrame`, `Adjudication`
* lineage overlay: `LegacyIRValidator`

Key anchors:

* `ir_id`
* `proof_id`
* `puzzle_id`
* `request_hash`
* `formula_hash`
* `proof_hash`

Residual note:

* this is the clearest drift stratum:
  weaker discriminator discipline, more open maps, older channel/solver grammar

---

## 10. Lean-oriented notes

### Stable data structures

These look formalizable now:

* `ArtifactCore`
* carrier overlay inductive
* lineage overlay record/typeclass
* named anchor slots
* closed local record/enum defs
* sequence structures:
  steps, edges, gates, checkpoints
* collection structures:
  manifests, bundles, registries
* graph/model structures:
  nodes, edges, channels, projections
* adjudication structures:
  findings, checks, severity counts, judgments

### Predicates / invariants / proof obligations

These look like the real ADEU formal layer:

* reference existence and resolution
* hash binding consistency
* schema discriminator consistency
* canonical order preservation
* source precedence and no retrospective swap
* authority non-escalation / no authority minting
* settlement carry preservation
* request/receipt/result identity-chain coherence
* evidence-anchor completeness
* monotonic trace / no post-hoc reconstruction
* no hidden branch logic
* no visual authority inflation
* deterministic/advisory boundary preservation

Those are exactly the kinds of obligations already hinted by the schema corpus and made explicit by ARC rejection fixtures.

### Too procedural or contextual to formalize cleanly yet

These should stay outside the first Lean layer for now:

* free-form summaries, notes, rationales
* raw oracle output text
* advisories and human escalation notes
* open `metadata`/`details`/`options` maps
* embedded policy JSON blobs not yet normalized

### Suggested next formal moves

1. Define `ArtifactCore`, `CarrierOverlay`, and `LineageOverlay` in Lean.
2. Build a small registry proving where each concrete schema lands.
3. Start with a benchmark subset:

   * `adeu_arc_task_packet`
   * `adeu_architecture_analysis_request`
   * `meta_loop_sequence_contract`
   * `ux_interaction_contract`
   * `adeu_core_ir`
   * `policy_registry`
4. Lift the existing rejection semantics into predicates:

   * no authority laundering
   * no settlement erasure
   * no hidden branching
   * no post-hoc reconstruction
   * no retroactive selection swap
5. Normalize the legacy stratum later, rather than forcing it into the first clean core.

The main takeaway is:

**The corpus already evidences ADEU as a governed artifact calculus.**
What is stable is the **envelope**.
What varies is the **carrier** and the **lineage vocabulary**.
So the right self-description layer is **core envelope + carrier overlay + lineage overlay**, with explicit residuals where the repo has genuinely not converged yet.
