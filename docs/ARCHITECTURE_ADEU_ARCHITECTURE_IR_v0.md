# ADEU Architecture Semantic IR (ASIR) - High-Level Design Spec

**Status:** working draft snapshot - 2026-03-23
**Scope:** proposed ADEU Studio module for architecture-intent compilation
**Method:** repo-native extension of the ADEU semantic compiler lane, the V36 UX IR/compiler family, and the V39-E hybrid checkpoint/oracle lane

---

## 1. Direct Answer to the Problem

The missing layer is not "more agent scaffolding." It is a **typed, governed intermediate representation for architecture semantics**.

Standard agents fail at architecture because they are being asked to do two jobs in one opaque step:

1. infer the intended world hidden inside an ambiguous human brief;
2. compile a concrete architecture inside that inferred world.

Those are different phases and must be separated.

The correct solution is:

- compile human briefs into a first-class **Architecture Semantic IR**;
- make the inferred world explicit before any UI tree, API surface, workflow, or schema is emitted;
- let LLM agents operate only as **advisory world-hypothesis generators** and bounded ambiguity oracles;
- keep final typing, normalization, conflict checking, authority enforcement, projection, and release gating under **deterministic script ownership**.

In compiler terms:

```text
brief / intent / repo context
    -> semantic-source normalization
    -> architecture intent packet
    -> candidate world hypotheses
    -> deterministic adjudication
    -> Architecture Semantic IR
    -> deterministic projections
    -> implementation-ready artifacts
```

That is the missing IR.

---

## 2. Repo-Native Design Thesis

This module should not be introduced as an alien subsystem. ADEU Studio already has the relevant substrate.

As of **March 23, 2026**, the latest completed in-tree hybrid execution arc is **`vNext+76`**, recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS76.md`. Its core law is the right precedent for architecture work:

- deterministic code classifies checkpoints first;
- the coding agent is advisory only;
- oracle output is typed, replay-pinned, and bounded;
- final adjudication remains deterministic;
- unresolved or contradictory outcomes fail closed into escalation.

Earlier ADEU Studio work already established the complementary UI-side rule:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md` and the `v61` to `v65` UX governance family explicitly froze that **no direct brief-to-code path is valid without IR**;
- `ux_domain_packet@1`, `ux_morph_ir@1`, `ux_surface_projection@1`, and `ux_surface_compiler_export@1` proved the repo can make open-ended product design legible as typed intermediate artifacts before implementation.

ASIR is the architecture-level generalization of those ideas:

- broader than `ux_morph_ir@1`, because it covers services, workflows, trust boundaries, capabilities, evidence, and utility tradeoffs;
- more specific than `adeu_core_ir@0.1`, because it introduces architecture-native primitives instead of forcing all architecture intent into a generic graph too early;
- downstream-compatible with `adeu_core_ir@0.1`, because ASIR should lower into O/E/D/U projections for shared integrity diagnostics.

---

## 3. Proposed Module Family

### 3.1 Proposed package boundaries

| Package | Responsibility |
|---|---|
| `packages/adeu_architecture_ir` | Typed ASIR models, canonicalization, schema export, reason codes |
| `packages/adeu_architecture_compiler` | Deterministic compilation, validation, hybrid checkpoint/oracle adjudication, projection |
| `apps/api` integration | Read/compile/project endpoints over typed architecture artifacts |
| `apps/web` integration | Artifact inspection, ambiguity review, projection review, evidence-first architecture workbench |

### 3.2 Why a new package family is justified

`adeu_commitments_ir` is about governance locks and compiler commitments.

`adeu_core_ir` is a generic O/E/D/U graph with strong integrity laws.

`ux_morph_ir@1` is a bounded surface-planning IR for one UI family.

Architecture planning needs additional first-class objects that none of those own directly:

- actors and roles;
- services and bounded contexts;
- trust and authority boundaries;
- capabilities and allowed actions;
- workflows and state transitions;
- evidence-before-commit requirements;
- ambiguity registers and hidden-assumption coverage;
- projection contracts for UI, API, workflow, event, storage, and test surfaces.

That requires a domain IR, not just another prompt template.

---

## 4. Proposed Artifact Family

### 4.1 Canonical artifacts

| Artifact | Purpose |
|---|---|
| `adeu_architecture_intent_packet@1` | Structured normalized input packet for one architecture brief |
| `adeu_architecture_ontology_frame@1` | Deterministic intermediate inventory of entities, boundaries, decisions, workflows, and failure surfaces |
| `adeu_architecture_boundary_graph@1` | Compiled cross-boundary interaction graph used for trust, authority, and sensitivity checks |
| `adeu_architecture_world_hypothesis@1` | Candidate agent-produced semantic world model, advisory only |
| `adeu_architecture_semantic_ir@1` | Canonical compiled architecture meaning artifact |
| `adeu_architecture_ir_delta@1` | Typed proposed semantic patch used only in bounded oracle-assisted repair |
| `adeu_architecture_projection_bundle@1` | Deterministic lowerings to implementation-facing surfaces |
| `adeu_architecture_projection_manifest@1` | Deterministic map from ASIR units to emitted surfaces, artifacts, and target files |
| `adeu_architecture_conformance_report@1` | Deterministic validator output and readiness classification |
| `adeu_architecture_oracle_request@1` | Bounded ambiguity question packet |
| `adeu_architecture_oracle_resolution@1` | Advisory oracle answer packet |
| `adeu_architecture_checkpoint_trace@1` | Canonical hybrid checkpoint and final adjudication trace |
| `adeu_architecture_variant_manifest@1` | Candidate-world comparison and selection record |

### 4.2 Internal compiler ladder

The artifact family should preserve the same structural order as the reasoning process that produces it.

Recommended internal ladder:

```text
adeu_architecture_intent_packet@1
    -> adeu_architecture_ontology_frame@1
    -> adeu_architecture_boundary_graph@1
    -> adeu_architecture_world_hypothesis@1
    -> adeu_architecture_semantic_ir@1
    -> adeu_architecture_checkpoint_trace@1
    -> adeu_architecture_projection_bundle@1
    -> adeu_architecture_projection_manifest@1
    -> adeu_architecture_conformance_report@1
```

This ordering matters because it preserves the same staged compilation order:

- intent before ontology;
- ontology before projection;
- ambiguity disposition before implementation readiness;
- projection before emitted-surface accounting.

### 4.3 Artifact placement

Recommended repo layout:

```text
packages/adeu_architecture_ir/
packages/adeu_architecture_compiler/
spec/adeu_architecture_*.schema.json
artifacts/architecture/<arc>/
docs/generated/architecture/<arc>/
apps/api/fixtures/architecture/<arc>/
```

### 4.4 Authority policy object

Every architecture artifact in the family should carry the same frozen authority boundary policy:

```json
{
  "no_direct_brief_to_codegen": true,
  "projections_may_express_but_may_not_mint_authority": true,
  "deterministic_adjudicator_authoritative": true,
  "oracle_output_advisory_only": true,
  "fail_closed_on_high_impact_ambiguity": true
}
```

This is the architecture analogue of:

- `no_free_form_ui_codegen_without_ir`;
- `ui_artifacts_may_express_but_may_not_mint_authority`;
- the `v76` anti-authorship and advisory-only hybrid law.

---

## 5. Control Plane and Pipeline

### 5.1 End-to-end pipeline

1. **Intent capture**
   - The source brief is normalized into `adeu_architecture_intent_packet@1`.
   - Inputs are repo-relative, hash-bound, and explicitly typed.
2. **Deterministic extraction**
   - Existing structured facts are harvested from semantic markdown blocks, lock docs, repo topology scans, policy files, and any already-accepted ADEU artifacts.
3. **Candidate world hypotheses**
   - One or more LLM-generated `adeu_architecture_world_hypothesis@1` candidates are produced.
   - These remain advisory only.
4. **Deterministic adjudication**
   - Candidates are schema-validated, coverage-scored, boundary-checked, and compared.
   - The compiler either composes a canonical ASIR, emits hybrid checkpoints, or fails closed.
5. **ASIR emission**
   - `adeu_architecture_semantic_ir@1` becomes the authoritative artifact for the brief.
6. **Deterministic projections**
   - ASIR lowers into implementation-facing projections and ADEU-native downstream artifacts.
7. **Conformance and evidence**
   - The compiler emits a conformance report, checkpoint trace, artifact hashes, and evidence manifest.

Hard rule:

- no projection or downstream implementation artifact may be emitted as compile-ready unless a canonical `adeu_architecture_semantic_ir@1` exists and its conformance state is pass-gated.

### 5.2 Internal artifact ladder

The compiler should materialize intermediate artifacts explicitly rather than hiding them inside one opaque compile step.

Recommended sequence:

1. `adeu_architecture_intent_packet@1`
2. `adeu_architecture_ontology_frame@1`
3. `adeu_architecture_boundary_graph@1`
4. one or more advisory `adeu_architecture_world_hypothesis@1` candidates
5. canonical `adeu_architecture_semantic_ir@1`
6. `adeu_architecture_checkpoint_trace@1`
7. `adeu_architecture_projection_bundle@1`
8. `adeu_architecture_projection_manifest@1`
9. `adeu_architecture_conformance_report@1`

This ladder is worth making explicit because it gives later review surfaces a place to detect semantic drift before it is buried inside code generation.

### 5.3 Optional BO4 compatibility

This module should support the repo's existing hybrid variant discipline instead of bypassing it.

This compatibility is not part of the `v1` minimal contract. The first lock should permit ASIR to interoperate with BO4-style semantic variant search without requiring that lane for baseline validity.

The right BO4 object is not "four code diffs." It is:

- four candidate `adeu_architecture_world_hypothesis@1` payloads;
- deterministic meta review over ambiguity coverage, boundary completeness, deontic integrity, utility explicitness, and projection readiness;
- one accepted variant manifest binding the winning hypothesis lineage into the final ASIR.

That keeps variant search in the semantic layer rather than in the codegen layer.

### 5.4 Compiler pass outline

Recommended deterministic pass sequence:

1. `LoadIntentPacket`
2. `NormalizeAuthorityInputs`
3. `ExtractStructuredFacts`
4. `ValidateWorldHypotheses`
5. `AssembleOntology`
6. `ResolveEpistemicGaps`
7. `AssembleDeontics`
8. `AssembleUtility`
9. `RunArchitectureIntegrityLints`
10. `LowerToAdeuCoreIR`
11. `ProjectImplementationSurfaces`
12. `EmitCheckpointTrace`
13. `EmitConformanceReport`
14. `EmitEvidenceManifest`

Only steps 3 and 4 consume agent output. No step delegates final authority.

### 5.5 Phase-Boundary Mapping

This module should align explicitly to the existing `meta_loop_sequence_contract@1` phase vocabulary rather than inventing an unrelated lifecycle.

| Meta-loop phase | ASIR responsibility |
|---|---|
| `intent_interpretation` | build `adeu_architecture_intent_packet@1` and advisory world hypotheses |
| `pre_generation_validation` | construct ontology/boundary artifacts, assemble ASIR, classify checkpoints, run architecture validators |
| `artifact_generation` | emit projection bundle and projection manifest from pass-gated ASIR |
| `post_generation_validation` | emit conformance report and downstream validator outputs over projected artifacts |
| `evidence_gate` | hash-bind artifacts, manifests, traces, and reference inputs |
| `operator_gate` | receive any human escalation or final bounded approval surface |

---

## 6. ASIR Root Contract

### 6.1 Proposed root schema

`adeu_architecture_semantic_ir@1`

### 6.2 Proposed root fields

| Field | Type | Meaning |
|---|---|---|
| `schema` | const | `adeu_architecture_semantic_ir@1` |
| `architecture_id` | string | Stable human-readable artifact id |
| `intent_packet_id` | string | Bound source packet id |
| `semantic_hash` | sha256 hex | Hash of canonical ASIR payload |
| `compiler` | object | Compiler name, version, pass versions, config hash |
| `authority_boundary_policy` | object | Frozen authority law |
| `source_set` | object | Repo-relative source refs and hashes |
| `variant_lineage` | object | Accepted candidate ancestry |
| `ontology` | object | Architecture-world entities and relations |
| `epistemics` | object | Facts, assumptions, ambiguities, evidence |
| `deontics` | object | Obligations, prohibitions, permissions, gates, invariants |
| `utility` | object | Goals, metrics, priorities, tradeoffs |

### 6.3 Root boundary and validation geometry

The ASIR root stops at architecture meaning. It is not the place where downstream projection, hybrid trace state, or readiness summaries accumulate.

Those later pipeline surfaces belong to sibling artifacts:

- `adeu_architecture_checkpoint_trace@1` for checkpoint classes and final adjudication;
- `adeu_architecture_projection_bundle@1` for emitted lowerings;
- `adeu_architecture_projection_manifest@1` for semantic-to-surface lineage;
- `adeu_architecture_conformance_report@1` for compile-readiness, blocking refs, and validator findings.

Validation should therefore happen in two explicit layers:

1. staged section-local validation during assembly
   - ontology closure, reference shape, and graph reachability;
   - epistemic provenance, impact typing, and ambiguity route legality;
   - deontic authority-source and invariant shape checks;
   - utility goal, metric, and tradeoff shape checks.
2. one whole-ASIR integrity pass after all sections are assembled
   - cross-section closure between ontology, epistemics, deontics, and utility;
   - enforcement of ontology laws that depend on `gate`, `evidence_requirement`, or authority provenance;
   - checkpoint classification preconditions;
   - projection gating eligibility.

No projection or readiness claim may be emitted before the whole-ASIR integrity pass completes successfully or legally fails into checkpoint escalation.

### 6.4 Root invariants

The root object must fail closed unless all of the following hold:

- every referenced id resolves within the semantic root;
- `semantic_hash` matches the canonical payload bytes;
- every source path is repo-relative and hash-bound;
- authority policy matches the frozen architecture authority policy exactly;
- ontology, epistemics, deontics, and utility sections are each present, even if empty;
- every ambiguity entry has an explicit `impact_class` and `resolution_route`;
- no downstream readiness, checkpoint-trace, or emitted-surface summary fields are stored in the root.

---

## 7. ASIR Ontology Specification

### 7.1 Ontology purpose

The ontology layer captures what exists in the intended architecture before implementation:

- actors;
- systems;
- surfaces;
- data objects;
- boundaries;
- capabilities;
- workflows;
- states;
- decisions;
- failure modes.

### 7.2 Required ontology primitives

| Primitive | Required fields | Notes |
|---|---|---|
| `actor` | `actor_id`, `kind`, `label`, `trust_domain`, `authority_level` | `kind` example values: `human_role`, `external_system`, `internal_service`, `policy_engine` |
| `surface` | `surface_id`, `kind`, `owner_ref`, `authority_posture`, `exposed_actions[]` | `kind` example values: `ui`, `api`, `queue`, `job`, `storage`, `policy`, `event_stream` |
| `data_object` | `object_id`, `label`, `sensitivity_class`, `source_of_truth_ref` | Used for trust and evidence requirements |
| `boundary` | `boundary_id`, `from_ref`, `to_ref`, `boundary_class`, `auth_required`, `audit_required` | `boundary_class` example values: `trust`, `authority`, `data_sensitivity`, `organizational`, `execution` |
| `capability` | `capability_id`, `subject_ref`, `action`, `resource_ref`, `granted_by_ref` | Expresses allowed action semantics before implementation |
| `workflow` | `workflow_id`, `entry_ref`, `step_refs[]`, `terminal_state_refs[]` | Top-level flow container |
| `flow_step` | `step_id`, `kind`, `actor_ref`, `surface_ref`, `inputs[]`, `outputs[]`, `preconditions[]`, `postconditions[]` | Deterministic execution skeleton |
| `state` | `state_id`, `workflow_id`, `state_kind`, `terminal` | State machine backbone |
| `transition` | `transition_id`, `from_state_ref`, `to_state_ref`, `trigger_ref`, `guard_refs[]` | Enables reachability and dead-end checks |
| `decision` | `decision_id`, `decider_ref`, `authority_source_ref`, `evidence_required_refs[]`, `ambiguity_default` | Explicitly separates authority from UI or prose emphasis |
| `failure_mode` | `failure_mode_id`, `affected_refs[]`, `default_disposition`, `observable_surface_ref` | Required for fail-closed behavior |

### 7.3 Ontology laws

- section-local ontology checks may run during ontology assembly, but any law that references `gate`, `evidence_requirement`, or authority provenance is enforced only in the whole-ASIR integrity pass;
- every cross-boundary `flow_step` must reference a `boundary`;
- every `decision` must resolve to an authority source outside surface styling or route-local convenience;
- every authoritative surface action must map to at least one `capability` and one `gate`;
- every workflow must have at least one terminal state;
- every terminal state must have an observable surface or event consequence;
- every state-bearing workflow or authority-bearing decision path must bind to at least one declared `failure_mode`;
- every `data_object` with non-public sensitivity must cross only through declared boundaries.

## 8. ASIR Epistemics Specification

### 8.1 Epistemic purpose

The epistemic layer captures what is known, what is assumed, what is unclear, and what evidence is required before the architecture can safely project into implementation.

### 8.2 Required epistemic primitives

| Primitive | Required fields | Notes |
|---|---|---|
| `source_ref` | `source_ref_id`, `source_kind`, `location`, `verbatim_excerpt?`, `inference_rationale?` | Universal provenance object for all semantically meaningful architecture claims |
| `epistemic_annotation` | `annotation_id`, `subject_ref`, `confidence_kind`, `evaluable_as` | Used only when confidence or evaluability must be attached to a non-epistemic subject ref |
| `fact` | `fact_id`, `statement`, `source_refs[]`, `confidence_kind`, `evaluable_as` | Derived from explicit authority inputs |
| `assumption` | `assumption_id`, `statement`, `impact_class`, `touches_refs[]`, `confidence_kind` | Explicit hidden-world assumption |
| `ambiguity` | `ambiguity_id`, `question`, `impact_class`, `touches_refs[]`, `resolution_route`, `evaluable_as` | Central object for hybrid adjudication |
| `evidence_requirement` | `evidence_id`, `required_before_refs[]`, `evidence_kind`, `source_policy` | Mirrors ADEU evidence-first discipline |
| `observability_hook` | `hook_id`, `subject_ref`, `observable_kind`, `required_for_metrics[]` | Used for future runtime verification |
| `hypothesis_binding` | `candidate_id`, `accepted`, `coverage_summary`, `rejection_reasons[]` | Records lineage from advisory candidates |

Frozen starter annotation values:

- `confidence_kind`: `explicit`, `strongly_implied`, `weakly_implied`
- `evaluable_as`: `deterministic`, `contextual`, `semantic`

### 8.3 Epistemic attachment rules

Confidence and evaluability are not free-floating primitives in `v1`.

They must appear in exactly one of these forms:

- as direct fields on `fact`, `assumption`, or `ambiguity`;
- as an `epistemic_annotation` attached to some other subject ref such as an ontology node, deontic node, or utility node.

Detached posture objects with no `subject_ref` target are illegal.

### 8.4 Epistemic laws

- every `fact` must bind to at least one repo-relative or artifact-relative source;
- every architecture node participating in a decision, gate, invariant, capability, projection unit, or checkpoint must be traceable to one or more `source_ref` values directly or through an explicit derivation relation;
- nodes with `confidence_kind = weakly_implied` must not be the sole support for irreversible, authority-bearing, or fail-closed behavior without checkpoint adjudication;
- any subject marked `evaluable_as = semantic` must not be claimed as deterministically validated;
- every `assumption` must declare `impact_class` and `touches_refs[]`;
- every `ambiguity` must declare exactly one `resolution_route`;
- any ambiguity touching an authority boundary, destructive action, external trust boundary, or legal/compliance surface is at least `high` impact;
- any `high` or `critical` ambiguity blocks direct projection unless checkpoint adjudication resolves it or escalates it fail-closed;
- evidence requirements for authoritative decisions must be explicit and reachable before commit.

### 8.5 Impact class vocabulary

Frozen starter vocabulary:

- `low`
- `medium`
- `high`
- `critical`

### 8.6 Resolution route vocabulary

Frozen starter vocabulary:

- `deterministic_only`
- `oracle_assisted`
- `human_only`

---

## 9. ASIR Deontics Specification

### 9.1 Deontic purpose

The deontic layer captures what the architecture must do, must not do, may do, and how decisions are gated.

### 9.2 Required deontic primitives

| Primitive | Required fields | Notes |
|---|---|---|
| `obligation` | `obligation_id`, `statement`, `target_refs[]`, `condition` | Positive required behavior |
| `prohibition` | `prohibition_id`, `statement`, `target_refs[]`, `condition` | Forbidden behavior |
| `permission` | `permission_id`, `statement`, `target_refs[]`, `condition` | Allowed but not required |
| `gate` | `gate_id`, `subject_ref`, `authority_source_ref`, `required_refs[]`, `fail_closed` | Explicit authority and evidence gate |
| `invariant` | `invariant_id`, `statement`, `scope_refs[]`, `severity` | Non-negotiable architecture law |
| `escalation_rule` | `rule_id`, `trigger_refs[]`, `escalate_to`, `default_disposition` | Human escalation law |

### 9.3 Frozen starter invariants

The first ASIR baseline should carry these invariant classes explicitly:

1. `no_surface_mints_authority`
2. `evidence_before_authoritative_commit`
3. `cross_boundary_actions_are_authenticated`
4. `cross_boundary_actions_are_auditable`
5. `ambiguity_on_high_impact_surface_fails_closed`
6. `policy_authority_outranks_ui_convenience`

### 9.4 Deontic laws

- every authoritative action must be guarded by at least one `gate`;
- every `gate` must resolve to an authority source outside the rendering layer;
- every irreversible or destructive action must require explicit evidence;
- no permission may contradict a prohibition at the same priority level without an explicit exception path;
- no projection may weaken an invariant by omission.

---

## 10. ASIR Utility Specification

### 10.1 Utility purpose

The utility layer prevents the architecture compiler from pretending that goals are self-evident. The brief's tradeoffs must be explicit.

### 10.2 Required utility primitives

| Primitive | Required fields | Notes |
|---|---|---|
| `goal` | `goal_id`, `statement`, `served_by_refs[]` | Human-declared or compiler-normalized outcome |
| `metric` | `metric_id`, `label`, `target_expression`, `measured_by_refs[]` | Implementation-facing success test |
| `priority_rule` | `priority_id`, `higher_ref`, `lower_ref`, `condition` | Makes tradeoffs executable |
| `tradeoff` | `tradeoff_id`, `between_refs[]`, `adjudication_rule` | Explicit conflict model |

### 10.3 Utility laws

- every architecture must declare at least one goal;
- every goal that can conflict with another goal must either have a priority rule or be emitted as unresolved utility ambiguity;
- every metric must bind to at least one observability hook or evidence requirement;
- utility cannot silently override deontic invariants.

---

## 11. Projection Surfaces and Derived Artifacts

### 11.1 Projection purpose

ASIR is not itself code. It is the authoritative architecture meaning layer from which narrower projections can be derived.

Projection policy is derived from the accepted source scope and compiler configuration. It is not stored as mutable state inside the semantic root.

### 11.2 Projection targets

`v1` minimal contract:

- `adeu_core_ir`

`v1` compatible but non-baseline target families:

- `ux_domain_packet`
- `ux_morph_ir`

Future-compatible target families outside the `v1` minimal lock:

- `api_contract`
- `workflow_contract`
- `event_contract`
- `test_obligation_bundle`

### 11.3 Projection unit shape

Each `projection_unit` should include:

- `projection_id`
- `target_family`
- `source_refs[]`
- `readiness`
- `blocked_by_ambiguity_refs[]`
- `output_artifact_refs[]`
- `compiler_entrypoint`

### 11.4 Projection manifest

The compiler should emit a first-class `adeu_architecture_projection_manifest@1` artifact.

Its job is to make the lowering relation inspectable:

- which ASIR refs were consumed by each emitted projection unit;
- which target surfaces were emitted;
- which files, routes, schemas, or artifacts were touched;
- which ambiguity or gate constraints remained blocking;
- which compiler entrypoint and version materialized the output.

This prevents "ghost structure" drift where implementation surfaces appear without a clean semantic lineage back to the governing IR.

### 11.5 Conformance report

The compiler should emit a first-class `adeu_architecture_conformance_report@1` artifact separate from the ASIR root.

Its job is to carry downstream readiness state:

- `projection_readiness`
- blocking ambiguity refs
- failed validator check ids
- scope-bound emitted artifact refs
- any required human escalation surface

Final adjudication in the checkpoint trace and compile readiness in the conformance report must remain distinct. `resolved_pass` is not itself permission to claim emitted surfaces are ready; readiness belongs to deterministic post-projection validation.

### 11.6 Lowering rules

#### Lowering to `adeu_core_ir@0.1`

- ontology objects lower into `O` nodes;
- facts, assumptions, ambiguities, and evidence requirements lower into `E` nodes;
- obligations, prohibitions, permissions, gates, invariants, and escalation rules lower into `D` nodes;
- goals, metrics, and priorities lower into `U` nodes.

Recommended edge use:

- `depends_on` for workflow and evidence dependencies;
- `gates` for authority and precondition constraints;
- `serves_goal` for mapping obligations or claims to utility;
- `prioritizes` for explicit utility ordering;
- `justifies` for evidence and fact support into policy nodes.

#### Lowering to UX artifacts

ASIR should not emit React trees directly.

This lowering family is compatible with ASIR but is not required for the `v1` minimal lock.

The correct lowering is:

```text
ASIR
    -> bounded surface family selection
    -> ux_domain_packet@1
    -> ux_morph_ir@1
    -> ux_surface_projection@1
    -> ux_interaction_contract@1
    -> bounded surface compiler export
```

That preserves the existing ADEU Studio principle that UI is projected from typed intent, not generated from prose.

---

## 12. Deterministic Validator Suite

### 12.1 Validator classes

Recommended deterministic validator families:

| Family | Purpose |
|---|---|
| Input and source validators | path policy, hash binding, schema integrity |
| Ontology integrity validators | id uniqueness, reference closure, state reachability |
| Boundary validators | trust-boundary, authority-boundary, sensitivity-boundary coverage |
| Deontic validators | authority-source integrity, invariant preservation, conflict detection |
| Utility validators | missing priorities, metric without observability, hidden tradeoffs |
| Ambiguity validators | impact classification, route legality, fail-closed enforcement |
| Projection validators | target-family readiness and blocked-surface honesty |
| Hybrid validators | replay identity, advisory-only boundary, transition-law enforcement |

### 12.2 Mandatory fail-closed checks

The first release should fail closed on at least these conditions:

1. A cross-boundary step has no declared boundary.
2. An authoritative decision has no `authority_source_ref`.
3. A required evidence-before-commit rule is absent.
4. A `high` or `critical` ambiguity touches a projected surface without checkpoint disposition.
5. A projection unit claims readiness while blocked by unresolved ambiguity.
6. A surface implies stronger authority than the governing capability or gate permits.
7. An oracle resolution attempts to introduce new authority, new boundary classifications, or new scope.

### 12.3 Check-ID structure

The validator suite should expose stable semantic check ids, separate from broader compiler or runtime diagnostics.

Recommended families:

- `ASIR-O-xxx` for ontology and structure
- `ASIR-E-xxx` for epistemics, provenance, confidence, and evaluability
- `ASIR-D-xxx` for authority, invariants, and deontic integrity
- `ASIR-U-xxx` for utility, metric, and tradeoff integrity
- `ASIR-P-xxx` for projection honesty and manifest integrity
- `ASIR-H-xxx` for hybrid checkpoint, replay identity, and oracle boundary checks

These check ids should then map into emitted diagnostic artifacts and conformance reports.

### 12.4 Suggested diagnostic family

Recommended stable reason-code families:

- `AAC1xxx` input and source diagnostics
- `AAC2xxx` ontology and graph diagnostics
- `AAC3xxx` epistemic and ambiguity diagnostics
- `AAC4xxx` deontic and authority diagnostics
- `AAC5xxx` projection and conformance diagnostics
- `AAC6xxx` hybrid oracle and checkpoint diagnostics

### 12.5 Formal Kernel Boundary

ASIR has a bounded finite-law subset that is suitable for formal proof mirrors in Lean.

The right target is not the whole compiler. The right target is the finite surface where:

- vocabularies are frozen;
- transition tables are exact;
- gating predicates are small and enumerable;
- downstream validators can mirror the same law without reinterpreting prose.

The initial ASIR formal-kernel candidates are:

- primitive-to-lane and artifact-marker separation for AAL vocabulary;
- checkpoint-class and final-adjudication transition law;
- route/checkpoint/oracle-emission compatibility;
- projection-readiness gating from ambiguity severity and status;
- adjudication-to-readiness connector law between hybrid outcomes and projection gating.

These kernels should remain explicitly bounded:

- they are proof mirrors for frozen finite laws, not the authority over the full ASIR compiler;
- they do not replace deterministic validators, schema exports, or artifact-level conformance checks;
- downstream Python or JSON mirrors inherit the Lean law only to the extent that the mirroring path is itself exact and trusted.

Current working formal notes live under:

- `docs/formal/asir/ASIR_FORMAL_KERNEL.md`
- `docs/formal/asir/ASIRKernelHybrid.md`
- `docs/formal/asir/ASIRKernelGating.md`
- `docs/formal/asir/ASIRKernelConnector.md`

The first ASIR family should therefore treat the formal lane as a sidecar proof surface for already-frozen law slices, not as a blocking prerequisite for every implementation slice.

---

## 13. Hybrid Checkpoint and Oracle Lane

### 13.1 Why ASIR needs the hybrid lane

Architecture work inevitably encounters bounded semantic questions that cannot be resolved from explicit sources alone.

Examples:

- Does "frictionless" mean fewer approvals, fewer clicks, or fewer context switches?
- Is the approval actor a policy role, a manager, or a delegated service account?
- Does "trust-sensitive" imply same-context evidence visibility, dual control, or strict audit prominence?

Those questions should not be answered by silently mutating code generation. They should be turned into typed checkpoints.

### 13.2 Checkpoint class vocabulary

Frozen starter vocabulary:

- `deterministic_pass`
- `deterministic_fail`
- `oracle_needed`
- `human_needed`

### 13.3 Final adjudication vocabulary

Frozen starter vocabulary:

- `resolved_pass`
- `resolved_fail`
- `escalated_human`

Compile readiness is reported separately in `adeu_architecture_conformance_report@1`.

### 13.4 Transition law

Frozen starter transition law:

- `deterministic_pass -> resolved_pass`
- `deterministic_fail -> resolved_fail`
- `oracle_needed -> resolved_pass | resolved_fail | escalated_human`
- `human_needed -> escalated_human`

No other transition is legal in v1.

### 13.5 Oracle request law

`adeu_architecture_oracle_request@1` should:

- bind one request to one exact ambiguity or checkpoint;
- be emitted only when `checkpoint_class = oracle_needed`;
- carry replay identity pinned to:
  - `intent_packet_hash`
  - `asir_draft_hash`
  - `policy_source_hashes[]`
  - `model_id`
  - `model_version`
  - `reasoning_effort`
  - `prompt_template_version`
  - `compiler_version`
- carry only bounded local context;
- forbid repo mutation instructions, hidden tool grants, or live network state as canonical evidence.

### 13.6 Oracle resolution law

`adeu_architecture_oracle_resolution@1` should:

- bind one resolution to one exact request;
- record model id, model version, reasoning effort, and raw-output hash;
- record one of:
  - `advisory_support`
  - `advisory_reject`
  - `inconclusive`
  - `contradictory`
- remain advisory only;
- never mint new authority, new capability, new boundary class, or new scope;
- fail closed into escalation on contradiction or replay-identity mismatch.

### 13.7 Typed repair delta law

`adeu_architecture_ir_delta@1` should be the only legal repair-shaped output that an oracle-assisted path can propose.

It should obey these laws:

- it may propose edits only against already-existing ASIR refs or against explicitly pre-authorized placeholder refs;
- it may not widen scope beyond the current architecture unit;
- it may not introduce fresh authority sources, fresh capability grants, or fresh trust-boundary classes without human escalation;
- it may not bypass invariant or checkpoint evaluation;
- it becomes effective only after deterministic revalidation of the full candidate ASIR.

If applying an `adeu_architecture_ir_delta@1` introduces new failures or unresolved high-impact ambiguity, the delta is rejected and the checkpoint fails closed.

### 13.8 Deterministic checkpoint classifier

Recommended starter classifier:

```text
if ambiguity.resolution_route == human_only:
    checkpoint_class = human_needed
elif ambiguity.touches_authority_boundary and missing_authority_source:
    checkpoint_class = human_needed
elif ambiguity.touches_irreversible_action and missing_evidence_rule:
    checkpoint_class = human_needed
elif ambiguity.resolution_route == oracle_assisted and ambiguity.impact_class in {high, critical} and bounded_context_complete:
    checkpoint_class = oracle_needed
elif ambiguity.resolution_route == deterministic_only and ambiguity.impact_class in {low, medium} and safe_default_exists:
    checkpoint_class = deterministic_pass
else:
    checkpoint_class = deterministic_fail
```

### 13.9 Borrowed V76 laws that should be preserved

- deterministic adjudicator authoritative;
- oracle output advisory only;
- exact policy-source-set pinning;
- bounded context exact-match requirement;
- one oracle round trip per checkpoint in v1;
- contradictory or unstable resolution fails closed to human escalation.

---

## 14. ADEU Native Pseudo-Language

### 14.1 Purpose

The pseudo-language is not a user-facing implementation language. It is a high-level semantic notation for ASIR authoring, inspection, and deterministic lowering.

Name:

- **AAL**: `ADEU Architecture Language`

Suggested fence label:

- ```` `adeu.architecture_ir` ````

### 14.2 Core block structure

```text
ARCHITECTURE <id> {
  SOURCE { ... }
  AUTHORITY_POLICY { ... }
  O { ... }
  E { ... }
  D { ... }
  U { ... }
}

PROJECTION_MANIFEST <id> {
  LOWER { ... }
}

CHECKPOINT_TRACE <id> {
  CHECKPOINT { ... }
}

CONFORMANCE_REPORT <id> {
  STATUS { ... }
}
```

### 14.3 Primitive set

| Primitive | ASIR section | Meaning |
|---|---|---|
| `ACTOR` | O | human or machine participant |
| `SURFACE` | O | UI, API, queue, job, storage, policy, event stream |
| `DATA` | O | architecture-relevant information object |
| `BOUNDARY` | O | trust, authority, sensitivity, organizational, or execution boundary |
| `CAPABILITY` | O | allowed action on a resource by a subject |
| `WORKFLOW` | O | end-to-end flow container |
| `STEP` | O | workflow step |
| `STATE` | O | state machine node |
| `TRANSITION` | O | legal state transition |
| `DECISION` | O + D | authority-bearing choice point |
| `FACT` | E | bound known truth |
| `ANNOTATE` | E | attach confidence and evaluability to a non-epistemic subject ref |
| `ASSUME` | E | explicit hidden-world assumption |
| `AMBIGUITY` | E | unresolved semantic question |
| `EVIDENCE` | E | evidence-before-commit or proof requirement |
| `OBSERVE` | E | observability hook |
| `OBLIGE` | D | required behavior |
| `FORBID` | D | prohibited behavior |
| `PERMIT` | D | permitted behavior |
| `GATE` | D | authority and evidence gate |
| `INVARIANT` | D | fail-closed law |
| `ESCALATE` | D | escalation rule |
| `GOAL` | U | desired outcome |
| `METRIC` | U | measurable success condition |
| `PRIORITY` | U | tradeoff ordering |
| `TRADEOFF` | U | explicit conflict model |
| `LOWER` | PROJECTION_MANIFEST | deterministic projection target |
| `CHECKPOINT` | CHECKPOINT_TRACE | hybrid ambiguity disposition rule |
| `STATUS` | CONFORMANCE_REPORT | deterministic readiness and blocking summary |

### 14.4 Example AAL program

```adeu.architecture_ir
ARCHITECTURE approval_flow_v1 {
  SOURCE {
    BRIEF "frictionless, trust-sensitive approval flow"
    CONTEXT "internal procurement approvals for medium-risk requests"
    HASH brief_sha256 = "<to-be-computed>"
  }

  AUTHORITY_POLICY {
    no_direct_brief_to_codegen = true
    projections_may_express_but_may_not_mint_authority = true
    deterministic_adjudicator_authoritative = true
    oracle_output_advisory_only = true
    fail_closed_on_high_impact_ambiguity = true
  }

  O {
    ACTOR requester kind=human_role trust_domain=external_to_approval authority_level=request_only
    ACTOR approver kind=human_role trust_domain=approval_core authority_level=approve_or_reject
    ACTOR policy_engine kind=policy_engine trust_domain=approval_core authority_level=policy_decide

    SURFACE request_portal kind=ui owner=requester authority_posture=advisory
    SURFACE approval_api kind=api owner=policy_engine authority_posture=authoritative
    SURFACE approval_workbench kind=ui owner=approver authority_posture=authoritative
    SURFACE audit_log kind=event_stream owner=policy_engine authority_posture=authoritative

    DATA approval_request sensitivity_class=internal source_of_truth_ref=approval_api
    DATA approval_decision sensitivity_class=internal source_of_truth_ref=approval_api

    BOUNDARY request_to_core
      from=request_portal
      to=approval_api
      boundary_class=trust
      auth_required=true
      audit_required=true

    CAPABILITY submit_request subject_ref=requester action=create resource_ref=approval_request granted_by_ref=request_portal
    CAPABILITY review_request subject_ref=approver action=review resource_ref=approval_request granted_by_ref=approval_workbench
    CAPABILITY decide_request subject_ref=approver action=approve_or_reject resource_ref=approval_decision granted_by_ref=approval_api

    WORKFLOW approval_path entry_ref=request_portal terminal_state_refs=[approved, rejected, needs_info]

    STEP capture_request actor_ref=requester surface_ref=request_portal inputs=[] outputs=[approval_request]
    STEP validate_identity actor_ref=policy_engine surface_ref=approval_api inputs=[approval_request] outputs=[approval_request]
    STEP evaluate_policy actor_ref=policy_engine surface_ref=approval_api inputs=[approval_request] outputs=[approval_request]
    STEP review_request actor_ref=approver surface_ref=approval_workbench inputs=[approval_request] outputs=[approval_decision]
    STEP emit_audit actor_ref=policy_engine surface_ref=audit_log inputs=[approval_decision] outputs=[]

    STATE draft workflow_id=approval_path state_kind=working terminal=false
    STATE submitted workflow_id=approval_path state_kind=queued terminal=false
    STATE approved workflow_id=approval_path state_kind=success terminal=true
    STATE rejected workflow_id=approval_path state_kind=failure terminal=true
    STATE needs_info workflow_id=approval_path state_kind=waiting terminal=true

    TRANSITION t1 from_state_ref=draft to_state_ref=submitted trigger_ref=capture_request
    TRANSITION t2 from_state_ref=submitted to_state_ref=approved trigger_ref=review_request guard_refs=[gate_decide]
    TRANSITION t3 from_state_ref=submitted to_state_ref=rejected trigger_ref=review_request guard_refs=[gate_decide]

    DECISION decide_outcome
      decider_ref=approver
      authority_source_ref=policy_engine
      evidence_required_refs=[ev_policy_basis, ev_request_context, ev_prior_actions]
      ambiguity_default=fail_closed
  }

  E {
    FACT fact_authority "approval authority is derived from policy_engine plus approver role binding" source_refs=[approval_api] confidence_kind=strongly_implied evaluable_as=contextual
    ASSUME assignee_separation "requester and approver are distinct for medium-risk requests" impact_class=high touches_refs=[review_request, decide_outcome] confidence_kind=weakly_implied

    AMBIGUITY auto_approve_threshold
      question="Are low-risk requests allowed to auto-approve without human review?"
      impact_class=high
      touches_refs=[policy_engine, approval_api, approval_workbench, audit_log]
      resolution_route=oracle_assisted
      evaluable_as=semantic

    EVIDENCE ev_policy_basis required_before_refs=[decide_outcome] evidence_kind=policy_basis source_policy=same_context_visible
    EVIDENCE ev_request_context required_before_refs=[decide_outcome] evidence_kind=request_context source_policy=same_context_visible
    EVIDENCE ev_prior_actions required_before_refs=[decide_outcome] evidence_kind=audit_history source_policy=same_context_visible

    OBSERVE obs_turnaround subject_ref=approval_path observable_kind=latency required_for_metrics=[m_turnaround]
    OBSERVE obs_audit subject_ref=audit_log observable_kind=audit_trace required_for_metrics=[m_audit_coverage]
  }

  D {
    INVARIANT inv_no_surface_mints_authority "no surface may mint approval authority" scope_refs=[request_portal, approval_workbench, approval_api]
    INVARIANT inv_evidence_before_commit "required evidence must be reachable before approve or reject" scope_refs=[approval_workbench, decide_outcome]

    OBLIGE obl_cross_boundary_auth "request_to_core crossing must authenticate requester" target_refs=[request_to_core] condition=always
    OBLIGE obl_cross_boundary_audit "request_to_core crossing must write audit evidence" target_refs=[request_to_core] condition=always
    OBLIGE obl_emit_audit "every terminal decision emits audit event" target_refs=[emit_audit] condition=on_decision

    FORBID fbd_self_approval "requester may not approve own request at medium or higher risk" target_refs=[decide_outcome] condition=risk_gte_medium

    GATE gate_decide
      subject_ref=decide_outcome
      authority_source_ref=policy_engine
      required_refs=[ev_policy_basis, ev_request_context, ev_prior_actions, obs_audit]
      fail_closed=true

    ESCALATE esc_high_ambiguity trigger_refs=[auto_approve_threshold] escalate_to=human_architect default_disposition=escalated_human
  }

  U {
    GOAL g_fast "minimize turnaround time for standard approvals" served_by_refs=[approval_path]
    GOAL g_trust "preserve trust-boundary clarity and auditability" served_by_refs=[gate_decide, emit_audit]

    METRIC m_turnaround label="time_to_decision" target_expression="< 4h for standard cases" measured_by_refs=[obs_turnaround]
    METRIC m_audit_coverage label="audited_decision_rate" target_expression="100%" measured_by_refs=[obs_audit]

    PRIORITY p1 higher_ref=g_trust lower_ref=g_fast condition=authority_or_audit_conflict
    TRADEOFF tr1 between_refs=[g_fast, g_trust] adjudication_rule="optimize speed only within invariant and gate boundaries"
  }
}

PROJECTION_MANIFEST approval_flow_v1_projection {
  LOWER target=adeu_core_ir
}

CHECKPOINT_TRACE approval_flow_v1_trace {
  CHECKPOINT auto_approve_threshold
    checkpoint_class=oracle_needed
    final_adjudication=escalated_human
    rationale="high-impact ambiguity touches authority, audit, and routing of approval decisions"
}

CONFORMANCE_REPORT approval_flow_v1_conformance {
  STATUS projection_readiness=blocked blocking_refs=[auto_approve_threshold] failed_checks=[]
}
```

### 14.5 Semantics of the example

The example does four important things that standard prompt-to-code generation usually does not:

1. It separates the world model from implementation.
2. It makes hidden assumptions and ambiguities explicit.
3. It binds authority to policy and gates instead of to UI emphasis.
4. It blocks implementation-readiness claims until high-impact ambiguity is adjudicated.

That is the essential semantic-control-plane behavior the module exists to provide.

---

## 15. Deterministic Compilation Pseudocode

```text
function compile_architecture(intent_sources):
    intent_packet = build_intent_packet(intent_sources)
    structured_facts = extract_structured_facts(intent_packet)

    advisory_candidates = propose_world_hypotheses(intent_packet, structured_facts)
    valid_candidates = []
    for candidate in advisory_candidates:
        if schema_valid(candidate) and replay_identity_valid(candidate):
            valid_candidates.append(candidate)

    variant_manifest = compare_candidates(valid_candidates, structured_facts)
    winning_candidate = select_best_candidate(variant_manifest)

    draft_asir = assemble_asir(intent_packet, structured_facts, winning_candidate)
    whole_asir_report = run_architecture_integrity_lints(draft_asir)

    checkpoints = classify_ambiguity_checkpoints(draft_asir, whole_asir_report)
    if any(checkpoint.class == human_needed for checkpoint in checkpoints):
        checkpoint_trace = emit_checkpoint_trace(checkpoints)
        conformance_report = emit_blocked_conformance_report(draft_asir, checkpoint_trace, whole_asir_report)
        return emit_artifacts(
            intent_packet,
            variant_manifest,
            draft_asir,
            checkpoint_trace,
            conformance_report,
        )

    oracle_packets = emit_oracle_requests_for(checkpoints where class == oracle_needed)
    oracle_resolutions = collect_bounded_oracle_resolutions(oracle_packets)
    checkpoint_trace = adjudicate_checkpoints(draft_asir, checkpoints, oracle_resolutions)

    if checkpoint_trace.contains(escalated_human):
        conformance_report = emit_blocked_conformance_report(draft_asir, checkpoint_trace, whole_asir_report)
        return emit_artifacts(
            intent_packet,
            variant_manifest,
            draft_asir,
            checkpoint_trace,
            conformance_report,
        )

    final_asir = finalize_asir(draft_asir)
    projection_bundle = project_surfaces(final_asir)
    projection_manifest = build_projection_manifest(final_asir, projection_bundle)
    conformance_report = validate_projection_bundle(
        final_asir,
        checkpoint_trace,
        projection_bundle,
        projection_manifest,
    )

    return emit_artifacts(
        intent_packet,
        variant_manifest,
        final_asir,
        checkpoint_trace,
        projection_bundle,
        projection_manifest,
        conformance_report,
    )
```

Key property:

- the agent contributes candidate hypotheses and bounded oracle answers;
- deterministic code owns final assembly, classification, and projection;
- no direct prompt output becomes architecture truth without typed validation and adjudication.

---

## 16. Suggested Arc Ladder

To keep this repo-native, the module should land as a narrow family of arcs rather than one large feature drop.

### `A1` - ASIR schemas and reference fixture baseline

Deliver:

- `adeu_architecture_intent_packet@1`
- `adeu_architecture_ontology_frame@1`
- `adeu_architecture_boundary_graph@1`
- `adeu_architecture_world_hypothesis@1`
- `adeu_architecture_semantic_ir@1`
- one accepted reference fixture
- schema export and canonicalization tests

Not yet authorized:

- projections
- hybrid oracle lane
- API or web routes

### `A2` - deterministic architecture compiler baseline

Deliver:

- compile entrypoint
- deterministic pass manifest
- architecture integrity lint suite
- explicit section-local plus whole-ASIR integrity passes
- phase-boundary mapping and pass-gated intermediate artifact emission
- conformance report baseline

### `A3` - hybrid ambiguity checkpoint baseline

Deliver:

- `adeu_architecture_oracle_request@1`
- `adeu_architecture_oracle_resolution@1`
- `adeu_architecture_checkpoint_trace@1`
- `adeu_architecture_ir_delta@1`
- replay identity and advisory-only guard suite

This arc should preserve the exact bounded hybrid law from `v76`.

### `A4` - core IR lowering baseline

Deliver:

- lowering from ASIR to `adeu_core_ir@0.1`
- `adeu_architecture_projection_bundle@1`
- `adeu_architecture_projection_manifest@1`
- projection honesty checks

### `A5` - first UX lowering baseline

Deliver:

- lowering from ASIR to `ux_domain_packet@1`
- optional follow-on lowering to `ux_morph_ir@1`
- compatibility checks against the existing UX IR/compiler family

### `A6` - evidence and stop-gate integration

Deliver:

- evidence manifest integration
- stop-gate parity and continuity evidence
- closeout conformance fixtures

---

## 17. Summary

The answer to the original problem is not "build smarter agents." It is:

- give architecture work a real intermediate representation;
- force the hidden world of the brief into explicit typed objects;
- preserve ADEU's O/E/D/U separation;
- keep authority, deontics, and ambiguity legible;
- let LLMs advise inside typed, replayable, bounded lanes;
- keep final architecture compilation deterministic and fail-closed.

That yields a module that fits ADEU Studio's actual trajectory:

- docs as semantic authority;
- typed artifacts as the center of gravity;
- deterministic validators and evidence as the release boundary;
- hybrid agent lanes used only where bounded and explicit.

ASIR is the missing architecture IR that turns prompt-driven architecture from a brittle leap into a governed compilation pipeline.

---

## Appendix A. Repo as Reasoning Medium

This document is also evidence for a broader ADEU Studio claim:

> markdown, JSON, and Python do not have to function only as documentation, payloads, and implementation; together they can form a governed medium for reasoning about the next module.

The first ASIR draft was strong not only because of model capability, but because it was produced from inside an already partially formalized conceptual harness:

- markdown documents carried scope, precedent, lock discipline, and semantic authority;
- JSON schemas and fixtures carried typed ontology, artifact contracts, and frozen vocabularies;
- Python modules carried deterministic transforms, validators, canonicalization rules, and integrity checks;
- committed evidence artifacts carried historical release boundaries and examples of bounded hybrid execution.

That means the repo was not merely being described. It was acting as a semantic substrate for self-extension.

ASIR should preserve and deepen that property by treating the repo's mixed artifact ecology as a first-class authority surface:

- lock docs and architecture notes as semantic authority inputs;
- schemas and fixtures as ontological and contract authority inputs;
- deterministic validators as epistemic and deontic authority inputs;
- closeout artifacts as evidence of what bounded hybrid and compiler patterns are already legitimate in-tree.

### A.1 The Draft as a Micro-Instance of ASIR

The drafting process was not only commentary about the proposed architecture compiler. It was also a condensed enactment of the same architecture at micro-scale.

| Drafting process | ASIR pipeline analogue |
|---|---|
| user prompt stating a compressed problem | raw intent brief |
| repo inspection across docs, schemas, fixtures, and Python modules | authority-input normalization |
| extraction of recurring objects such as trust boundaries, authority rules, projections, checkpoints, and evidence lanes | ontology and contract decomposition |
| comparison across existing precedents (`v61` to `v65`, `v76`, semantic compiler, core IR) | world-hypothesis assembly under bounded authority |
| rejection of direct prompt-to-code framing | no direct brief-to-code without IR |
| production of a typed artifact family, control plane, validator suite, and pseudo-language | semantic IR externalization |
| only then describing lowering paths toward implementation | bounded projection toward code |

That matters because it suggests the bridge from intent to code is not merely "add one more artifact." It is "force the reasoning process itself to unfold in IR-shaped stages":

1. do not project too early;
2. gather authority inputs from multiple artifact kinds;
3. unpack the hidden world until entities, boundaries, obligations, evidence, and goals become explicit;
4. make uncertainty visible instead of hiding it inside generation;
5. constrain downstream implementation by the explicit semantic artifact.

So the document is not only about a future architecture module. It is also evidence that ADEU Studio's existing artifact ecology already supports a proto-form of semantic compilation in practice.
