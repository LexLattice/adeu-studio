# ODEU WCPGC Core And `strict_v0` Consolidated Draft

Status: working consolidated draft.

Authority posture:

- this document is a support/spec-synthesis artifact;
- it is not a lock doc;
- it does not authorize runtime behavior or implementation by itself;
- it consolidates
  `docs/support/DRAFT_WCPGC_CORE_FRAMEWORK_v0.md` as the WCPGC framework and
  `docs/support/DRAFT_WCPGC_STRICT_V0_PROFILE_v0.md` as the bounded `strict_v0`
  implementation profile.

## document_role

This document merges the two prior drafts into one master reference.

- `docs/support/DRAFT_WCPGC_CORE_FRAMEWORK_v0.md` remains the formal backbone:
  - ontology
  - lawful specialization
  - refresh law
  - typed verdicts
  - checked transitions
- `docs/support/DRAFT_WCPGC_STRICT_V0_PROFILE_v0.md` supplies the bounded
  implementation profile:
  - closed DSL
  - canonicalization
  - BridgeWitness schema
  - ProjectionWitnessManifest
  - TaskResidual quotient law
  - executable validation/action-selection rule
  - strict boolean enforcement surface

The governing intent is simple:

- keep WCPGC as the general framework;
- implement only `wcpgc.strict_v0`;
- harden the small issues identified by the merge guide before runtime rollout.

## wcpgc_framework

WCPGC is the ODEU Witness-Carrying Packet Governance Calculus. It is a
strict-governance execution calculus for systems whose upper law is fixed, whose
lower packets must lawfully specialize that law, and whose runtime still must
select concrete next actions under typed factual state.

Its purpose is to answer, inside one packet system:

1. whether a packet is well-formed and lawful,
2. whether a lower packet lawfully specializes an upper packet set,
3. which obligations are active,
4. which defaults are defeated rather than violated,
5. whether runtime facts are clean or contaminated,
6. whether a transition is legal,
7. which next action is legal,
8. how those typed results project to boolean gates.

The runtime configuration is:

```text
Γ = ⟨phase, C, R, Tχ, Tρ, S, Ω, m, π⟩
```

where:

- `C` = Constitution
- `R` = Role
- `Tχ` = TaskCharter
- `Tρ` = TaskResidual
- `S` = RuntimeFactStore
- `Ω` = AdapterOverlay
- `m` = model handle
- `π` = canonical trace prefix

## minimal_ontology

Primary governance strata:

- `Constitution`
  - immutable upper law during ordinary execution
- `Role`
  - material posture packet, not nominal label
- `TaskCharter`
  - assignment packet
- `TaskResidual`
  - derived task-stratum artifact, not authored law
- `RuntimeFactStore`
  - observed and feasibility facts only

Required auxiliary artifacts:

- `BridgeWitness`
  - lower-to-upper specialization proof surface
- `ScopedExportArtifact`
  - typed carry-over artifact with source, target, and warrant
- `AdapterOverlay`
  - explicit adapter/overlay artifact, not hidden tuning
- `MaintenanceChange`
  - privileged constitutional-change artifact
- `ProjectionWitnessManifest`
  - compiler projection accounting surface

The four semantic layers remain:

1. constitution
2. role
3. task
4. runtime

`TaskResidual`, `BridgeWitness`, `ScopedExportArtifact`, `AdapterOverlay`, and
`ProjectionWitnessManifest` are native artifacts needed to make those four
layers executable without contamination.

## normative_force_system

WCPGC uses exactly four force classes:

- `hard`
- `default`
- `advisory`
- `factual`

Rules:

- `hard` enters the legality kernel;
- `default` enters the defeasible preference kernel;
- `advisory` affects ranking and explanation only;
- `factual` is orthogonal and may activate guards or feasibility only.

Ordering:

```text
hard > default > advisory
factual is orthogonal, not in the defeat chain
```

Defeat is lawful only if:

1. the defeated clause is `default` or `advisory`,
2. the defeating clause is active,
3. the defeating basis is admissible and more specific or explicitly prior,
4. the relevant `BridgeWitness` permits that defeat.

## lawful_specialization

Lower packets do not become lawful merely by sounding narrower. WCPGC requires:

```text
lawful_spec(U, L, W) iff
  wf(U) ∧ wf(L) ∧ wf(W)
  ∧ vocab_closed(U, L, W)
  ∧ support_complete(U, L, W)
  ∧ force_admissible(U, L, W)
  ∧ nonwidening(U, L, W)
  ∧ hard_preserving(U, L, W)
  ∧ satisfiable(U, L, W)
```

Stratum-specific readings:

- `role_refines(C, R, W_R)`
- `task_refines(C, R, Tχ, W_T)`
- `state_instantiates(C, R, Tχ, Tρ, S)`

Runtime is not specialization. It instantiates conditions; it does not mint law.

## refresh_law

WCPGC uses one inheritance/refresh law:

```text
Refresh(op, x) =
  inherit(x)          if class(x)=immutable and op is ordinary
  replace(x, x')      if the stratum is explicitly replaced and authorized
  derive(x')          if class(x)=derived
  clear(x); recompute if class(x)=ephemeral
  append_only(x)      if class(x)=audit
```

Key consequences:

- `Constitution`, `Role`, and `TaskCharter` preserve exact semantic identity across
  ordinary execution seams;
- `TaskResidual` is never blindly inherited and must be re-derived;
- `RuntimeFactStore` is never authority-carrying across seams and must be
  recomputed from live state plus lawful imports;
- compaction/resume cannot preserve upper law by paraphrase alone.

## checked_transitions

The framework transition algebra is:

```text
spawn            : Γ_parent × Role? × TaskCharter × ExportSet × Adapter? -> Γ_child × V
compact          : Γ -> Snapshot × V
resume           : Snapshot × LiveEnv × Adapter? -> Γ × V
swap_model       : Γ × ModelHandle × AdapterOverlay -> Γ' × V
enter_maintenance: System × MaintenanceChange -> System' × V
```

Framework invariants:

- exact upper-layer identity for ordinary transitions;
- typed export/import only;
- no runtime-momentum laundering into role/task/constitution;
- explicit failure classes such as:
  - `illegal_export`
  - `missing_witness`
  - `illegal_widening`
  - `compaction_law_drift`
  - `residual_forgery`
  - `adapter_unsafe`

## strict_v0_profile

`strict_v0` is the smallest bounded profile that closes the previously exposed
implementation gaps without pretending to solve the full open-ended calculus.

It hardens exactly these surfaces:

1. restricted packet DSL
2. canonicalization and identity pinning
3. BridgeWitness and projection-witness trust path
4. TaskResidual quotient law
5. executable validation vs action-selection semantics
6. bounded enforcement profile

Anything not needed to make `checkpoint first` executable over broader defeasible
role posture is deferred.

## strict_v0_packet_dsl

`strict_v0` uses a closed JSON DSL. No free-form prose is executable.

Packet kinds:

- `constitution`
- `role`
- `task_charter`
- `task_residual`
- `runtime_fact_store`
- `bridge_witness`

Shared requirements:

- every authored packet carries:
  - `schema`
  - `profile = "wcpgc.strict_v0"`
  - `packet_kind`
  - `canon_id`
  - `ast_hash`
  - `scope`
  - `parent_packet_refs`
- `instance_id` is materialization only, never semantic identity

Bounded clause allowance:

- Constitution:
  - action catalog
  - fact catalog
  - hard base permissions
  - hard effect forbids
  - hard export rules
- Role:
  - `prefer` defaults and advisories only
- TaskCharter:
  - `first`
  - `before`
  - `stop_when`
  - scoped `permit`
  - default/advisory `prefer`
- RuntimeFactStore:
  - typed `obs`
  - typed `feas`
- TaskResidual:
  - derived only
- BridgeWitness:
  - proof surface only

Compile-time forbidden in `strict_v0`:

- free-form executable prose
- disjunction, quantifiers, recursion, modal nesting
- `until`, `next`, `after`, `unless`
- role hard clauses
- task hard clauses other than `first`, `before`, `stop_when`, scoped `permit`
- vocabulary aliases/synonyms
- permissions induced from runtime facts
- export of residual obligations
- hidden salience carriers

## strict_v0_identity_and_canonicalization

Semantic identity is operational.

Canonical semantic payload excludes:

- `instance_id`
- `source_refs`
- `projection_ref`
- evidence and audit refs

Normalization rules:

1. trim strings and normalize to NFC
2. lowercase enums to canonical spellings
3. reject unknown fields
4. inject canonical defaults
5. dedupe and sort set-like arrays
6. normalize or deterministically generate clause ids
7. sort clause arrays by `clause_id`
8. sort parent packet refs by packet identity tuple

Identity rules:

```text
ast_hash(P) := sha256_canonical_json(semantic_payload(P))
canon_id(P) := packet_kind + ":" + ast_hash(P)[0:24]
```

Pinned identities across spawn/compact/resume:

- `ConstitutionPacket.canon_id + ast_hash`
- `RolePacket.canon_id + ast_hash`
- `TaskCharterPacket.canon_id + ast_hash`
- required `BridgeWitness` hashes
- required `ProjectionWitnessManifest` hash

Not identity carriers:

- `TaskResidualPacket`
- `RuntimeFactStore`
- arbitrary prompt text

## bridgewitness_and_projection_witness

`BridgeWitness` is required for `RolePacket` and `TaskCharterPacket`.

Its job is to make admissibility explicit:

- vocabulary map
- support map
- specialization mode:
  - `restriction`
  - `concretization`
  - `defeat`
- force admissibility basis
- non-widening certificate

Fixed `strict_v0` admissibility rules:

- `SR1.role_defaults_only`
- `SR2.task_hard_ordering`
- `SR3.task_permission_subset`
- `SR4.task_defaults_only`
- `SR5.task_over_role_default_defeat`

The compiler must also emit a `ProjectionWitnessManifest`. This prevents the
compiler from silently rewriting governance meaning.

Required manifest accounting:

- every source fragment is classified as:
  - `accepted`
  - `rejected`
  - `ambiguous`
- every accepted fragment has exactly one assigned layer
- every generated packet exists and hash-matches
- every generated clause is traceable to accepted source fragments
- clause coverage and manifest coverage hashes recompute exactly

`strict_v0` trust is fail-closed:

- missing manifest => reject
- accepted ambiguity => reject
- packet hash mismatch => reject
- clause coverage gap => reject

## task_residual_quotient_law

`derive_residual(Tχ, π, S)` is a pure runtime function.

It may read only:

- canonical `TaskCharterPacket`
- canonical trace prefix
- canonical `RuntimeFactStore`

It may not read:

- `RolePacket`
- constitution prose
- prompt text
- parent narrative summaries
- model hints

It may emit only:

- `charter_ref`
- `prefix_hash`
- `satisfied`
- `pending`
- `frontier`
- `blocked_by_fact_refs`
- `defeat_records`

It may never emit:

- new permissions
- new obligations
- new defaults or priorities
- upper-layer summaries
- role-default defeat records
- free-prose blockers
- recommended next actions

Stable/volatile split:

```text
stable_core(Tρ)   := { charter_ref, prefix_hash, satisfied, pending, frontier }
volatile_shell(Tρ):= { blocked_by_fact_refs, defeat_records }
```

Resume rule:

- verify stable order structure against the charter and prefix;
- recompute the volatile shell from live `RuntimeFactStore`;
- cached blockers never count as authoritative after resume unless recomputed
  from live `RuntimeFactStore`.

## executable_validation_and_action_selection

Validation and action selection are separate functions.

Validation order:

```text
validate(Γ):
  1. load C, R, Tχ
  2. validate schema, canonical hashes, pinned refs
  3. validate ProjectionWitnessManifest(s)
  4. validate BridgeWitness(Role -> Constitution)
  5. validate BridgeWitness(Task -> Role + Constitution)
  6. validate RuntimeFactStore typing and contamination
  7. derive TaskResidualPacket
  8. compute trust_state
  9. return ValidatedState Σ
```

Candidate universe is closed-world.

In this consolidated profile, the runtime meta-actions are not magical side
channels. They are constitution-declared actions and must appear in the
constitution action catalog:

- `emit_blocked_status`
- `request_more_facts`
- `escalate`

So:

```text
candidate_actions := declared_actions(Σ) ∪ constitutional_meta_actions
```

Hard-frontier rule:

- if task stop facts are active:
  - legal next actions are only status/escalation meta-actions
- if hard frontier exists but no frontier action is feasible:
  - legal next actions are only status/request/escalation meta-actions
- if hard frontier exists and some frontier action is feasible:
  - legal next actions are only feasible frontier actions
- defaults are consulted only when hard frontier is empty, or to rank among
  multiple feasible hard-frontier actions

This yields the core behavioral rule:

- blocked hard frontier does not fall back to exploratory role behavior
- task-local hard order controls the next step
- role posture survives as defeasible posture, not erased law

## defaults_and_defeat

Two distinctions must remain explicit:

- defeated default:
  - a higher-force or more-specific active basis excludes all actions preferred by
    that default from current legal next actions
- non-satisfied default:
  - the preferred action remains legal, but loses deterministically on final
    ranking

Role-default defeat is computed at action-selection time and returned as a
runtime verdict. It is not baked back into `TaskResidualPacket`.

## strict_v0_enforcement_profile

Checked in `strict_v0`:

- packet acceptance
- witness validation
- factual export
- spawn
- compact
- resume
- next-step selection

Deferred out of `strict_v0`:

- general model swap
- maintenance transition
- executable adapter/overlay ecology

Fail-closed verdicts include:

- malformed packet
- missing projection manifest
- accepted-fragment ambiguity
- missing BridgeWitness
- hash mismatch
- illegal widening
- permission subset failure
- role under-instantiated
- runtime contamination
- illegal fact export
- unknown action symbol
- pinned identity mismatch on resume
- cross-family model change

Degraded trust is narrow:

- same model family
- same model major version
- different patch/minor evaluator identity

Under degraded trust, only effect subsets of:

```text
{ read_local, status_only }
```

may proceed.

Boolean gates exposed by the profile:

- `accept_packet_bundle?`
- `allow_spawn?`
- `allow_compact?`
- `allow_resume?`
- `allow_export?`
- `allow_action(a)?`

## consolidation_patches

This consolidated draft applies the merge-guide hardening directly.

### 1. Constitutional meta-action catalog

The scheduler meta-actions:

- `emit_blocked_status`
- `request_more_facts`
- `escalate`

must be explicit members of the constitution action catalog. They are lawful
actions with fixed effect envelopes, not hidden runtime escape hatches.

### 2. Role packet materiality minimum

`RolePacket` must be materially non-empty.

Profile rule:

- a `RolePacket` must contain at least one `default` or `advisory` clause

A role label without such content is under-instantiated and invalid for
`strict_v0`.

### 3. No cached blocker authority

Cached blockers or cached stop conditions never count as authoritative after
resume unless recomputed from live `RuntimeFactStore`.

### 4. Minimal test matrix

The bounded conformance test matrix should include at least:

1. anchor bug:
   - role prefers exploration, task hard frontier requires checkpoint, checkpoint wins
2. role label without packet:
   - reject as under-instantiated
3. contaminated runtime fact:
   - reject or block under contamination rules
4. illegal export:
   - reject when fact kind, scope, or warrant fails
5. compaction identity drift:
   - reject if `C`, `R`, or `Tχ` identity changes across seam
6. blocked hard frontier:
   - allow only status/request/escalation meta-actions
7. degraded same-family resume:
   - yield `degraded_trust`, then allow only `read_local` and `status_only`

## minimum_implementation_lane

Only the bounded lane should be built first.

Compiler-side minimum:

- authored schemas and models for:
  - `ConstitutionPacket`
  - `RolePacket`
  - `TaskCharterPacket`
  - `BridgeWitness`
  - `ProjectionWitnessManifest`
- canonicalization and `canon_id` / `ast_hash` helpers
- fail-closed `strict_v0` compiler target that emits:
  - packet bundle
  - role/task bridge witnesses
  - projection witness manifest

Runtime-side minimum:

- `RuntimeFactStore`
- `TaskResidualPacket`
- `derive_residual(Tχ, π, S)`
- checked `strict_v0` operators:
  - spawn
  - compact
  - resume
  - next-step selection

Bridge/compaction seam minimum:

- carry refs and hashes for:
  - constitution
  - role packet
  - task charter
  - projection manifest
  - role/task bridge witnesses
  - prefix hash
  - model family/version
  - trust state

Verdict minimum:

- keep typed verdicts primary;
- derive booleans from typed verdicts;
- do not collapse `defeated_default`, `degraded_trust`, and `blocked` into one
  generic failure bucket.

## explicit_deferrals

Do not attempt these in `strict_v0`:

- open-ended theorem proving of non-widening
- non-identity vocabulary maps
- conditional defaults
- generalized temporal operators
- general model-swap calculus
- executable maintenance calculus
- executable adapter overlays
- richer ontology expansion beyond the fixed bounded alphabet

## implementation_posture

This consolidated draft should be read as:

- WCPGC-core gives the governing framework;
- `strict_v0` gives the bounded profile that is implementable now;
- implementation should target only the bounded profile;
- anything beyond that must be a later profile revision, not silent widening of
  `strict_v0`.

That is the intended merge result:

- one framework,
- one bounded profile,
- one explicit witness path,
- one pure residual law,
- one executable action-selection rule,
- one small implementation target.
