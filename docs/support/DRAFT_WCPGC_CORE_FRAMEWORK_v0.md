I will call the derived framework **ODEU Witness-Carrying Packet Governance Calculus (WCPGC)**.

It is not “IMNS + PDLL + TDTL + THAM” left side by side. In WCPGC, governance validity, defeasible local defeat, temporal task order, and checked runtime transitions are all expressed through one packet ontology, one clause language, one specialization relation, one residual law, one verdict algebra, and one transition machine. It is derived from the prior work’s fixed commitments: four semantically distinct layers, typed refinement instead of the single slogan “lawful specialization,” a split between task charter and task residual, a contamination firewall, exact upper-layer identity across compaction/resume/swap, explicit adapter/overlay artifacts, and a separation between validation order and action-selection order.

## framework_purpose

WCPGC is a strict-governance execution calculus for systems whose upper law is fixed by ODEU and whose runtime must still make concrete next-step decisions. Its purpose is to answer, in one formalism:

1. whether a packet is lawful,
2. whether a lower packet lawfully specializes an upper context,
3. which obligations are currently active,
4. which defaults are defeated rather than violated,
5. which runtime artifacts are contaminated,
6. whether a transition is legal,
7. which next action is selected,
8. how those typed results project to boolean gates.

The core runtime configuration is:

```text
Γ = ⟨phase, C, R, Tχ, Tρ, S, Ω, m, π⟩
```

where `C` is constitution, `R` role, `Tχ` task charter, `Tρ` task residual, `S` runtime fact store, `Ω` adapter/overlay, `m` model handle, and `π` the executed trace prefix.

## minimal_ontology

WCPGC needs the following native sorts.

**Primary governance strata**

* `Constitution`

  * immutable upper law during ordinary execution
  * carries global action/effect ontology, hard constraints, delegation templates, export policy, maintenance policy

* `Role`

  * material posture packet, not a nominal label
  * carries role-local defaults, advisories, and only those hard guards explicitly authorized by constitution

* `TaskCharter`

  * the assignment packet
  * carries task-local ordered obligations, stop conditions, scoped permissions, import requirements

* `TaskResidual`

  * a derived task-stratum artifact, not a generic runtime bag
  * carries current frontier, satisfied obligations, pending obligations, blockers by fact reference, and defeat records
  * this is how “open obligations” persist without mutating charter law

* `RuntimeFactStore`

  * observed and feasibility facts only
  * has no native authority to create permissions or defaults

**Auxiliary governance artifacts**

* `AdapterOverlay`

  * explicit model-family adapter plus autonomy/collaboration overlay
  * orthogonal artifact, not hidden residue

* `MaintenanceChange`

  * privileged meta-governance artifact for constitutional update

* `ScopedExportArtifact`

  * typed carry-over artifact for inter-task or inter-worker transfer
  * always source-scoped, target-scoped, and warrant-bound

* `BridgeWitness`

  * proof-carrying relation artifact
  * binds lower packet clauses to upper support, vocabulary mapping, defeat basis, and non-widening certificate

* `ViolationClass`

  * typed failure taxonomy used in verdict evidence

**Foundational sorts**

* `GovernanceClause`
* `Force = {hard, default, advisory, factual}`
* `Action`, `Effect`, `TracePrefix`
* `Guard`, `Scope`, `Identity`
* `TypedVerdict`

The four main semantic layers remain constitution / role / task / runtime. `TaskResidual`, `AdapterOverlay`, `ScopedExportArtifact`, `BridgeWitness`, and `MaintenanceChange` are native artifact kinds, but they are not extra law layers; they are typed control artifacts required to make the four-layer story executable without contamination. That directly addresses the prior stress test’s pressure points around task residuals, adapters/overlays, and maintenance.

## packet_grammar

All packets share one header and compile to one internal clause IR.

```text
PacketHeader ::=
{
  kind: PacketKind,
  canon_id: CanonId,          // semantic identity
  instance_id: InstanceId,    // materialization identity
  ast_hash: Hash,             // normalized content hash
  version: Nat,
  issuer: Principal,
  issued_at: Time,
  provenance_ref: Ref,
  scope: Scope,
  parent_refs: [CanonId],
  witness_refs: [WitnessId],
  persistence_class: PersistenceClass
}

GovernanceClause ::= NormClause
                   | OrderClause
                   | FactSchema
                   | ExportRule
                   | AdapterRule
                   | MaintenanceRule
```

```text
NormClause ::=
{
  clause_id: ClauseId,
  force: hard | default | advisory,
  modality: oblige | forbid | permit | recommend | stop,
  trigger: Guard,
  body: ActionFormula | EffectFormula | TraceFormula,
  priority: PriorityKey,
  scope: Scope
}

OrderClause ::=
{
  clause_id: ClauseId,
  force: hard | default | advisory,
  order: first(a) | before(a,b) | stage(k,a) | until(p,a),
  trigger: Guard,
  priority: PriorityKey,
  scope: Scope
}

FactSchema ::=
{
  clause_id: ClauseId,
  force: factual,
  fact_kind: obs | feas,
  predicate: FactPred,
  provenance_req: ProvenancePolicy,
  exportable: Bool,
  scope: Scope
}
```

### ConstitutionPacket

May contain:

* action/effect ontology
* hard norms
* global defaults/advisories
* delegation templates and force budgets
* export rules
* maintenance rules

May not contain:

* task-local residuals
* runtime facts
* model-family instructions
* live salience or handoff momentum

Identity:

* `canon_id` and `ast_hash` must remain exact across ordinary execution, spawn, compaction, resume, and model swap

Persistence:

* `immutable`

### RolePacket

May contain:

* role defaults
* role advisories
* constitution-authorized hard guards
* capability assumptions
* explicit defeat priorities

May not contain:

* raw runtime facts
* task residual
* constitutional amendment
* nominal label only

Identity:

* `canon_id` stable across ordinary execution, compaction, resume, swap

Persistence:

* `stable`

### TaskCharterPacket

May contain:

* `task_id`
* ordered hard obligations
* task defaults/advisories
* scoped permissions
* stop conditions
* completion tests
* import requirements

May not contain:

* constitutional rewrites
* role rewrites
* free-form inherited runtime momentum
* paraphrased upper law as new authority

Identity:

* `canon_id` stable for the life of the task instance

Persistence:

* `stable`

### TaskResidualPacket

May contain:

* `task_id`
* `charter_ref`
* `prefix_hash`
* `frontier`
* `pending`
* `satisfied`
* `blocked_by_fact_refs`
* `defeat_records`

May not contain:

* new permissions
* new defaults
* upper-law recaps
* unsourced facts

Identity:

* continuity is by `(task_id, charter_ref, prefix_hash)`, not by prose summary

Persistence:

* `derived`

### RuntimeFactStore

May contain:

* observed facts
* feasibility facts
* imported fact refs
* freshness and provenance maps

May not contain:

* norms
* permissions
* priorities
* salience weights
* law summaries
* adapter directives

Identity:

* no semantic persistence; only material window identity

Persistence:

* `ephemeral`

### AdapterOverlayPacket

May contain:

* target model family
* translation contract
* capability profile
* overlay controls
* influence budget
* trust contract
* regression refs

May not contain:

* new permissions
* task law
* constitutional law
* imported parent momentum masquerading as tuning

Identity:

* stable while installed; replaced on explicit swap/overlay change

Persistence:

* `stable`

### MaintenanceChangePacket

May contain:

* base constitution ref
* proposed constitution ref
* diff
* authority basis
* migration rules
* rollback plan

May not contain:

* ordinary task directives
* live runtime state as authority
* implicit constitutional edits

Persistence:

* `audit`

### ScopedExportArtifact

May contain:

* source task/session
* target scope
* artifact class
* payload
* TTL
* export warrant

May not contain:

* unscopeable obligations
* upper-law paraphrase
* hidden salience carriers

Persistence:

* `ephemeral`

### BridgeWitness

May contain:

* lower ref
* upper refs
* support map
* vocabulary map
* specialization mode
* non-widening certificate
* defeat basis

May not contain:

* free-standing directives

Persistence:

* `audit/stable-to-reference-pair`

## normative_force_system

WCPGC uses exactly four force classes.

**Hard**

Hard clauses enter the legality kernel. If an action or transition violates an active hard clause, the result is illegal in ordinary execution. Hard clauses are undefeated except by authorized maintenance replacing constitution-level law.

**Default**

Default clauses enter the preference kernel. They are presumptively action-guiding, but may be lawfully defeated by a more specific active clause with higher admissible priority. Defeat is recorded as `defeated_default`; it is not treated as constitutional violation.

**Advisory**

Advisory clauses do not change legality. They affect only ranking, logging, and explanation. Ignoring them never makes an otherwise legal action illegal.

**Factual**

Factual clauses are not normative at all. They can:

* satisfy guards,
* activate conditionals,
* prove feasibility/infeasibility.

They cannot:

* create permission,
* defeat norms,
* raise force,
* insert ranking weight on their own.

The force ordering is:

```text
hard  >  default  >  advisory
factual is orthogonal, not in the defeat chain
```

Defeat is lawful only if:

1. the defeated clause is `default` or `advisory`,
2. the defeating clause is active,
3. the defeating clause is more specific by scope/guard or has explicit priority,
4. the bridge witness permits the defeat.

## judgment_forms

WCPGC computes the following judgments.

```text
wf(P)                                   // packet is well-formed

C ⊢ R ▷ W_R : V                         // role lawfully specializes constitution

C,R ⊢ Tχ ▷ W_T : V                      // task charter lawfully specializes constitution+role

Tχ,π,S ⊢ Tρ : V                         // residual is lawful quotient of charter under prefix+facts

C,R,Tχ,Tρ ⊢ S ⇓ V                       // runtime facts instantiate but do not authorize

C,R,Tχ,Tρ,m ⊢ Ω ⇓ V                     // adapter/overlay is safe, degraded, or unsafe

Γ ⊢ X ↣ target_scope : V                // export artifact is legal

Γ ⊢ op ⇝ Γ' : V                         // checked transition is legal/illegal/underdetermined

Γ ⊢ a legal : V                         // next action a is normatively legal

Γ ⊢ choose a : V                        // a is the selected next action
```

Typical readings:

* `wf(C)` gives “constitution valid”
* `C ⊢ R ▷ W_R : valid` gives “role refines constitution”
* `C,R ⊢ Tχ ▷ W_T : valid` gives “task charter refines role and constitution”
* `C,R,Tχ,Tρ ⊢ S ⇓ instantiated` gives “runtime instantiates but does not authorize”
* `Γ ⊢ X ↣ target : illegal_export` gives “export is illegal”
* `C,R,Tχ,Tρ,m ⊢ Ω ⇓ degraded_trust` gives “adapter is degraded”
* `Γ ⊢ op ⇝ Γ' : underdetermined` gives “transition is legal but selection is unresolved”

## lawful_specialization_definition

This is the core definition.

Let `U` be the normalized upper context, `L` a candidate lower packet, and `W` a bridge witness. Then:

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

Where:

**1. `vocab_closed(U,L,W)`**
Every primitive in `L` is either:

* already in the upper action/effect/fact signature, or
* introduced by a definitional extension declared in `W`.

No silent vocabulary extension is allowed.

**2. `support_complete(U,L,W)`**
For every normative clause `c ∈ L`, `W` must provide a non-empty support set from `U`, and classify `c` as one of:

* `restriction`
* `concretization`
* `defeat`

**3. `force_admissible(U,L,W)`**
Lower clauses may not raise force arbitrarily. A lower hard clause is admissible only if:

* it is task- or role-scoped,
* it narrows the upper legal set,
* and an upper delegation template authorizes that form of local hardening.

Defeat may target only `default` or `advisory`, never active hard law.

**4. `nonwidening(U,L,W)`**
For every admissible runtime instantiation `σ` in the domain of `W`:

```text
AllowedEffects(U ∪ L, σ) ⊆ AllowedEffects(U, σ)
```

and, equivalently at the trace level,

```text
LegalTraces(U ∪ L, σ) ⊆ LegalTraces(U, σ)
```

projected to the shared upper signature.

This is the non-circular criterion that lower layers narrow rather than rewrite.

**5. `hard_preserving(U,L,W)`**
No active hard clause in `U` is made unsatisfiable by `L`.

**6. `satisfiable(U,L,W)`**
Within the declared scope of `L`, there exists at least one legal trace. Otherwise the lower packet is contradictory, not a specialization.

### Specialization relations by stratum

**Role specialization**

```text
role_refines(C, R, W_R) := lawful_spec(C, R, W_R)
                           ∧ role_material(R)
                           ∧ role_force_profile_ok(R)
```

Role is mostly posture: defaults/advisories plus constitution-authorized hard guards.

**Task specialization**

```text
task_refines(C, R, Tχ, W_T) := lawful_spec(C ∪ R, Tχ, W_T)
                               ∧ ordered_norms_well_founded(Tχ)
                               ∧ defeats_only_role_soft_clauses(Tχ, R, W_T)
```

Task may add hard local order, stop conditions, and scoped permissions only inside the upper effect envelope.

**Runtime instantiation**

Runtime is not specialization:

```text
state_instantiates(C, R, Tχ, Tρ, S) :=
  wf(S) ∧ clean(S) ∧ typed_facts_only(S)
  ∧ activates_only(S, guards(C,R,Tχ,Tρ))
```

It instantiates conditions; it does not authorize.

This directly replaces the prior single slogan with typed relations for role, task, and runtime.

## inheritance_refresh_algebra

WCPGC uses one refresh law parameterized by persistence class.

```text
PersistenceClass = immutable | stable | derived | ephemeral | audit
```

The law is:

```text
Refresh(op, x) =
  inherit(x)             if class(x)=immutable and op∉{maintenance}
  replace(x, x')         if op explicitly replaces x's stratum and authorization passes
  derive(x')             if class(x)=derived
  clear(x); recompute    if class(x)=ephemeral
  append_only(x)         if class(x)=audit
```

Primitive operators:

```text
inherit(x)      := preserve canon_id and ast_hash
replace(x,y)    := install y under new canon_id unless y is exact same canonical packet
clear(x)        := remove from active config
recompute(x)    := rebuild from live environment + legal imports
forbid_export(x):= export attempt yields illegal_export
quotient(Tχ,π,S):= derive Tρ from charter, prefix, and blocker facts
```

Application by artifact class:

* `ConstitutionPacket`

  * `inherit` across execute/spawn/compact/resume/swap
  * `replace` only in maintenance
  * export by reference only

* `RolePacket`

  * `inherit` across execute/compact/resume/swap
  * `replace` on explicit role transition or spawn with new role packet
  * export by reference only

* `TaskCharterPacket`

  * `inherit` within same task
  * `replace` on new assignment/spawn
  * export by reference only

* `TaskResidualPacket`

  * never blindly inherited
  * always `derive = quotient(Tχ,π,S)`
  * may export only scoped residual markers or imported obligations that pass subsumption

* `RuntimeFactStore`

  * always `clear; recompute`
  * no raw inheritance across spawn
  * imports only legal `ScopedExportArtifact`s

* `AdapterOverlayPacket`

  * `inherit` if same adapter remains installed
  * `replace` on swap/overlay change

* `MaintenanceChangePacket`, `BridgeWitness`

  * append-only audit artifacts

This is the single inheritance/refresh law the prior work was missing. It enforces exact upper identity and explicit lower recomputation instead of prose recap.

## transition_operators

The checked transition algebra is:

```text
spawn            : Γ_parent × Role? × TaskCharter × ExportSet × Adapter? -> Γ_child × V
compact          : Γ -> Snapshot × V
resume           : Snapshot × LiveEnv × Adapter? -> Γ × V
swap_model       : Γ × ModelHandle × AdapterOverlay -> Γ' × V
enter_maintenance: System × MaintenanceChange -> System' × V
```

### spawn

Inputs:

* parent config `Γp`
* optional replacement role `R'`
* child charter `Tχ'`
* export set `X*`
* optional adapter `Ω'`

Preserved identities:

* `C.canon_id`
* `R.canon_id` if no role change
* parent remains unchanged

Replaced identities:

* fresh child `task_id`
* fresh `Tχ'`
* fresh derived `Tρ' = quotient(Tχ', ε, ∅)`
* fresh `S' = recompute(import(X*))`

Import/export rules:

* only `ScopedExportArtifact`s may cross
* facts must be typed `obs` or `feas`
* residual obligations may cross only if the child charter explicitly imports them and the export warrant proves subsumption
* no parent upper-law recap may cross as runtime

Failure states:

* `role_under_instantiated`
* `illegal_export`
* `contaminated`
* `missing_witness`
* `illegal_widening`

### compact

Inputs:

* current `Γ`

Preserved identities:

* exact refs/hashes for `C`, `R`, `Tχ`, and normally `Ω`

Replaced identities:

* `Tρc = quotient(Tχ,π,S)`
* serialized clean subset of `S`

Export/import rules:

* compaction snapshot stores upper packets by reference/hash only
* no paraphrase summary of constitution/role/task charter counts as preservation

Failure states:

* `compaction_law_drift`
* `contaminated`
* `illegal_export`
* `residual_forgery`

### resume

Inputs:

* snapshot
* live environment
* optional adapter install

Preserved identities:

* `C`, `R`, `Tχ` by exact ref/hash
* `task_id`

Replaced identities:

* fresh `instance_id`s
* `S = recompute(live env + legal imports)`
* `Tρ = quotient(Tχ, π_snapshot, S)`

Failure states:

* hash mismatch
* missing canonical packet
* snapshot contamination
* adapter unsafe

### swap_model

Inputs:

* current `Γ`
* new model handle `m'`
* new `Ω'`

Preserved identities:

* `C`, `R`, `Tχ`, `Tρ`, `task_id`

Replaced identities:

* `m`
* `Ω`

Import/export rules:

* no law changes
* no paraphrased transfer into adapter text
* adapter packet is the only legal swap artifact

Failure states:

* `unsafe`
* `degraded_trust`
* capability mismatch
* failed equivalence suite

`degraded_trust` is not identical to immediate denial; it is a typed status that later projects differently by effect class.

### enter_maintenance

Inputs:

* system state
* `MaintenanceChangePacket`

Preserved identities:

* old constitution archived by ref/hash
* lower packets frozen until revalidation

Replaced identities:

* constitution only, if ratified
* new `C'` gets new `canon_id`

Import/export rules:

* live runtime salience may not become constitutional authority
* maintenance uses explicit evidence artifacts only

Failure states:

* unauthorized maintenance
* missing migration witness
* maintenance leakage
* non-quiesced protected tasks

## validation_vs_action_selection

Validation order and next-step control order are distinct. The prior stress test correctly singled this out.

### Validation order

```text
Validate(Γ):
  1. wf(C)
  2. C ⊢ R ▷ W_R
  3. C,R ⊢ Tχ ▷ W_T
  4. Tχ,π,S ⊢ Tρ
  5. C,R,Tχ,Tρ ⊢ S
  6. C,R,Tχ,Tρ,m ⊢ Ω
  7. transition/operator preconditions
```

This decides legality and typed status.

### Action-selection order

After validation, selection uses the active frontier.

```text
frontier(Tρ) = { o ∈ pending(Tρ) | prereqs(o) ⊆ satisfied(Tρ) }
```

If `frontier(Tρ)` contains an executable hard obligation, only actions that advance that frontier remain legal candidates.

Then:

```text
Feasible(Γ) = actions enabled by S and m
Legal(Γ)    = {a ∈ Feasible(Γ) | a preserves all active hard clauses}
RankΓ(a)    = ⟨
                hard_frontier_violations,
                other_hard_violations,
                task_default_penalty,
                role_default_penalty,
                advisory_penalty,
                adapter_penalty
              ⟩
choose(Γ)   = argmin RankΓ(a)
```

Consequences:

* task-ordered hard obligations control the next step when determinate,
* task defaults fill remaining task-local underdetermination,
* role defaults fill broader underdetermination,
* advisories shape only tail ranking,
* runtime facts gate feasibility only.

That is why “checkpoint first” can control the next step without rewriting or invalidating a broader role default like “explore/document first.”

## runtime_contamination_firewall

The firewall is strict.

```text
AllowedInS  = ObsFact | FeasFact
AllowedInTρ = OpenStage | SatisfiedStage | BlockerRef | DefeatRecord
BannedInS   = PermissionToken
            | PriorityWeight
            | SalienceHint
            | RoleDefault
            | TaskDirective
            | LawSummary
            | AdapterHint
```

### What may exist at runtime

**In `RuntimeFactStore`**

* external observations
* tool/resource feasibility
* imported typed facts with provenance and TTL

**In `TaskResidualPacket`**

* unsatisfied ordered obligations
* satisfied markers
* blockers by fact ref
* defeated default records

### What the firewall blocks

**Facts becoming permission**
Permission closure is computed from `C,R,Tχ,Ω`, never from `S`. Runtime facts may activate an existing permission; they may not author one.

**Salience carriers masquerading as facts**
Anything whose only semantics is “make the scheduler care more” is banned from `S`. It must either be:

* a real observed fact,
* a real feasibility fact,
* a residual record,
* or a declared overlay control.

**Runtime momentum leaking across spawn**
Child runtime begins from `clear(S); recompute(imports)`. Parent salience, recent focus, unresolved momentum, or soft-pressure residue do not cross unless they are exported as typed artifacts and lawfully scoped.

This is the explicit contamination barrier the prior work required.

## adapter_overlay_semantics

Adapters and overlays are native packet kinds, not informal residue. The prior stress test was right to insist on that.

An `AdapterOverlayPacket` has three semantic components:

```text
Ω = ⟨τ, κ, ι⟩
```

* `τ` = translation contract

  * maps canonical action/effect/constraint vocabulary into model-specific substrate

* `κ` = capability contract

  * declares supported action classes, effect classes, and conservative gaps

* `ι` = influence budget

  * states exactly what the overlay may influence:

    * tie-breaking among equally legal actions
    * decomposition fan-out
    * verbosity / collaboration style
    * extra conservative checkpoints

It may **not**:

* create permission,
* relax prohibition,
* defeat hard clauses,
* import salience as if it were law.

Adapter judgment has three statuses:

* `safe`

  * non-widening preserved
  * protected policy suite passes
  * high-impact actions may proceed

* `degraded_trust`

  * clause preservation holds but next-action equivalence is incomplete
  * high-impact actions are gated more strictly

* `unsafe`

  * reject install

## maintenance_semantics

Maintenance is a privileged meta-transition, not ordinary execution.

System phases:

```text
phase ∈ {normal, maintenance}
```

In `normal`:

* constitution is immutable,
* all ordinary transitions are evaluated against fixed `C`.

In `maintenance`:

* constitutional replacement is allowed only through `MaintenanceChangePacket`,
* lower packets are frozen or sandboxed,
* ordinary task execution cannot silently mutate law.

Legality rule:

```text
enter_maintenance(System, M) is legal iff
  authorized(M)
  ∧ quiesced_or_sandboxed(System)
  ∧ migration_witness_ok(M)
  ∧ no_runtime_to_constitution_leak(M)
```

Exit rule:

* install `C'`
* revalidate `R`, `Tχ`, `Tρ`, `Ω`
* clear and recompute `S`

Maintenance log remains audit-only; it is not an ordinary runtime authority surface.

## typed_verdict_algebra

WCPGC keeps typed intermediate verdicts in a product algebra.

```text
V = ⟨shape, authority, preference, contamination, trust, determinacy, evidence⟩
```

Where:

```text
shape        ∈ {wf, role_under_instantiated, malformed}
authority    ∈ {authorized, missing_witness, illegal_export, illegal_widening, hard_conflict}
preference   ∈ {none, defeated_default}
contamination∈ {clean, contaminated}
trust        ∈ {safe, degraded, unsafe}
determinacy  ∈ {determinate, underdetermined, blocked}
evidence     ⊆ ViolationClass × Ref
```

Combination is componentwise accumulation:

```text
V1 ⊗ V2 = componentwise_max_badness(V1, V2)
          with evidence = evidence(V1) ∪ evidence(V2)
```

Pattern names:

* `valid`

  * `shape=wf ∧ authority=authorized ∧ contamination=clean`

* `invalid`

  * any of `malformed`, `missing_witness`, `illegal_export`, `illegal_widening`, `hard_conflict`, `unsafe`

* `underdetermined`

  * valid but `determinacy=underdetermined`

* `contaminated`

  * `contamination=contaminated`

* `defeated_default`

  * `preference=defeated_default` while authority remains `authorized`

* `illegal_widening`

  * `authority=illegal_widening`

* `illegal_export`

  * `authority=illegal_export`

* `degraded_trust`

  * `trust=degraded`

* `role_under_instantiated`

  * `shape=role_under_instantiated`

This is the formal reason the system does not collapse prematurely to boolean.

## boolean_enforcement_projection

Boolean gates are final projections from typed verdicts.

Let `eclass(a)` be the effect class of action `a`.

```text
legal?(V) :=
  (shape = wf)
  ∧ (authority = authorized)
  ∧ (contamination = clean)

accept?(V) :=
  legal?(V)
  ∧ (trust ≠ unsafe)

allow?(V, a) :=
  legal?(V)
  ∧ (determinacy ≠ blocked)
  ∧ trusted_for(trust, eclass(a))
```

Where:

```text
trusted_for(safe,     any)        = true
trusted_for(degraded, low_impact) = true
trusted_for(degraded, high_impact)= false
trusted_for(unsafe,   any)        = false
```

So:

* `defeated_default` can still project to `allow`
* `underdetermined` can still project to `legal`; selection then resolves the tie
* `degraded_trust` may still allow read-only/checkpoint/log actions while denying write/spawn/swap/maintenance/network actions
* `contaminated`, `illegal_export`, `illegal_widening`, `hard_conflict`, `role_under_instantiated` project to deny/reject

This gives the required runtime booleans without erasing the richer internal judgment space.

## anchor_case_walkthrough

The motivating case is the prior bug surface: inherited role posture equivalent to `explore/document first` versus task-local ordered obligation equivalent to `checkpoint first`.

Let:

```text
C0 contains:
  hC1 = hard forbid(permission_widening)
  hC2 = hard permit task-local procedural narrowing within assigned scope
  hC3 = hard forbid unscoped export

Rexp contains:
  dR1 = default first(explore_or_document)
        when task frontier is otherwise unspecified

Tchk contains:
  hT1 = hard first(checkpoint)
  hT2 = hard before(checkpoint, inspect)
  dT3 = default explore_after_checkpoint if topology_unknown

S0 contains:
  feas(run_checkpoint)
  feas(explore_repo)
  obs(repo_topology_unknown)
```

### Step 1: validation

* `wf(C0)` succeeds
* `C0 ⊢ Rexp ▷ W_R` succeeds because `dR1` is role-local posture, not global law
* `C0,Rexp ⊢ Tchk ▷ W_T` succeeds because `hT1` and `hT2` are task-scoped procedural hardening inside the upper effect envelope and explicitly authorized by `hC2`
* `Tρ0 = quotient(Tchk, ε, S0)` yields:

```text
frontier(Tρ0) = {checkpoint}
pending(Tρ0)  = {checkpoint, inspect}
satisfied(Tρ0)= ∅
```

### Step 2: action legality

Candidate actions:

* `a1 = explore_repo`
* `a2 = document_repo`
* `a3 = run_checkpoint`

`a1` and `a2` violate `hT1` because an executable hard frontier item exists and they do not advance it. Their verdict is illegal.

`a3` satisfies the hard frontier and remains inside all upper hard constraints. Its verdict is valid.

### Step 3: default adjudication

`dR1` is not rewritten and not invalidated globally. It is simply defeated in this local state:

```text
preference = defeated_default
evidence   = {specificity(task_scope > role_scope), hard_over_default}
```

So the result is not “role law lost.” The result is “role default lawfully defeated here.”

### Step 4: post-checkpoint

After `run_checkpoint`:

```text
Tρ1 = quotient(Tchk, π·checkpoint, S1)
frontier(Tρ1) = {inspect} or broader set per charter
```

Now `dR1` may reactivate if the task becomes underdetermined after checkpoint. That is exactly the desired behavior.

## countermodels_against_the_new_framework

These are the adversarial surfaces the prior stress test made unavoidable: hidden widening, nominal roles, export contamination, model swap drift, compaction drift, adapter laundering, and maintenance leakage.

**1. Hidden widening**
Attack: a task clause says “use helper_tool for evidence,” but the tool’s undeclared effect class includes remote write.
WCPGC response: reject only if the constitution’s action/effect ontology knows that effect class.
Residual risk: if ontology coverage is incomplete, widening can still hide behind action aliases.

**2. Nominal role collapse**
Attack: the runtime receives `role="explorer"` but the packet has no substantive defaults, guards, or capability assumptions.
WCPGC response: `role_under_instantiated`; reject install.
Residual risk: a vacuous but non-empty packet could still slip through unless minimal substantive content checks are strong.

**3. Export contamination**
Attack: parent exports `recent_focus=map_repo` as an alleged fact to a child whose task is checkpointing.
WCPGC response: contamination firewall rejects it unless it is a true observed fact or a subsuming residual artifact with warrant.
Residual risk: some payloads are dual-use and need finer schema than simple fact/non-fact separation.

**4. Model swap drift**
Attack: same packet set, different model family, different next action under ambiguity.
WCPGC response: `Ω` must pass trust contract; otherwise `degraded_trust` or reject.
Residual risk: observational suites may still miss rare but constitutionally relevant drift.

**5. Compaction law drift**
Attack: compaction stores a prose summary of constitution/role instead of exact packet refs and hashes.
WCPGC response: illegal; compaction must preserve canonical refs.
Residual risk: even with pinned packet refs, interpreter-version drift can still change behavior unless evaluation semantics are also pinned.

**6. Adapter laundering**
Attack: an overlay quietly encodes “prefer exploration before checkpoint” inside translation knobs.
WCPGC response: overlay influence budget forbids undeclared ranking dimensions; reject or mark unsafe.
Residual risk: hidden model priors may still simulate an undeclared overlay.

**7. Maintenance leakage**
Attack: temporary runtime blockers or salience pressure are smuggled into constitutional amendment prose.
WCPGC response: maintenance accepts only explicit audited evidence artifacts; live runtime momentum is not lawful authority.
Residual risk: human-authored maintenance rationales can still disguise contingency as principle.

**8. Compiler / witness laundering**
Attack: the compiler misclassifies a role default as constitutional hard law, then generates apparently consistent witnesses.
WCPGC response: no internal runtime rule can fully save a bad compiler; only compiler audits, round-trip tests, and independent witness checks help.
Residual risk: this remains the sharpest implementation hazard.

## minimum_runtime_checks

These are the minimum fail-closed checks.

1. **Schema and canonical-hash check** for every packet.
2. **Canonical identity pinning** for `C`, `R`, and `Tχ` across compaction/resume/swap.
3. **Role materiality check**: no label-only role packets.
4. **Bridge witness completeness check** for every lower clause.
5. **Vocabulary closure check** against the declared action/effect/fact ontology.
6. **Non-widening check** over effect envelopes and ordered trace constraints.
7. **Residual quotient integrity check**: `Tρ` must be derivable from `Tχ`, `π`, and blocker facts.
8. **Runtime contamination scan** over `RuntimeFactStore`.
9. **Permission/feasibility separation check**: feasibility facts cannot create permission.
10. **Export legality check**: scope, warrant, TTL, target subsumption.
11. **Adapter trust check**: safe/degraded/unsafe plus effect-class gating.
12. **Hard-frontier selection check** before choosing next action.
13. **Maintenance isolation check**: no normal execution under partial constitutional update.
14. **Audit evidence emission** for every nontrivial verdict, especially defeated defaults, degraded trust, illegal export, and compaction/resume seams.

Without these, WCPGC collapses back into disciplined prose rather than strict governance.

## mapping_to_repo_implementation

The repo already leans schema-first and Pydantic-heavy, with transition enforcement in `packages/urm_runtime` and canonical artifact patterns in `packages/adeu_core_ir`. WCPGC fits that shape well.

### ConstitutionPacket

Implement as a new schema/model pair:

* schema under `spec/constitution_packet.schema.json`
* model/canonicalizer under `packages/adeu_core_ir` or `packages/adeu_commitments_ir`

Required fields:

* `canon_id`
* `ast_hash`
* `source_text_hash` optional for traceability, but not as legal identity
* `action_effect_ontology`
* `hard_norms`
* `global_defaults`
* `delegation_templates`
* `export_rules`
* `maintenance_rules`

This becomes the strict replacement for any prose-only inherited policy surface.

### RolePacket

The repo’s current `RolePolicy` registry in `packages/urm_runtime/src/urm_runtime/roles.py` is nominal. Under WCPGC it should become:

* display label + runtime affordance info, **plus**
* `role_packet_ref`

`RolePacket` fields:

* `role_id`
* `label`
* `defaults`
* `advisories`
* `authorized_hard_guards`
* `capability_assumptions`
* `bridge_witness_refs`

`requested_role` / `granted_role` remain useful for UX and routing, but they are no longer sufficient authority surfaces.

### TaskCharterPacket

Today the spawn path carries a raw `prompt` plus role/task-kind metadata. In WCPGC, the governing artifact should be `TaskCharterPacket`, and the prompt becomes explanatory mirror text, not execution law.

Required fields:

* `task_id`
* `ordered_clauses`
* `stop_conditions`
* `scoped_permissions`
* `completion_tests`
* `import_requirements`
* `bridge_witness_refs`

`AgentSpawnRequest` should be extended to carry:

* `task_charter_ref`
* `role_packet_ref`
* `export_artifact_refs`
* `adapter_overlay_ref`

### TaskResidualPacket

This should live near runtime code, because it is derived, not handwritten.

Required fields:

* `task_id`
* `charter_ref`
* `prefix_hash`
* `frontier`
* `pending`
* `satisfied`
* `blocked_by_fact_refs`
* `defeat_records`

Creation rule:

* only `derive_residual(Tχ, π, S)` may create or update it.

Persistence rule:

* compaction snapshots store `Tρ` by structured derived form, never as free recap prose.

### RuntimeFactStore

Implement in `packages/urm_runtime` as a strict typed store:

```text
RuntimeFactStore = {
  obs: [...],
  feas: [...],
  imported_fact_refs: [...],
  provenance: {...},
  freshness: {...}
}
```

Do not let current handoff/blocker/free-text surfaces become execution authority directly. If existing runtime artifacts such as blockers or reconciliation outputs are consumed operationally, they must first be typed either into:

* `obs` / `feas`, or
* `blocked_by_fact_refs` in `TaskResidualPacket`.

### AdapterOverlayPacket

Implement as a first-class packet, not hidden config.

Required fields:

* `adapter_id`
* `target_model_family`
* `translation_contract`
* `capability_profile`
* `overlay_controls`
* `influence_budget`
* `regression_suite_refs`
* `trust_class`

`swap_model` should refuse raw model-handle replacement without this packet.

### checked operators for spawn/compaction/resume/swap/maintenance

Add a new transition module in `packages/urm_runtime`, for example:

```text
packages/urm_runtime/src/urm_runtime/governance_transitions.py
```

with typed results:

```python
Result[NextConfig, TypedVerdict]
```

and operators:

* `checked_spawn(...)`
* `checked_compact(...)`
* `checked_resume(...)`
* `checked_swap_model(...)`
* `checked_enter_maintenance(...)`

Repo-specific upgrade points:

* extend `RuntimeEnforcementCandidate` to include packet refs and witness refs, not just role/task-kind strings
* extend `AgentSpawnRequest` / `AgentSpawnResponse` to carry packet refs/hashes
* extend `ContinuationBridgeRef` and `CompactionSeam` to include:

  * `constitution_ref`
  * `role_ref`
  * `task_charter_ref`
  * `task_residual_hash`
  * `adapter_ref`
* keep using deterministic canonicalization and hash patterns already common in `adeu_core_ir`

The important implementation move is this: the repo’s current role/task/scope enforcement becomes a pre-filter inside WCPGC, not the whole governance story.

## open_risks

The prior falsification criteria remain relevant here: if non-circular refinement fails, if fact-to-permission leakage remains structurally unavoidable, if model swap drift cannot be bounded, or if exact law identity still fails to preserve constitutionally relevant behavior, then the architecture is in trouble.

1. **Compiler trust**
   WCPGC assumes packets and witnesses are compiled correctly. A miscompiler can still create a formally neat but substantively wrong system.

2. **Ontology completeness**
   Hidden widening is only catchable if the action/effect ontology is sufficiently complete.

3. **Refinement-check cost**
   Full trace inclusion is expensive. WCPGC therefore needs a deliberately restricted DSL plus syntactic/SMT approximations.

4. **Adapter certification realism**
   `safe` may require empirical regression, not only static proof.

5. **Dual-use fact surfaces**
   Some artifacts genuinely mix description and salience. The firewall will need careful schema design to avoid both leakage and over-blocking.

6. **Residual growth**
   Long-running tasks may accumulate large residual state; compaction must preserve strategy-relevant information without reintroducing law drift.

7. **Legacy nominal surfaces in the repo**
   Existing role strings, raw prompts, and handoff summaries can silently bypass the packet discipline if not aggressively wrapped.

8. **Human maintenance leakage**
   Even with strict schemas, human constitutional changes can still smuggle contingent runtime concerns upward unless governance review is strong.

My judgment is that WCPGC is strong enough to implement as the alternate strict path. It is not complete in the mathematical sense, but it is precise enough to govern a real runtime, preserve typed intermediate verdicts, and expose the anchor bug class as a formal, testable condition rather than a post hoc narrative.
