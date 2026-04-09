## hardening_scope

WCPGC stays fixed. This is not a redesign and not a candidate-family reopen. The hardening target is the smallest `strict_v0` subset that closes the implementation gaps the prior stress-test already exposed: schema-compiled packets instead of prose, explicit witness surfaces for specialization, a real task charter/task residual split, a strict validation-vs-control split, and exact upper-layer identity across spawn/compaction/resume. This pass hardens only four surfaces: the restricted packet DSL, the BridgeWitness/compiler/projection-witness trust path, the TaskResidual quotient law, and executable action-selection semantics.

The key narrowing move for `strict_v0` is this: anything not needed to enforce `checkpoint first` over a broader defeasible role posture is deferred. That means identity-only vocabulary, no general theorem proving, no rich temporal operators beyond `first` and `before`, no role hardening, no residual export of obligations, and no general adapter ecology.

## restricted_packet_dsl

`strict_v0` uses a closed, finite JSON DSL. No free-form normative prose is executable.

### 1. Shared atoms

```text
ProfileId    := "wcpgc.strict_v0"

PacketKind   := constitution | role | task_charter | task_residual | runtime_fact_store | bridge_witness

ScopeKind    := repo_wide | subtree | module_set | file_set | artifact_surface_only
ArtifactSurf := implementation | governance | mixed | none

Scope :=
{
  kind: ScopeKind,
  values: [string],              // normalized repo-relative selectors
  artifact_surfaces: [ArtifactSurf]
}

PacketRef :=
{
  packet_kind: PacketKind,
  canon_id: string,
  ast_hash: string
}

EffectClass :=
  read_local | write_local | network_io | spawn_child | export_data | status_only

ActionSpec :=
{
  action_id: string,
  effect_classes: [EffectClass],
  allowed_scope_kinds: [ScopeKind]
}

FactKind := obs | feas

FactSchema :=
{
  fact_name: string,
  force: "factual",
  fact_kind: FactKind,
  exportable: boolean
}
```

`strict_v0` keeps the effect vocabulary small on purpose. Non-widening is checked over this fixed effect alphabet only.

### 2. Packet header

```text
Header :=
{
  schema: string,
  profile: "wcpgc.strict_v0",
  packet_kind: PacketKind,
  canon_id: string,
  ast_hash: string,
  instance_id?: string,               // runtime materialization only; never semantic
  scope: Scope,
  parent_packet_refs: [PacketRef],    // semantic parents
  source_refs: [string],              // provenance only
  projection_ref?:                    // authored packets only
  {
    manifest_ref: string,
    manifest_hash: string
  }
}
```

### 3. Allowed clause forms

#### ConstitutionPacket

```text
ConstitutionPacket :=
{
  header: Header(packet_kind=constitution),
  action_catalog: [ActionSpec],
  fact_catalog: [FactSchema],
  base_permissions:
    [
      {
        clause_id: string,
        clause_type: "permit",
        force: "hard",
        action_ids: [string],
        scope: Scope
      }
    ],
  hard_effect_forbids:
    [
      {
        clause_id: string,
        clause_type: "forbid_effects",
        force: "hard",
        effect_classes: [EffectClass]
      }
    ],
  export_rules:
    [
      {
        clause_id: string,
        clause_type: "export_allow" | "export_deny",
        force: "hard",
        fact_kind: "obs" | "feas",
        fact_names: [string],
        target_scope_kinds: [ScopeKind]
      }
    ]
}
```

#### RolePacket

Role is posture only in `strict_v0`.

```text
PreferenceClause :=
{
  clause_id: string,
  clause_type: "prefer",
  force: "default" | "advisory",
  action_ids: [string]
}

RolePacket :=
{
  header: Header(packet_kind=role),
  defaults: [PreferenceClause(force=default)],
  advisories: [PreferenceClause(force=advisory)]
}
```

#### TaskCharterPacket

```text
OrderClause :=
  {
    clause_id: string,
    clause_type: "first",
    force: "hard",
    action_id: string
  }
| {
    clause_id: string,
    clause_type: "before",
    force: "hard",
    predecessor: string,
    successor: string
  }

StopClause :=
{
  clause_id: string,
  clause_type: "stop_when",
  force: "hard",
  all_of_facts: [string]   // conjunction only
}

TaskCharterPacket :=
{
  header: Header(packet_kind=task_charter),
  hard_orders: [OrderClause],
  permissions:
    [
      {
        clause_id: string,
        clause_type: "permit",
        force: "hard",
        action_ids: [string],
        scope: Scope
      }
    ],
  stops: [StopClause],
  defaults: [PreferenceClause(force=default)],
  advisories: [PreferenceClause(force=advisory)]
}
```

#### RuntimeFactStore

```text
ObsFact :=
{
  fact_id: string,
  fact_name: string,
  evidence_ref: string,
  ts: string
}

FeasFact :=
{
  fact_id: string,
  fact_name: string,
  subject_action_id: string,
  status: "feasible" | "blocked",
  evidence_ref: string,
  ts: string
}

RuntimeFactStore :=
{
  header: Header(packet_kind=runtime_fact_store),
  obs: [ObsFact],
  feas: [FeasFact]
}
```

#### TaskResidualPacket

Derived only; never authored.

```text
TaskResidualPacket :=
{
  header: Header(packet_kind=task_residual),
  charter_ref: PacketRef,
  prefix_hash: string,
  satisfied: [string],
  pending: [string],
  frontier: [string],
  blocked_by_fact_refs: { string: [string] },    // action_id -> fact_ids; "__task_stop__" reserved
  defeat_records:
    [
      {
        defeated_clause_id: string,
        defeating_basis: "hard_frontier_preemption" | "task_stop_preemption"
      }
    ]
}
```

### 4. Forbidden clause forms

`strict_v0` rejects all of the following at compile time:

* arbitrary natural-language executable clauses
* nested boolean formulas
* disjunction, quantifiers, recursion, or modal nesting
* `until`, `next`, `after`, `unless`
* role hard clauses
* task hard clauses other than `first`, `before`, `stop_when`, and scoped `permit`
* constitutive “counts-as” rules
* numeric weights or soft priority arithmetic
* action symbols not present in `ConstitutionPacket.action_catalog`
* fact symbols not present in `ConstitutionPacket.fact_catalog`
* permissions induced from runtime facts
* export of residual obligations or salience artifacts
* vocabulary aliases or synonyms

### 5. What is intentionally left out of `strict_v0`

* conditional defaults
* residual-status guards in authored packets
* task/role clause priorities beyond force class
* generalized trace monitoring
* rich effect ontologies
* model-family overlays/adapters as executable packets

This is the smallest DSL that still represents hard ordered obligations, scoped permissions, factual typing, export rules, and defeasible role posture. The narrowing is deliberate because the prior analysis already identified packet over-elasticity, vocabulary drift, and prose compilation as core failure surfaces.

## dsl_normalization_and_canonicalization

`strict_v0` packet identity must be operational, not rhetorical.

### 1. Canonical semantic payload

For every authored packet `P`:

```text
semantic_payload(P) :=
{
  "schema": P.header.schema,
  "profile": P.header.profile,
  "packet_kind": P.header.packet_kind,
  "scope": norm_scope(P.header.scope),
  "body": norm_body(P.body)
}
```

The following fields are **not** part of `semantic_payload`:

* `instance_id`
* `source_refs`
* `projection_ref`
* any evidence or audit refs

Those are provenance/materialization, not law.

### 2. Normalization rules

Apply in this order:

1. all strings: trim outer whitespace and normalize to NFC
2. enums: lowercase canonical spelling only
3. unknown fields: reject
4. omitted defaults: inject explicit canonical defaults
5. list fields with set semantics: dedupe + lexicographically sort
6. clause ids:

   * if present, normalize
   * if absent, generate deterministically from clause payload
7. clause arrays:

   * sort by `clause_id`
8. `action_ids`, `effect_classes`, `fact_names`, `target_scope_kinds`:

   * dedupe + sort
9. `source_refs`:

   * dedupe + sort, but exclude from semantic hash
10. `parent_packet_refs`:

* sort by `(packet_kind, canon_id, ast_hash)`

### 3. Hash and identity rules

```text
ast_hash(P)  := sha256_canonical_json(semantic_payload(P))
canon_id(P)  := packet_kind + ":" + ast_hash(P)[0:24]
instance_id  := runtime-generated UUID-like materialization id
```

### 4. Equality notions

```text
semantic_equal(P,Q)  iff ast_hash(P) = ast_hash(Q)
same_law(P,Q)        iff canon_id(P) = canon_id(Q)      // equivalent to same ast_hash under strict_v0
same_instance(P,Q)   iff instance_id(P) = instance_id(Q)
same_provenance(P,Q) iff projection_ref(P)=projection_ref(Q) and source_refs(P)=source_refs(Q)
```

So:

* same `canon_id` + different `instance_id` = same law, different load
* same `source_refs` + different `ast_hash` = different law
* same `ast_hash` + different `source_refs` = same law, different provenance

### 5. Identity pinning consequences

Across spawn/compact/resume in `strict_v0`, the runtime pins:

* `ConstitutionPacket.canon_id/ast_hash`
* `RolePacket.canon_id/ast_hash`
* `TaskCharterPacket.canon_id/ast_hash`
* required `BridgeWitness` hashes
* required `ProjectionWitnessManifest` hash

`TaskResidualPacket` and `RuntimeFactStore` are not law-identity carriers.

## bridgewitness_schema_and_proof_obligations

`BridgeWitness` is the specialization proof surface for lower packets. It is required for `RolePacket` and `TaskCharterPacket`. `strict_v0` uses a deliberately small proof language: identity vocabulary, fixed admissibility bases, and syntactic non-widening certificates.

### 1. Schema

```text
BridgeWitness :=
{
  header: Header(packet_kind=bridge_witness),
  lower_packet_ref: PacketRef,
  upper_packet_refs: [PacketRef],
  scope: Scope,

  vocabulary_map:
    [
      {
        lower_symbol: string,
        upper_symbol: string,
        map_kind: "identity"
      }
    ],

  support_map:
    [
      {
        lower_clause_id: string,
        specialization_mode: "restriction" | "concretization" | "defeat",
        support_refs:
          [
            {
              ref_kind: "upper_clause" | "strict_profile_rule",
              packet_ref?: PacketRef,
              clause_id?: string,
              rule_id?: string
            }
          ],
        force_admissibility_basis:
          "SR1.role_defaults_only" |
          "SR2.task_hard_ordering" |
          "SR3.task_permission_subset" |
          "SR4.task_defaults_only" |
          "SR5.task_over_role_default_defeat",

        nonwidening_certificate:
          {
            cert_kind:
              "action_subset" |
              "effect_subset" |
              "scope_subset" |
              "order_restriction" |
              "default_slot_defeat",

            lower_action_ids: [string],
            upper_action_ids: [string],
            lower_effect_classes: [EffectClass],
            upper_effect_classes: [EffectClass],
            scope_relation: "equal" | "subset",
            check_passed: boolean
          }
      }
    ],

  evidence_refs: [string]
}
```

### 2. Fixed admissibility rules for `strict_v0`

These are profile rules, not new runtime layers.

```text
SR1: RolePacket may contain only default/advisory preference clauses.
SR2: TaskCharterPacket may introduce hard local order via first/before and hard stop_when.
SR3: TaskCharterPacket may narrow permission only by action subset + scope subset.
SR4: TaskCharterPacket may contain only default/advisory preference clauses beyond hard order/stop/permit.
SR5: An active task clause may defeat a role default locally; it may not rewrite or erase it.
```

### 3. Proof obligations

#### A. Role packet lawfully specializes constitution

For every role clause `r`:

```text
1. force(r) ∈ {default, advisory}
2. clause_type(r) = prefer
3. action_ids(r) ⊆ Constitution.action_catalog
4. ⋃ Eff(action_ids(r)) ⊆ Constitution.effect_catalog
5. scope(Role) ⊆ scope(Constitution)
6. vocabulary_map entries are identity-only
7. support_map(r).force_admissibility_basis = SR1.role_defaults_only
8. nonwidening_certificate.check_passed = true
```

What is shown in `strict_v0`:

* syntactically, role posture does not create new actions, effects, or permissions
* role is posture, not law

What is **not** shown in `strict_v0`:

* that the role default is globally optimal
* that the source prose was semantically perfect

#### B. Task charter lawfully specializes role + constitution

For every task hard order clause `t`:

```text
1. force(t) = hard
2. clause_type(t) ∈ {first, before}
3. referenced actions ⊆ Constitution.action_catalog
4. no cycle in the induced order graph
5. at most one distinct unconditional first(a)
6. scope(Task) ⊆ scope(Constitution)
7. support_map(t).force_admissibility_basis = SR2.task_hard_ordering
8. nonwidening_certificate.cert_kind = order_restriction
```

For every task permission clause `p`:

```text
1. force(p) = hard
2. clause_type(p) = permit
3. action_ids(p) ⊆ action_ids of some Constitution.base_permissions clause
4. scope(p) ⊆ scope of supporting Constitution.base_permissions clause
5. support_map(p).force_admissibility_basis = SR3.task_permission_subset
6. cert_kind ∈ {action_subset, effect_subset, scope_subset}
```

For every task default/advisory `d`:

```text
1. force(d) ∈ {default, advisory}
2. clause_type(d) = prefer
3. action_ids(d) ⊆ Constitution.action_catalog
4. support_map(d).force_admissibility_basis = SR4.task_defaults_only
```

#### C. Task clause may defeat role default

This is the key local adjudication witness.

Compile-time admissibility:

```text
1. upper clause force ∈ {default, advisory}
2. upper clause type = prefer
3. lower packet = task_charter
4. lower clause type ∈ {first, before, stop_when, prefer}
5. scope(Task) ⊆ scope(Role)
6. nonwidening_certificate.cert_kind = default_slot_defeat
7. support_map(lower).force_admissibility_basis = SR5.task_over_role_default_defeat
```

Runtime activation condition:

```text
The defeat is realized only if the lower clause is active at the current decision slot.
```

So BridgeWitness proves **admissibility of defeat**, not that defeat always occurs.

#### D. Local hardening admissibility

In `strict_v0`, a lower hard clause is admissible **only** if it is one of:

* `first(a)`
* `before(a,b)`
* `stop_when(facts)`
* `permit(action_subset, scope_subset)`

Everything else is rejected.

### 4. What is syntactic vs approximated

Syntactic in `strict_v0`:

* vocabulary closure
* identity-only vocabulary map
* action subset
* effect subset
* scope subset
* order graph cycle detection
* distinct-`first` contradiction detection

Approximated:

* global satisfiability beyond direct order contradictions
* semantic completeness of the effect vocabulary
* whether a source fragment’s natural-language interpretation was the only reasonable one

This is intentionally narrow because the prior analysis identified compiler smuggling and post hoc witness rationalization as major risks.

## projection_witness_contract

The compiler must not be an invisible constitutional editor. `strict_v0` therefore requires a manifest-level projection witness for every authored packet set.

### 1. Projection witness schema

```text
ProjectionWitnessManifest :=
{
  schema: "wcpgc_projection_witness@0.1",
  profile: "wcpgc.strict_v0",
  projection_id: string,
  compiler_name: string,
  compiler_version: string,
  compiler_entrypoint: string,

  source_artifact_refs: [string],
  source_set_hash: string,

  fragment_decisions:
    [
      {
        fragment_id: string,
        source_ref: string,
        span: {start_line, start_col, end_line, end_col},
        raw_text_hash: string,
        normalized_text_hash: string,
        status: "accepted" | "rejected" | "ambiguous",
        assigned_layer: "constitution" | "role" | "task" | "runtime" | "reject",
        decision_rule_ids: [string],
        extracted_clause_ids: [string]
      }
    ],

  rejected_fragments:
    [
      {
        fragment_id: string,
        reason_code:
          "UNSUPPORTED_FORM" |
          "LAYER_AMBIGUOUS" |
          "FORCE_AMBIGUOUS" |
          "UNKNOWN_ACTION" |
          "UNKNOWN_FACT" |
          "NON_IDENTITY_VOCAB" |
          "RUNTIME_NORM_LAUNDERING"
      }
    ],

  ambiguity_flags:
    [
      {
        fragment_id: string,
        ambiguity_kind: "layer" | "force" | "symbol" | "scope"
      }
    ],

  generated_packets:
    [
      {
        packet_kind: string,
        canon_id: string,
        ast_hash: string,
        output_ref: string,
        clause_ids: [string]
      }
    ],

  bridge_witness_refs: [string],

  coverage_hash: string,

  round_trip_hooks:
    {
      replay_entrypoint: string,
      normalized_clause_dump_ref: string,
      packet_hash_check: boolean
    }
}
```

### 2. Trust contract

A packet bundle is trusted in `strict_v0` iff all of the following hold:

```text
1. manifest.profile = "wcpgc.strict_v0"
2. every accepted fragment has exactly one assigned layer
3. accepted fragments have zero ambiguity flags
4. every source fragment is accounted for as accepted, rejected, or ambiguous
5. every generated packet in the manifest exists and hash-matches
6. every generated clause id is covered by at least one accepted fragment
7. RolePacket and TaskCharterPacket each have required BridgeWitness refs
8. coverage_hash recomputes exactly
```

There is no compiler-side degraded mode in `strict_v0`:

* missing manifest => reject
* ambiguity in accepted fragment => reject
* packet hash mismatch => reject
* clause coverage gap => reject

### 3. Round-trip / audit hooks

`strict_v0` requires only bounded replay, not semantic theorem proving.

Minimum audit hooks:

* `replay_entrypoint`
* `source_set_hash`
* `normalized_clause_dump_ref`
* `coverage_hash`
* emitted packet refs and hashes
* emitted BridgeWitness refs

This is enough for later replay and offline audit without making the runtime ingest raw prose.

## taskresidual_quotient_law

`derive_residual(Tχ, π, S)` is a pure runtime function over a charter, a canonical trace prefix, and a typed fact store.

### 1. Inputs it may read

Only these inputs are legal:

```text
Tχ : canonical TaskCharterPacket
π  : canonical trace prefix of executed action events
S  : canonical RuntimeFactStore
```

Where:

```text
TraceEvent :=
{
  seq: int,
  action_id: string,
  outcome: "completed" | "failed" | "denied"
}
```

Only `outcome="completed"` counts toward satisfaction.

`derive_residual` may **not** read:

* RolePacket
* Constitution prose
* raw prompt text
* parent narrative summaries
* model-family hints
* raw event logs beyond canonicalized `TraceEvent[]`

### 2. Outputs it may emit

Only these:

* `charter_ref`
* `prefix_hash`
* `satisfied`
* `pending`
* `frontier`
* `blocked_by_fact_refs`
* `defeat_records`

### 3. Outputs it may never emit

Never:

* new permissions
* new obligations
* new defaults or priorities
* upper-layer summaries
* role-default defeat records
* free-prose blockers
* unsourced blocker claims
* imported runtime momentum
* recommended next actions

### 4. Quotient construction

Let `Ord(Tχ)` be the set of hard order clauses in the charter.

Construct the hard order graph `Gχ = (V,E)`:

```text
V := all action_ids appearing in hard_orders
E := { (a,b) | before(a,b) in hard_orders }
```

For every `first(a)` in `hard_orders`, add:

```text
(a,x) for every x ∈ V and x ≠ a
```

Then reject if:

* `Gχ` has a cycle
* more than one distinct `first(a)` exists

Now compute:

```text
completed(π) := { e.action_id | e in π and e.outcome = "completed" }

satisfied := sort(V ∩ completed(π))
pending   := sort(V \ satisfied)

frontier := sort(
  { a ∈ pending | predecessors_Gχ(a) ⊆ satisfied }
)
```

Important: `frontier` is **order-semantic only**. It does not include feasibility.

### 5. Blockers

`blocked_by_fact_refs` is the feasibility/stop shell over the stable order core.

For each action `a` in `frontier ∪ pending`:

```text
blocked_by_fact_refs[a] :=
  sorted({
    f.fact_id
    | f ∈ S.feas
    and f.subject_action_id = a
    and f.status = "blocked"
  })
```

For hard stop conditions:

```text
blocked_by_fact_refs["__task_stop__"] :=
  sorted({
    f.fact_id
    | f ∈ S.obs
    and f.fact_name satisfies all_of_facts of some stop_when clause
  })
```

No free text is allowed in blockers. Every blocker must be a fact id.

### 6. Defeat records

In `strict_v0`, `TaskResidual.defeat_records` is deliberately narrow.

It records only **task-charter-local** default preemption, not role-default defeat.

```text
defeat_records :=
  [
    {
      defeated_clause_id: d.clause_id,
      defeating_basis: "hard_frontier_preemption"
    }
    for each active task default d
    if frontier ≠ ∅ and (d.action_ids ∩ frontier) = ∅
  ]
```

If `blocked_by_fact_refs["__task_stop__"]` is non-empty, then task defaults that still prefer ordinary actions may receive:

```text
defeating_basis = "task_stop_preemption"
```

Role-default defeat is computed at step selection time and emitted as a runtime verdict, not stored in `TaskResidualPacket`. That keeps the quotient pure: it depends only on `Tχ`, `π`, and `S`.

### 7. Stable core vs volatile shell

This is the compaction law for residuals.

```text
stable_core(Tρ)   := { charter_ref, prefix_hash, satisfied, pending, frontier }
volatile_shell(Tρ):= { blocked_by_fact_refs, defeat_records }
```

Compaction may serialize both.

Resume must:

* verify `stable_core` against `derive_residual(Tχ, π, ∅)`-equivalent order reconstruction
* recompute `volatile_shell` from live `S`

So compaction preserves residual **without mutating the charter**, and resume cannot silently turn cached blockers or cached defeats into new law.

## validation_vs_action_selection_executable_rule

Validation and next-step choice are separate functions. They must stay separate because the prior stress test correctly identified that `C → R → T → S` as a validation order is not the same thing as “consult C then R then T then S” for next-action control.

### 1. Validation order

```text
validate(Γ):
  1. load ConstitutionPacket, RolePacket, TaskCharterPacket
  2. validate schema + canonical hash + pinned refs
  3. validate ProjectionWitnessManifest(s)
  4. validate BridgeWitness(Role -> Constitution)
  5. validate BridgeWitness(Task -> Role+Constitution)
  6. validate RuntimeFactStore typing + contamination scan
  7. derive TaskResidualPacket = derive_residual(Tχ, π, S)
  8. compute trust_state
  9. return ValidatedState Σ
```

Validation answers:

* are packets trusted?
* are witnesses valid?
* is runtime factual and clean?
* what is the residual?

Validation does **not** choose an action.

### 2. Candidate universe

`strict_v0` action selection is closed-world.

```text
declared_actions(Σ) :=
  actions referenced in:
    - Tχ.hard_orders
    - Tχ.defaults/advisories
    - R.defaults/advisories

meta_actions :=
  { emit_blocked_status, request_more_facts, escalate }

candidate_actions := declared_actions(Σ) ∪ meta_actions
```

No other next action is legal in `strict_v0`.

### 3. Legal base

```text
legal_base :=
  {
    a ∈ candidate_actions
    | a ∈ Constitution.action_catalog
    | a permitted by Constitution.base_permissions
    | if Task.permissions non-empty: a also permitted by Task.permissions
    | effects(a) not forbidden by Constitution.hard_effect_forbids
  }
```

Runtime facts do not add to `legal_base`. They only gate feasibility and stop.

### 4. Feasibility

```text
feasible(a,S,Tρ) :=
  blocked_by_fact_refs[a] = []
  and blocked_by_fact_refs["__task_stop__"] = []
```

### 5. Hard-frontier precedence

```text
HardFrontier := Tρ.frontier
FeasibleHard := { a ∈ HardFrontier | feasible(a,S,Tρ) }
```

Selection rule:

```text
if blocked_by_fact_refs["__task_stop__"] ≠ []:
    legal_next := { emit_blocked_status, escalate }

elif HardFrontier ≠ [] and FeasibleHard = []:
    legal_next := { emit_blocked_status, request_more_facts, escalate }
    status := blocked

elif HardFrontier ≠ [] and FeasibleHard ≠ []:
    legal_next := FeasibleHard

else:
    legal_next := { a ∈ legal_base | feasible(a,S,Tρ) }
```

The crucial point is:

* if `HardFrontier` exists, defaults are **not** consulted to widen `legal_next`
* blocked frontier does **not** fall back to role exploration
* the only fallback is the fixed meta-action set

### 6. Default consultation

Defaults are consulted only when `HardFrontier = ∅`, or to rank among multiple members of `FeasibleHard`.

Define active preferences:

```text
task_defaults := Tχ.defaults
role_defaults := R.defaults
task_advisories := Tχ.advisories
role_advisories := R.advisories
```

Score each `a ∈ legal_next` by:

```text
score(a) :=
(
  count of task default clauses whose action_ids do not contain a,
  count of role default clauses whose action_ids do not contain a,
  count of advisory clauses whose action_ids do not contain a,
  a                      // lexicographic tie-break on action_id
)
```

Choose:

```text
choose(Σ) := argmin_a score(a)
```

That tie-break is deterministic and deliberately non-model-based.

### 7. Defeated vs violated defaults

A default is **defeated**, not violated, iff:

```text
default d is active
and legal_next ∩ d.action_ids = ∅
because of a higher-force or more-specific clause
```

A default is merely **not satisfied by the chosen action** iff:

```text
legal_next ∩ d.action_ids ≠ ∅
but another legal action wins on the full score tuple
```

So defeat is a legality fact. Non-satisfaction is a ranking fact.

### 8. Anchor case

Let:

```text
R.defaults = [ prefer {explore, document} ]          // role posture
Tχ.hard_orders = [ first(checkpoint), before(checkpoint, inspect) ]
π = []
S.feas says checkpoint feasible, explore feasible, document feasible
S.obs has no stop facts
```

Then:

```text
V = {checkpoint, inspect}
E = {(checkpoint, inspect)}
satisfied = []
pending = [checkpoint, inspect]
frontier = [checkpoint]
blocked_by_fact_refs[checkpoint] = []
blocked_by_fact_refs["__task_stop__"] = []
```

So:

```text
HardFrontier = {checkpoint}
FeasibleHard = {checkpoint}
legal_next = {checkpoint}
```

Role default `prefer {explore, document}` is active, but:

```text
legal_next ∩ {explore, document} = ∅
```

because of an active task hard frontier. Therefore the correct runtime record is:

```text
defeated_default(
  defeated_role_clause = role_prefer_explore_document,
  defeating_basis = active_task_hard_frontier
)
```

and the chosen next action is:

```text
checkpoint
```

That is exactly the motivating case: task-local hard order controls the next step, while the broader role posture survives as a defeasible default rather than being silently promoted into law or silently erased.

If `checkpoint` is blocked by feasibility facts, then:

```text
HardFrontier = {checkpoint}
FeasibleHard = ∅
legal_next = {emit_blocked_status, request_more_facts, escalate}
```

and `explore` / `document` remain illegal at that point.

## strict_v0_enforcement_profile

### 1. Pinned identities

`strict_v0` pins these at session start and across compaction/resume:

* `ConstitutionPacket.canon_id + ast_hash`
* `RolePacket.canon_id + ast_hash`
* `TaskCharterPacket.canon_id + ast_hash`
* required `BridgeWitness` hashes
* required `ProjectionWitnessManifest` hash
* `model_family`
* `model_major_version`

It does **not** pin:

* `TaskResidualPacket` as law identity
* `RuntimeFactStore`
* arbitrary prompt text

### 2. Checked operators

Checked in `strict_v0`:

* packet acceptance
* spawn
* factual export
* compact
* resume
* next-step selection

Not supported in `strict_v0`:

* general model swap
* maintenance transition
* overlay install

### 3. Fail-closed verdicts

These are hard deny/reject:

* malformed packet
* projection manifest missing
* accepted-fragment ambiguity
* bridge witness missing
* hash mismatch
* illegal widening
* illegal permission subset failure
* role under-instantiated
* runtime contamination
* illegal fact export
* unknown action symbol
* pinned identity mismatch on resume
* cross-family model change

### 4. Verdicts that may degrade trust

Only one degraded path exists in `strict_v0`:

```text
same model_family
same model_major_version
different patch/minor runtime evaluator identity
```

That yields:

```text
trust_state = degraded_trust
```

not immediate reject.

### 5. Allowed effects under degraded trust

Under `degraded_trust`, only actions whose full effect set is a subset of:

```text
{ read_local, status_only }
```

may proceed.

So degraded trust may still allow:

* read-only checkpointing
* read-only inspection
* blocked-status emission
* escalation/request-more-facts meta-actions

It may **not** allow:

* write-local actions
* network I/O
* spawn
* factual export
* any cross-session propagation

### 6. Boolean gates

`strict_v0` exposes these booleans:

```text
accept_packet_bundle?
allow_spawn?
allow_compact?
allow_resume?
allow_export?
allow_action(a)?
```

with the obvious projections:

```text
allow_action(a) :=
  packet_bundle_trusted
  ∧ witnesses_valid
  ∧ runtime_clean
  ∧ a ∈ legal_next
  ∧ trust_allows(effects(a))
```

`defeated_default` does not force boolean denial. `contaminated`, `illegal_widening`, `illegal_export`, and identity mismatch do.

## minimum_repo_changes_for_v0

Observed in the repo: `urm_runtime` already has canonical JSON hashing, spawn models, runtime enforcement candidates, and compaction/continuation bridge surfaces; `adeu_commitments_ir` already owns schema-heavy semantic governance models; and `adeu_semantic_compiler` already owns deterministic compilation patterns. The minimum change set should follow those existing seams, not create a second architecture.

### 1. `ConstitutionPacket`, `RolePacket`, `TaskCharterPacket`

Add authored packet schemas and models under the semantic-governance lane:

* `packages/adeu_commitments_ir/schema/wcpgc_constitution_packet@0.1.json`
* `packages/adeu_commitments_ir/schema/wcpgc_role_packet@0.1.json`
* `packages/adeu_commitments_ir/schema/wcpgc_task_charter_packet@0.1.json`
* `packages/adeu_commitments_ir/schema/wcpgc_bridge_witness@0.1.json`
* `packages/adeu_commitments_ir/schema/wcpgc_projection_witness@0.1.json`

and one new implementation module, e.g.:

* `packages/adeu_commitments_ir/src/adeu_commitments_ir/wcpgc_packets.py`

That module should own:

* Pydantic models
* normalization
* canonical semantic payload dump
* `ast_hash` / `canon_id` helpers

### 2. compiler / projection witness output

Extend the semantic compiler, not the runtime, to emit the authored packet bundle.

Minimum path:

* add a `strict_v0` emission target in
  `packages/adeu_semantic_compiler/src/adeu_semantic_compiler/compile.py`
  or a sibling module such as
  `packages/adeu_semantic_compiler/src/adeu_semantic_compiler/strict_v0.py`

Compiler outputs:

* `ConstitutionPacket.json`
* `RolePacket.json`
* `TaskCharterPacket.json`
* `BridgeWitness.role.json`
* `BridgeWitness.task.json`
* `ProjectionWitnessManifest.json`

The compiler must fail closed on ambiguity for accepted fragments.

### 3. `AgentSpawnRequest` / runtime binding

Current `AgentSpawnRequest` in `packages/urm_runtime/src/urm_runtime/models.py` carries `prompt`, role/task-kind, and delegated scope, but no law packet refs.

Add a nested strict binding:

```text
StrictGovernanceBinding :=
{
  constitution_ref,
  role_packet_ref,
  task_charter_ref,
  role_bridge_witness_ref,
  task_bridge_witness_ref,
  projection_manifest_ref,
  model_family,
  model_version
}
```

Then extend:

* `AgentSpawnRequest`
* `AgentSpawnResponse`

with optional `strict_binding`. For `strict_v0` requests, it becomes mandatory.

`prompt` remains, but becomes non-authoritative explanatory mirror text.

### 4. `RolePacket` vs current `roles.py`

Current `roles.py` is nominal transport/sandbox/tool policy. Keep it for transport and tooling, but extend `RolePolicy` to include:

```text
role_packet_ref: str | None
```

For `strict_v0`, a role label without `role_packet_ref` is invalid.

### 5. `TaskResidualPacket` and `RuntimeFactStore`

These should be runtime-side, not compiler-side.

Add new runtime models in a new module, e.g.:

* `packages/urm_runtime/src/urm_runtime/strict_governance.py`

or split:

* `strict_runtime_facts.py`
* `strict_residual.py`

Implement there:

* `RuntimeFactStore`
* `TaskResidualPacket`
* `derive_residual(Tχ, π, S)`

### 6. checked spawn / compact / resume operators

In the same runtime module, add:

* `checked_spawn_strict_v0`
* `checked_compact_strict_v0`
* `checked_resume_strict_v0`
* `select_next_action_strict_v0`

These should consume the new packet refs/hashes and emit typed verdicts.

### 7. `ContinuationBridgeRef` and `CompactionSeam`

Current `orchestration_state.py` bridge/seam models are audit-stream oriented. Extend them minimally with optional strict fields:

```text
constitution_ref
role_packet_ref
task_charter_ref
projection_manifest_ref
role_bridge_witness_ref
task_bridge_witness_ref
prefix_hash
model_family
model_version
trust_state
```

No new seam class is required if optional fields are acceptable.

### 8. typed verdict return surface

Current `runtime_enforcement.py` is mostly boolean/exception oriented. Add one typed verdict model there or in the new strict module:

```text
StrictVerdict :=
{
  verdict:
    "valid" |
    "invalid" |
    "blocked" |
    "underdetermined" |
    "contaminated" |
    "degraded_trust" |
    "defeated_default",

  code: string,
  evidence_refs: [string],
  defeated_clause_refs: [string],
  packet_refs: [string]
}
```

Then wrap boolean gates around that instead of replacing it.

### 9. `AdapterOverlayPacket`

Do **not** add it in `strict_v0`.

Minimum rule instead:

* cross-family swap: reject
* same-family patch/minor drift: degraded trust only

That keeps `strict_v0` bounded.

## what_to_defer_to_v1_1

Do not attempt these in `strict_v0`:

* general theorem proving of non-widening
* non-identity vocabulary maps
* conditional defaults
* `until` / `next` / richer temporal operators
* role hard clauses
* exported residual obligations with subsumption proofs
* explicit `AdapterOverlayPacket`
* cross-family model swap semantics
* full maintenance governance machinery
* rich overlay/autonomy ecology
* semantic equivalence proofs across compaction snapshots
* complex runtime trace monitoring beyond the required residual quotient
* broad natural-language ambiguity repair instead of fail-closed rejection

`strict_v0` should be intentionally austere.

## remaining_formal_risks

The hardening above materially reduces ambiguity, but it does not eliminate the main risks the earlier analysis already surfaced: compiler smuggling, hidden widening through ontology loss, facts acquiring de facto permission, model drift, and the possibility that exact law identity still fails to preserve constitutionally relevant behavior.

1. **Compiler trust remains the largest risk.**
   Projection manifests make the compiler visible, but they do not prove the layer assignment is substantively correct. A deterministic miscompiler is still a dangerous compiler.

2. **Ontology incompleteness can still hide widening.**
   `strict_v0` checks only the declared action/effect vocabulary. If a dangerous side effect is omitted from `ActionSpec.effect_classes`, the non-widening certificate can pass while behavior still widens.

3. **Non-widening is still only syntactic in `strict_v0`.**
   Action subset, effect subset, and scope subset are necessary, not sufficient. They do not capture all semantic broadening.

4. **Dual-use facts remain a real pressure point.**
   Even with typed `obs` / `feas`, some “facts” still carry salience. The prior countermodels around phenomenology leak and fact-to-permission laundering remain relevant, just narrowed.

5. **Model-family drift is only bounded, not solved.**
   Denying cross-family swap and degrading same-family drift is safer, but it does not prove stable ranking behavior under all ambiguity cases.

6. **Residual bloat across long compaction chains is still open.**
   The stable-core/volatile-shell split helps, but long prefixes and blocker histories can still grow enough to require later summarization or compression rules.

7. **Vacuous role packets are still possible if content minima are weak.**
   Requiring a `role_packet_ref` is necessary, but the packet also needs minimum substantive content checks, or nominal collapse just moves one layer deeper.

This is the bounded subset I would hand to Codex for `strict_v0`: identity-only packet DSL, binary compiler trust with explicit projection manifests, pure residual quotienting, and deterministic hard-frontier-first action selection.
