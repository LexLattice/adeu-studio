# ARCHITECTURE: ADEU Conceptual-First Retrieval Pipeline v0

**Status:** architecture / doctrine recommendation.
**Authority posture:** this note proposes a new ADEU-native retrieval family. It does not authorize implementation, schema release, ANM authority promotion, or runtime behavior by itself.

## 1. Executive thesis

Current retrieval makes the worker/model reconstruct its conceptual neighborhood every time. The worker must repeatedly guess aliases, implementation surfaces, witness forms, neighboring concepts, storage substrates, lifecycle concepts, and failure modes before it can even search. That behavior is unstable, prompt-sensitive, non-exhaustive, and difficult to audit.

ADEU should externalize that recurring reasoning burden into a canonical, auditable, additive semantic broker:

```text
worker declares retrieval intent
  -> broker resolves intent to canonical ODEU concepts
  -> broker proposes bounded typed expansion options
  -> worker selects axes / depth / budget / stores
  -> broker expands deterministically
  -> broker queries shallow evidence stores
  -> broker returns evidence candidates + coverage report
  -> worker reasons over served evidence or requests another expansion
  -> auditor checks claim/evidence/coverage alignment
```

The worker should not have to invent the whole conceptual zone. It should declare:

```text
what it needs to know
why it needs to know it
which O/E/D/U lanes are active
which typed conceptual axes may expand
how far expansion may go
what evidence would count
what drift/noise budget is acceptable
which evidence stores are admissible
```

The broker should then serve a deterministic retrieval result relative to a versioned canonical concept graph, a declared source set, and selected evidence stores.

**Observed repo grounding**

Targeted inspection found adjacent doctrine but no first-class `CanonicalODEUConceptDB`, `SemanticBroker`, `ConceptualSearchPlan`, or `EvidenceCoverageReport` surface.

Relevant observed grounding:

* `docs/ARCHITECTURE_ADEU_STUDIO_v0.md` establishes O/E/D/U as system methodology and emphasizes typed IR, explicit evidence, fail-closed validation, stable hashes, and ADEU-native methodology. See `docs/ARCHITECTURE_ADEU_STUDIO_v0.md:21-36`, `:215-229`, and `:435-464`.
* `docs/support/anm.adeu.md` establishes ANM authority-layer discipline: prose remains prose; normative semantics come only from recognized authority blocks such as `D@1`. See `docs/support/anm.adeu.md:17-19`, `:109-114`, `:122-167`, and `:319`.
* `docs/DRAFT_SCHEMA_META_CORE_v0.md` and `docs/support/ADEU_SCHEMA_META_GRAMMAR.md` establish common-envelope / carrier-overlay / lineage-overlay / named-residual schema posture, plus explicit anchors, governance, evidence, lineage, and O/E/D/U realization. See `docs/DRAFT_SCHEMA_META_CORE_v0.md:22-57`, `:69-90`, `:181-193`, and `docs/support/ADEU_SCHEMA_META_GRAMMAR.md:50-123`.
* `docs/ARCHITECTURE_ADEU_OPERATOR_PROJECTION_FAMILY_v0.md` establishes that projection and visibility do not mint authority. See `docs/ARCHITECTURE_ADEU_OPERATOR_PROJECTION_FAMILY_v0.md:15-43`, `:107-110`, and `:125-140`.
* `docs/support/DRAFT_MORPHIC_UX_GOVERNED_ENACTMENT_PROTOCOL_v0.md` explicitly treats repeated hidden reasoning substitutes as burdens that should be logged and promoted only through bounded support surfaces. See `docs/support/DRAFT_MORPHIC_UX_GOVERNED_ENACTMENT_PROTOCOL_v0.md:68-73`, `:75-96`, `:139-153`, and `:275-307`.
* Resident-agent continuation and communication docs establish that raw transcript and generic memory must not become task law, continuation identity, or witness by default. See `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_FAMILY_v0.md:52-77` and `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_FAMILY_v0.md:44-69`.
* Existing brokered reflexive execution artifacts provide adjacent precedent for compiled plans, explicit route order, role-gated phases, and non-goals around raw markdown execution. See `docs/implementation_slices/vnext_plus71/V38-A_brokered_reflexive_execution.md:11-43`.

**Inferred:** conceptual-first retrieval should become a bounded institutional retrieval component, not another LLM prompt style.

**Recommended:** introduce a small v0 family centered on:

```text
CanonicalODEUConceptDB
SemanticBroker
ConceptualSearchPlan
EvidenceCoverageReport
```

---

## 2. Problem statement

The retrieval problem is not merely “bad keywords.” Normal search collapses several distinct acts into one unstable prompt:

```text
identify relevant concepts
  + invent aliases
  + infer neighboring concepts
  + decide which relations matter
  + generate queries
  + retrieve chunks
  + classify evidence
  + remember coverage gaps
```

This causes ADEU-specific failures:

| Domain                                | Failure                                                                                                           |
| ------------------------------------- | ----------------------------------------------------------------------------------------------------------------- |
| Repo search                           | Worker searches one phrase and misses implementation surfaces under local vocabulary.                             |
| Agent harness state recovery          | Transcript memory or continuity context is confused with typed continuation state.                                |
| ProgramBench-style black-box recovery | Command ontology, config precedence, defaults, side effects, negative behavior, and parser precedence are missed. |
| ANM / D@1 retrieval                   | Support prose, architecture drafts, generated views, and recognized normative authority blocks are conflated.     |
| Long-context / sparse-attention runs  | Lexical hits are retrieved but witness slots remain uncovered.                                                    |
| Test/witness discovery                | Worker misses negative probes, fixture surfaces, edge cases, or no-witness checks.                                |
| Capability-probe routing              | Tests, probe templates, edge classes, witness forms, and failure modes are not expanded consistently.             |

The core failure is conceptual coverage, not string matching.

ADEU already separates ontology, evidence, deontic authority, and utility tradeoffs. Retrieval should preserve the same separation.

---

## 3. Core doctrine

### 3.1 Retrieval begins from canonical concepts

The worker may say:

```text
I need to find where runtime model/provider selection is persisted.
```

The worker should not have to manually invent:

```text
provider choice
model selection
profile selection
fallback/default
runtime config
environment variable
SQLite row
worker run
copilot session
capability probe
provider parity
IPC update path
frontend state
storage substrate
```

The broker should resolve the intent against canonical ODEU concepts and expose a bounded option space.

### 3.2 Relation axes are closed and typed

The canonical DB is not a synonym table. It is a typed graph.

The worker does not ask for “related things.” The worker selects typed axes:

```text
alias
genus
species
sibling
part_whole
implementation_surface
evidence_surface
deontic_law
utility_axis
test_witness_template
failure_mode
lifecycle_phase
storage_substrate
protocol_action_surface
domain_specific_edge_class
```

### 3.3 Lexical hits are not evidence witnesses

A lexical match is an evidence candidate at most.

The broker must distinguish:

```text
term appears in source
  vs
source structurally implements the concept
  vs
source is an admissible witness for a claim
  vs
source is authority-bearing for D-lane law
```

This follows the repo’s broader witness discipline:

```text
raw transcript is not native witness
support docs do not mint runtime authority
projection is not ratification
generated views are not authority by themselves
candidate evidence is not proof
```

### 3.4 Exhaustiveness is bounded

The broker cannot say:

```text
all relevant evidence has been found
```

It can say:

```text
all selected concepts, relation axes, depths, confidence tiers,
and evidence stores in this plan were expanded and searched,
except the listed skipped / clipped / failed branches
```

That is the ADEU form of retrieval exhaustiveness: closed relative to an explicit source set and plan envelope.

### 3.5 No authority laundering

The broker retrieves and classifies. It does not promote prose into law, chunks into proof, UI projection into authority, or candidate relations into canonical ontology.

For D-lane retrieval, only authority-admissible sources can satisfy normative claims. ANM/D@1 authority posture must remain explicit.

---

## 4. End-to-end pipeline

### 4.1 Primary data flow

```text
RetrievalIntent@1
  -> concept resolution
  -> expansion option set
  -> worker-selected expansion envelope
  -> ConceptualSearchPlan@1
  -> deterministic graph expansion
  -> QueryBranch@1 records
  -> shallow store adapter calls
  -> EvidenceCandidate@1 records
  -> EvidenceCoverageReport@1
  -> worker answer / further expansion / audit
  -> optional ConceptDBPatchProposal@1
```

### 4.2 Primary control flow

The protocol is intentionally two-stage.

**Stage A — Intent and options**

The worker declares what it needs. The broker resolves canonical concepts and proposes legal expansion axes. Ambiguous or unresolved terms are returned explicitly.

**Stage B — Bounded expansion and retrieval**

The worker selects axes, depth, stores, confidence tier, and budget. The broker expands deterministically and retrieves evidence candidates. The coverage report records what was searched and what remains open.

This prevents both under-searching by vibes and over-searching by uncontrolled semantic sprawl.

### 4.3 Worker / harness responsibilities

The worker or harness provides:

```text
active task frame
retrieval objective
reason for retrieval
desired O/E/D/U lanes
seed terms and/or seed concept IDs
required evidence kinds
admissibility requirements
preferred axes
forbidden axes
allowed stores
forbidden stores
recall/precision posture
noise budget
cost/budget limits
authority boundary for D-lane retrieval
prior coverage report refs, if continuing
```

The worker may formulate intent and choose from broker options. It must not silently introduce unexpanded concepts as if they were covered.

### 4.4 Broker responsibilities

The broker must:

```text
validate RetrievalIntent@1
resolve terms to canonical concepts
report ambiguity and unresolved terms
propose bounded expansion options
expand the concept graph deterministically
generate stable query branches
call shallow evidence-store adapters
classify returned chunks as candidates
preserve branch provenance and relation paths
distinguish lexical matches from witnesses
emit drift warnings
emit coverage accounting
report unresolved slots
produce deterministic hashes for plans and reports
```

The broker must not:

```text
invent new canonical relations during retrieval
widen selected axes silently
treat vector similarity as a typed relation
treat lexical hits as semantic support
make advisory text authoritative
mutate the canonical DB directly
hide skipped, clipped, or failed branches
```

### 4.5 Auditor responsibilities

The auditor checks whether downstream claims are supported by served evidence.

The auditor asks:

```text
Did the worker cite evidence returned by the broker?
Does candidate kind support the claim type?
Are D-lane claims backed by authority-admissible sources?
Did lexical matches get overstated as witnesses?
Are unresolved slots material?
Did drift warnings invalidate the answer?
Is a concept DB patch proposal evidence-backed?
```

The auditor may be deterministic policy, human, model-assisted, or mixed. The audit record must be explicit either way.

### 4.6 Shallow store adapter responsibilities

Adapters retrieve and annotate. They do not become semantic authorities.

Initial adapter classes:

| Adapter          | Role                                                            |
| ---------------- | --------------------------------------------------------------- |
| `repo_grep`      | Exact / alias / canonical term search over repo files.          |
| `docs_anm`       | ANM/D@1 block extraction and authority-layer-aware docs search. |
| `schema_json`    | JSON schema and model-field search.                             |
| `ast_symbol`     | Language-aware symbol/class/function lookup.                    |
| `tests_fixtures` | Tests, fixtures, golden files, probe fixtures.                  |
| `git_history`    | Commit/diff/log search, when allowed.                           |
| `vector_index`   | Optional recall aid, always attached to a typed branch.         |
| `external_tool`  | Allowed only under explicit task/tool authority.                |

Every adapter returns:

```text
source refs
spans where available
source hashes
store coverage
query provenance
adapter limitations
```

---

## 5. Component architecture

### 5.1 `CanonicalODEUConceptDB`

A versioned typed concept graph.

It stores canonical concepts, relation edges, aliases, evidence surfaces, witness templates, failure modes, domain packs, confidence tiers, provenance, deprecation records, and conflict records.

It is an O-lane substrate with E-lane provenance and D-lane admissibility metadata. It is not a vector DB and not a normative authority source by itself.

### 5.2 `SemanticBroker`

The deterministic retrieval coordinator.

Consumes:

```text
RetrievalIntent@1
CanonicalODEUConceptDB version/hash
active task frame
domain profile
authority/admissibility policy
adapter registry
optional prior coverage report
```

Emits:

```text
concept resolution result
expansion options
ConceptualSearchPlan@1
QueryBranch@1 records
EvidenceCandidate@1 records
EvidenceCoverageReport@1
DriftWarning@1 records
optional ConceptDBPatchProposal@1
```

### 5.3 Concept resolver

Maps worker language to canonical concepts.

Resolution modes:

```text
exact_concept_id
exact_alias
normalized_alias
domain_scoped_alias
phrase_match
ambiguous_match
unresolved
```

Ambiguity is not an error by itself. Silent disambiguation is the error.

### 5.4 Expansion engine

Walks the typed concept graph under selected controls:

```text
root concepts
allowed relation types
denied relation types
max depth
confidence threshold
domain pack
drift budget
store allowlist
authority boundary
```

Output:

```text
expanded concept closure
preserved relation paths
skipped edges with reasons
drift warnings
deterministic ordering trace
```

Stable ordering should be:

```text
root concept ID
  -> relation type canonical order
  -> relation ID
  -> target concept ID
  -> store adapter order
```

### 5.5 Query planner

Turns expansion closure into `QueryBranch@1` records.

A query branch is not just a string. It records why the query exists:

```text
root concept
expanded concept
relation path
relation types
store adapter
query terms
expected evidence surface
admissibility filter
budget
drift risk
branch hash
```

### 5.6 Evidence candidate classifier

Classifies returned chunks as candidates, not conclusions.

Candidate kinds:

```text
lexical_match
alias_match
structural_match
implementation_surface_candidate
evidence_surface_candidate
witness_candidate
negative_witness_candidate
checked_no_witness
inadmissible
stale_hint
ambiguous
```

Classification can use deterministic rules first and optional model review second. The record must say how the classification was made.

### 5.7 Coverage reporter

The coverage reporter is the broker’s audit spine.

It records:

```text
roots selected
axes selected
axes excluded
depth
confidence tier
stores selected
stores excluded
branches generated
branches searched
branches skipped
branches clipped
candidates found
lexical-only branches
witness slots filled
empty witness slots
unresolved terms
ambiguous concepts
drift warnings
adapter failures
bounded exhaustiveness statement
```

### 5.8 Operator / projection surface

A future UI may project:

```text
concept resolution
expansion options
plan branches
candidate evidence
coverage gaps
drift warnings
patch proposals
```

But projection does not ratify concepts, relations, claims, or authority. This follows the operator projection doctrine that visual prominence, operator clicks, case views, and recommendations do not mint authority.

---

## 6. Canonical ODEU Concept DB

### 6.1 What is stored

`CanonicalODEUConceptDB` stores a curated typed graph.

Each concept record should include:

```text
concept_id
canonical_label
short_definition
odeu_lanes
domain_pack_refs
authority_posture
lifecycle_status
aliases
search_terms
relation_refs
evidence_surface_hints
witness_template_refs
failure_mode_refs
provenance_refs
confidence_tier
semantic_hash
deprecation / replacement metadata
```

The DB should not store only synonyms. It should store typed semantic affordances for retrieval.

### 6.2 Required relation types

| Relation type                | Meaning                                                     | Example                                     |
| ---------------------------- | ----------------------------------------------------------- | ------------------------------------------- |
| `alias`                      | Alternate term for same concept, scoped where needed.       | `provider_choice` ↔ `model_selection`       |
| `genus`                      | Broader class.                                              | `CLI_flag` → `command_interface_element`    |
| `species`                    | Narrower class.                                             | `config_file` → `toml_config_file`          |
| `sibling`                    | Adjacent concept under shared parent.                       | `stdout` ↔ `stderr`                         |
| `part_whole`                 | Component or aggregate relation.                            | `subcommand` → `command_ontology`           |
| `implementation_surface`     | Code/symbol/API surface likely to implement concept.        | `provider_choice` → `ProviderKind`          |
| `evidence_surface`           | Source class likely to evidence concept.                    | `config_precedence` → docs/tests/probe logs |
| `deontic_law`                | Relevant rule, prohibition, obligation, authority boundary. | `D@1_block` → `authority_zone`              |
| `utility_axis`               | Objective/tradeoff axis.                                    | `recall` → `broad_expansion`                |
| `test_witness_template`      | Expected test/probe witness shape.                          | `error_behavior` → invalid-input probe      |
| `failure_mode`               | Known failure pattern.                                      | `lexical_hit_as_witness`                    |
| `lifecycle_phase`            | Concept status or phase.                                    | `candidate_relation` → `promotion_review`   |
| `storage_substrate`          | Persistence layer.                                          | `runtime_selection` → SQLite/env/config     |
| `protocol_action_surface`    | Action/API/IPC/CLI surface.                                 | `provider_update` → request endpoint        |
| `domain_specific_edge_class` | Domain-local edge taxonomy.                                 | ADEU witness / edge / obligation class ref  |

### 6.3 Relation record requirements

Each relation must carry:

```text
relation_id
source_concept_id
target_concept_id
relation_type
directionality
domain_scope_refs
allowed_store_refs
confidence_tier
lifecycle_status
drift_risk_tier
supporting_evidence_refs
provenance_refs
conflict_refs
deprecated_by_relation_id?
relation_hash
```

Rules:

```text
relation type is a closed enum
unknown relation types fail closed
aliases are not global equivalence unless explicitly scoped
relation paths must be preserved in query branches
candidate relations are excluded by default unless the plan admits them
```

### 6.4 Confidence tiers

Minimal v0 tiers:

| Tier              | Meaning                                  |
| ----------------- | ---------------------------------------- |
| `seeded`          | Hand-authored initial DB seed.           |
| `candidate`       | Proposed by worker/broker, not promoted. |
| `evidence_backed` | Supported by admissible evidence.        |
| `stabilized`      | Repeatedly useful and regression-tested. |
| `deprecated`      | Retained for audit, excluded by default. |
| `rejected`        | Retained as known-bad relation.          |

Deprecated and rejected relations should remain inspectable. Erasure hides why an expansion was forbidden.

### 6.5 Domain packs

Domain packs prevent global semantic sprawl.

Recommended starter packs:

```text
adeu_repo
adeu_anm_normative
adeu_agent_harness
adeu_operator_projection
adeu_schema_family
adeu_witness_discipline
programbench_cli
typescript_repo
python_repo
```

A concept may appear in multiple packs, but relation semantics should be scoped when meaning differs.

Example:

```text
model_selection
  in adeu_repo: LLM provider / proposer backend / Codex runtime ambiguity
  in programbench_cli: CLI model/config choice, if applicable
```

### 6.6 O/E/D/U posture of the DB

| Lane  | DB role                                                                           |
| ----- | --------------------------------------------------------------------------------- |
| **O** | Canonical concepts, relation graph, domain packs, concept slots.                  |
| **E** | Provenance refs, supporting evidence refs, witness templates.                     |
| **D** | Relation admissibility, authority posture, forbidden expansions, promotion rules. |
| **U** | Retrieval utility hints, drift risk, recall/precision affordances.                |

The DB itself is primarily O-lane. It can carry E/D/U metadata, but it should not become D-lane authority by existence.

---

## 7. Runtime protocol

### 7.1 Step 0 — Establish active task frame

The harness creates an active task frame:

```text
task_id
source_set_ref
source_set_hash
repo commit or artifact snapshot
worker role
domain profile
authority boundary
allowed stores
allowed tools
budget
prior coverage reports
claim types expected
```

This prevents retrieval from escaping the task.

### 7.2 Step 1 — Worker declares `RetrievalIntent@1`

Example:

```json
{
  "schema": "RetrievalIntent@1",
  "intent_id": "intent.adeu.runtime_provider_persistence",
  "active_task_frame_ref": "task.repo_search.provider_selection",
  "worker_role": "architecture_worker",
  "objective": "Find where runtime model/provider selection is persisted.",
  "why": "A change to runtime provider selection must update the correct persistence and runtime surfaces.",
  "seed_terms": [
    "runtime model selection",
    "provider selection",
    "provider choice",
    "persisted provider"
  ],
  "desired_odeu_lanes": ["O", "E"],
  "required_evidence": [
    "implementation_surface",
    "storage_substrate",
    "protocol_action_surface",
    "checked_no_witness"
  ],
  "preferred_axes": [
    "alias",
    "implementation_surface",
    "storage_substrate",
    "protocol_action_surface",
    "failure_mode"
  ],
  "forbidden_axes": ["deontic_law"],
  "allowed_stores": ["repo_grep", "schema_json", "docs", "tests"],
  "recall_precision_posture": "recall_biased",
  "noise_budget": "medium"
}
```

### 7.3 Step 2 — Broker resolves concepts

Example result:

```text
Resolved:
- runtime_selection
- provider_choice
- persistence_substrate

Ambiguous:
- model_selection:
    may mean API proposer provider, Codex worker runtime, UI provider button,
    policy profile, or capability model

Unresolved:
- shell preference:
    not in active domain pack unless developer_environment is enabled
```

The broker does not hide unresolved or ambiguous terms.

### 7.4 Step 3 — Broker proposes expansion options

| Axis                      | Default depth | Estimated concepts | Drift risk | Notes                                        |
| ------------------------- | ------------: | -----------------: | ---------- | -------------------------------------------- |
| `alias`                   |             1 |                  6 | low        | Provider/model/profile vocabulary.           |
| `implementation_surface`  |             1 |                  8 | low        | Source symbols and request models.           |
| `storage_substrate`       |             1 |                  5 | low        | SQLite/env/config/profile.                   |
| `protocol_action_surface` |             1 |                  4 | medium     | API/IPC/update path.                         |
| `failure_mode`            |             1 |                  3 | medium     | Unsupported provider, fallback/default.      |
| `deontic_law`             |             1 |                  7 | high       | Probably unnecessary for persistence search. |

### 7.5 Step 4 — Worker selects expansion envelope

Example:

```json
{
  "selected_axes": [
    "alias",
    "implementation_surface",
    "storage_substrate",
    "protocol_action_surface",
    "failure_mode"
  ],
  "excluded_axes": ["deontic_law"],
  "max_depth": 1,
  "min_confidence_tier": "seeded",
  "max_concepts": 40,
  "max_branches": 80,
  "max_hits_per_branch": 20,
  "admissibility": {
    "implementation_claim_requires": ["source_span"],
    "persistence_claim_requires": ["storage_schema_or_write_path"],
    "absence_claim_requires": ["checked_no_witness"]
  }
}
```

### 7.6 Step 5 — Broker emits `ConceptualSearchPlan@1`

The plan records:

```text
concept DB version/hash
resolved roots
selected axes
excluded axes
relation paths
query branches
stores
budget
drift policy
deterministic ordering profile
plan hash
```

Same inputs must yield the same plan.

### 7.7 Step 6 — Broker queries shallow stores

The broker dispatches branches to adapters:

```text
repo_grep
schema_json
docs_anm
tests_fixtures
ast_symbol
git_history, if allowed
vector_index, if allowed
```

Each query is tied to a branch and relation path.

### 7.8 Step 7 — Broker classifies evidence candidates

Example distinction:

```text
"provider" appears in a path
  -> lexical_match

ProviderKind = Literal["mock", "openai", "codex"]
  -> implementation_surface_candidate

SQLite table `urm_worker_run` contains provider TEXT NOT NULL
  -> storage_substrate_witness_candidate

API rejects unsupported provider
  -> failure_mode_witness_candidate

Frontend button calls setProvider("codex")
  -> protocol/UI selection candidate, not persistence witness

No localStorage/sessionStorage hit in targeted frontend pass
  -> checked_no_witness only for declared source set, if adapter performed that check
```

### 7.9 Step 8 — Broker emits `EvidenceCoverageReport@1`

The report says:

```text
what was searched
what was not searched
what was found
what was lexical only
what was witness-like
what was checked and empty
what was ambiguous
what was clipped
what stores failed or were excluded
```

### 7.10 Step 9 — Worker reasons or expands again

The worker may:

```text
answer using served evidence
request another axis
deepen selected axes
add a store
ask for ambiguity resolution
submit a patch proposal
stop because evidence is insufficient
```

The worker may not silently fill gaps with vibes.

---

## 8. Schema sketches

These are minimal v0 schemas, not a giant schema universe.

They should follow the repo’s observed schema meta-grammar posture:

```text
required schema field
closed root
explicit anchors
governance posture
evidence / lineage refs
O/E/D/U realization
named residuals only
```

### 8.1 `CanonicalConceptRecord@1`

Purpose: canonical O-lane concept node.

```text
schema
concept_id
canonical_label
short_definition
odeu_lanes[]
domain_pack_refs[]
authority_posture
lifecycle_status
aliases[]
search_terms[]
relation_refs[]
evidence_surface_hints[]
witness_template_refs[]
failure_mode_refs[]
provenance_refs[]
confidence_tier
semantic_hash
deprecated_by_concept_id?
replacement_concept_ids[]
notes_advisory?
```

Rules:

```text
concept_id is identity; label is not identity
aliases do not imply global equivalence
advisory notes cannot create relations
```

### 8.2 `ConceptRelation@1`

Purpose: typed edge between canonical concepts.

```text
schema
relation_id
source_concept_id
target_concept_id
relation_type
directionality
domain_scope_refs[]
allowed_store_refs[]
confidence_tier
lifecycle_status
drift_risk_tier
supporting_evidence_refs[]
provenance_refs[]
created_by
created_at_source_ref
deprecated_by_relation_id?
conflict_relation_refs[]
relation_hash
```

Rules:

```text
relation_type is from a closed enum
relation paths must be preserved
candidate relations are not default expansion material
```

### 8.3 `RetrievalIntent@1`

Purpose: worker declaration of retrieval need.

```text
schema
intent_id
active_task_frame_ref
worker_role
objective
why
seed_terms[]
seed_concept_ids[]
desired_odeu_lanes[]
required_evidence[]
allowed_stores[]
forbidden_stores[]
preferred_axes[]
forbidden_axes[]
recall_precision_posture
noise_budget
max_cost?
authority_boundary_ref?
prior_coverage_report_refs[]
freeform_context_advisory?
```

Rules:

```text
freeform context is advisory
D-lane retrieval requires authority boundary
unresolved terms must be reported
```

### 8.4 `ConceptualSearchPlan@1`

Purpose: deterministic retrieval plan.

```text
schema
plan_id
intent_ref
concept_db_ref
concept_db_hash
active_task_frame_ref
resolved_root_concept_ids[]
ambiguous_terms[]
unresolved_terms[]
selected_axes[]
excluded_axes[]
max_depth
min_confidence_tier
domain_profile_ref
store_adapter_refs[]
query_branch_refs[]
budget
drift_policy_ref
deterministic_ordering_profile
plan_hash
```

Rules:

```text
same inputs produce same plan_hash
selected axes are explicit
skipped expansions are reportable
```

### 8.5 `QueryBranch@1`

Purpose: one planned search branch.

```text
schema
branch_id
plan_ref
root_concept_id
expanded_concept_id
relation_path[]
relation_types[]
store_adapter_ref
query_terms[]
query_filters
expected_evidence_surface
required_witness_kind?
admissibility_filter_ref?
max_hits
branch_drift_risk
branch_hash
```

Rules:

```text
no unexplained query strings
relation path must preserve relation types
worker-supplied manual terms are marked noncanonical
```

### 8.6 `EvidenceCandidate@1`

Purpose: retrieved chunk, candidate witness, or negative check.

```text
schema
candidate_id
plan_ref
branch_ref
concept_ids[]
source_ref
source_path?
source_span?
source_hash?
store_adapter_ref
matched_terms[]
candidate_kind
witness_kind?
admissibility_status
authority_layer?
excerpt_hash
summary_advisory?
limitations[]
model_review_status?
auditor_review_status?
```

Candidate kinds:

```text
lexical_match
alias_match
structural_match
implementation_surface_candidate
evidence_surface_candidate
witness_candidate
negative_witness_candidate
checked_no_witness
inadmissible
stale_hint
ambiguous
```

Rules:

```text
excerpt text is bounded
summaries are advisory
lexical matches are not witnesses
```

### 8.7 `EvidenceCoverageReport@1`

Purpose: retrieval accounting and bounded exhaustiveness statement.

```text
schema
report_id
plan_ref
concept_db_ref
source_set_ref
searched_concept_slots[]
unsearched_concept_slots[]
searched_relation_axes[]
excluded_relation_axes[]
searched_store_refs[]
unsearched_store_refs[]
branch_results[]
evidence_candidate_refs[]
resolved_concepts[]
ambiguous_concepts[]
unresolved_concepts[]
empty_witness_slots[]
checked_no_witness_slots[]
drift_warning_refs[]
budget_clipping_events[]
adapter_failures[]
coverage_status
coverage_statement
report_hash
```

Coverage statuses:

```text
closed_relative_to_plan
open_with_gaps
blocked_by_ambiguity
blocked_by_authority
blocked_by_adapter_failure
clipped_by_budget
drift_limit_exceeded
```

### 8.8 `ConceptDBPatchProposal@1`

Purpose: additive improvement proposal.

```text
schema
proposal_id
proposal_kind
target_concept_id?
target_relation_id?
proposed_concept_record?
proposed_relation_record?
reason
supporting_evidence_candidate_refs[]
coverage_report_refs[]
proposed_confidence_tier
risk_assessment
conflict_refs[]
submitted_by
review_status
reviewer_refs[]
decision_record_ref?
```

Proposal kinds:

```text
add_concept
add_relation
add_alias
add_witness_template
deprecate_relation
deprecate_alias
split_concept
merge_concept
raise_confidence
lower_confidence
```

### 8.9 `DriftWarning@1`

Purpose: explicit drift/noise warning.

```text
schema
warning_id
plan_ref
branch_ref?
concept_id?
relation_id?
warning_kind
drift_score
threshold
reason
recommended_action
was_branch_clipped
```

Warning kinds:

```text
domain_crossing
low_confidence_relation
depth_limit_pressure
budget_clipping
lexical_noise
authority_boundary_risk
ambiguous_alias
stale_path_hint
adapter_undercoverage
model_supplied_uncanonical_term
vector_untyped_similarity
```

---

## 9. Deterministic/model/auditor split

### 9.1 Deterministic broker-owned operations

These must be deterministic:

```text
schema validation
canonical ID lookup
exact alias lookup
domain-scoped alias lookup
relation filtering
depth-limited graph expansion
confidence-tier filtering
domain-pack filtering
query branch generation from canonical terms
query ordering
store adapter dispatch order
source span hashing
de-duplication
budget clipping
drift scoring from declared formula
coverage accounting
plan/report hashing
```

Given the same concept DB hash, source set, broker version, intent, and selected options, the plan and coverage accounting should be reproducible.

### 9.2 Model-mediated operations

The model may perform:

```text
intent formulation
explanation of why retrieval is needed
initial seed term generation
selection among broker-proposed axes
ambiguity adjudication when broker offers choices
semantic relevance review of evidence candidates
decision to request another expansion
proposal of new candidate relations or concepts
```

Model outputs remain advisory unless admitted through deterministic or auditor-mediated workflow.

### 9.3 Auditor-mediated operations

The auditor decides:

```text
whether evidence candidates support downstream claims
whether claim type matches candidate kind
whether D-lane claims used authority-admissible sources
whether lexical hits were overstated
whether unresolved slots matter
whether drift warnings invalidate the answer
whether DB patch proposals are promotable
```

### 9.4 Human/operator responsibilities

Human or operator review is required for:

```text
canonical DB promotion
high-impact concept splits/merges
deontic-law relation changes
authority grants
domain pack publication
promotion to stabilized
relation conflict settlement
deprecation of widely used relations
```

Operator projection may make cases visible. It must not ratify them by display.

---

## 10. Evidence and coverage semantics

### 10.1 Evidence classes

| Class                              | Meaning                                      | Claim support posture                     |
| ---------------------------------- | -------------------------------------------- | ----------------------------------------- |
| `lexical_match`                    | Term appears.                                | Never sufficient alone.                   |
| `alias_match`                      | Alias appears.                               | Weak candidate.                           |
| `structural_match`                 | Code/schema shape aligns.                    | Sometimes, with review.                   |
| `implementation_surface_candidate` | Likely implementation location.              | Supports “where to inspect.”              |
| `evidence_surface_candidate`       | Likely source of evidence.                   | Supports further retrieval.               |
| `witness_candidate`                | Likely direct support.                       | Supports claim after admissibility check. |
| `negative_witness_candidate`       | Evidence of failure/absence behavior.        | Supports negative behavior after check.   |
| `checked_no_witness`               | Declared slot searched and no witness found. | Supports bounded gap / absence claim.     |
| `inadmissible`                     | Found but not allowed for claim.             | Cannot support claim.                     |
| `stale_hint`                       | Old path/name likely stale.                  | Warning only.                             |
| `ambiguous`                        | Context insufficient.                        | Requires review.                          |

### 10.2 Claim-dependent admissibility

| Claim type              | Required evidence                                                     |
| ----------------------- | --------------------------------------------------------------------- |
| Implementation location | Source span, symbol span, schema span.                                |
| Persistence substrate   | Storage schema, write path, config binding, environment binding.      |
| Runtime behavior        | Test, probe log, fixture, executable witness, negative witness.       |
| Normative rule          | Recognized authority block or compiled authority artifact.            |
| Authority boundary      | ANM authority profile, policy artifact, lock, or compiled D artifact. |
| Absence claim           | Checked-no-witness over declared source set and stores.               |
| Concept DB promotion    | Evidence refs, coverage report, review decision.                      |
| Deprecation             | Failed retrieval examples or contrary evidence plus review.           |

### 10.3 Coverage statement form

Every coverage report must include a bounded statement like:

```text
Coverage is closed relative to:
- concept DB hash: X
- roots: runtime_selection, provider_choice
- axes: alias, implementation_surface, storage_substrate
- depth: 1
- confidence tier: >= seeded
- stores: repo_grep, schema_json, docs
- source set hash: Y

Coverage is not closed over:
- vector search
- git history
- external docs
- deontic-law relations
- depth > 1
- unresolved term: shell preference
- excluded store: frontend runtime browser storage beyond static source grep
```

### 10.4 Bounded exhaustiveness

Allowed statement:

```text
All selected relation paths matching the plan envelope were expanded,
and all generated query branches were run against selected stores,
except the listed skipped/clipped/failed branches.
```

Forbidden statement:

```text
All relevant evidence has been found.
```

### 10.5 O/E/D/U mapping

| Lane  | Retrieval role                                                                                                 |
| ----- | -------------------------------------------------------------------------------------------------------------- |
| **O** | Concept inventory, relation graph, active task frame, source/store identities, conceptual slots.               |
| **E** | Retrieved chunks, source spans, witnesses, no-witness checks, provenance, coverage report.                     |
| **D** | Allowed axes, forbidden axes, authority boundaries, admissibility filters, store permissions, promotion rules. |
| **U** | Retrieval objective, noise budget, recall/precision posture, budget allocation, stop criteria.                 |

This lane separation is the central reason the broker should exist.

---

## 11. Drift control

### 11.1 Drift sources

Retrieval drift occurs when:

```text
aliases are over-broad
sibling relations are treated as equivalence
genus expansion becomes too abstract
species expansion becomes too large
domain packs cross silently
low-confidence relations enter unnoticed
vector results bypass typed relations
lexical hits overwhelm witnesses
model-supplied terms become untracked search terms
stores outside the task frame are queried
advisory sources are used for authority claims
```

### 11.2 Required controls

The broker enforces:

```text
max_depth
max_concepts
max_branches
max_hits_per_branch
relation allowlist
relation denylist
confidence threshold
domain profile
store allowlist
authority boundary
evidence admissibility filter
active task frame binding
drift score threshold
budget clipping record
adapter failure record
```

### 11.3 Drift scoring

A simple deterministic v0 formula is enough:

```text
drift_score =
  relation_type_base_risk
  + confidence_penalty
  + depth_penalty
  + domain_crossing_penalty
  + store_weakness_penalty
  + lexical_noise_penalty
  + task_frame_mismatch_penalty
  + hit_explosion_penalty
```

The exact weights are less important than determinism, recording, and regression tests.

### 11.4 High-risk relation types

Default v0 risk posture:

| Relation type                | Default risk                  |
| ---------------------------- | ----------------------------- |
| `alias`                      | Low, if scoped.               |
| `implementation_surface`     | Low/medium.                   |
| `storage_substrate`          | Low/medium.                   |
| `evidence_surface`           | Medium.                       |
| `protocol_action_surface`    | Medium.                       |
| `test_witness_template`      | Medium.                       |
| `failure_mode`               | Medium.                       |
| `species`                    | Medium.                       |
| `part_whole`                 | Medium.                       |
| `sibling`                    | Medium/high.                  |
| `genus`                      | High beyond depth 1.          |
| `utility_axis`               | High unless task requires it. |
| `deontic_law`                | High, authority-bound.        |
| `domain_specific_edge_class` | Domain-dependent.             |

### 11.5 Forbidden silent widening

The broker must warn or fail closed when:

```text
an unknown relation type appears
an alias resolves to multiple concepts
model adds an uncanonical term
a store adapter searches outside source set
D-lane retrieval lacks authority boundary
a branch crosses a domain pack
vector search returns untyped similarity
branch count or hit volume exceeds budget
budget clipping affects absence claims
```

---

## 12. Canonical DB evolution workflow

### 12.1 Additive improvement

The DB improves through proposals, not silent mutation.

Workers may propose:

```text
new concept
new alias
new relation
new witness template
confidence upgrade
confidence downgrade
deprecation
split
merge
conflict record
domain-pack addition
```

Every proposal must include evidence candidates and coverage report refs.

### 12.2 Promotion path

```text
candidate observation
  -> ConceptDBPatchProposal@1
  -> evidence/admissibility review
  -> conflict check
  -> retrieval regression check
  -> operator/human approval if high-impact
  -> promoted DB version
  -> changelog + semantic hash
```

### 12.3 Bad relation deprecation

Bad relations are deprecated, not erased.

Deprecation record includes:

```text
relation_id
reason
failed retrieval examples
contrary evidence refs
replacement relation?
affected domain packs
regression fixture added?
review decision
```

### 12.4 Confidence lifecycle

Recommended lifecycle:

```text
seeded
  -> candidate
  -> evidence_backed
  -> stabilized

candidate -> rejected
evidence_backed/stabilized -> deprecated
```

A relation can be useful but still low-confidence. Plans must explicitly admit the confidence tier they use.

### 12.5 Domain pack governance

Domain packs should be separately reviewable.

Example packs:

```text
programbench_cli:
  command, subcommand, CLI flag, config file, env var,
  default value, precedence, exit code, stdout, stderr,
  output artifact, file side effect, error class

adeu_anm_normative:
  ANM document, authority profile, D@1 block, selector,
  D-IR, predicate contract, result set, obligation ledger,
  authority laundering failure mode

adeu_agent_harness:
  worker run, capability probe, taskpack, dispatch token,
  evidence root, policy profile, approval gate
```

### 12.6 Retrieval regression tests

Every promoted relation should support at least one retrieval regression fixture.

Examples:

```text
root provider_choice + axis storage_substrate
  emits query branches for urm_worker_run.provider

root authority_zone + axis evidence_surface
  does not treat ordinary prose as normative

root error_behavior + axis test_witness_template
  includes negative probes

deprecated alias
  is excluded from default expansion

vector adapter
  cannot introduce an untyped concept branch
```

### 12.7 Conflict handling

Example conflict:

```text
model_selection alias-of provider_choice
vs
model_selection alias-of capability_model_selection
```

Resolution options:

```text
split concept
domain-scope alias
lower confidence
mark ambiguous
require worker disambiguation
deprecate one relation
```

The broker should prefer explicit ambiguity to false unification.

---

## 13. ProgramBench example

**Grounding status:** ProgramBench was not observed as an existing ADEU repo artifact in the targeted pass. This section is a recommended adapter pattern for ProgramBench-style black-box specification recovery.

### 13.1 Task

A worker must reconstruct program behavior before implementation.

The task is not just “search docs.” It must recover a program ontology:

```text
commands
subcommands
flags
positional arguments
config files
environment variables
defaults
precedence
output artifacts
file side effects
error behavior
exit codes
stdout/stderr conventions
invalid input behavior
```

### 13.2 Worker intent

```json
{
  "schema": "RetrievalIntent@1",
  "intent_id": "intent.programbench.behavior_recovery",
  "objective": "Recover the program behavior ontology before implementation.",
  "why": "Build a ProgramODEUProfile from evidence rather than guessing behavior.",
  "seed_terms": [
    "CLI behavior",
    "config precedence",
    "default values",
    "error behavior",
    "output artifact",
    "file side effect"
  ],
  "desired_odeu_lanes": ["O", "E", "D", "U"],
  "required_evidence": [
    "help_text",
    "docs",
    "tests",
    "fixtures",
    "probe_logs",
    "negative_witness"
  ],
  "preferred_axes": [
    "genus",
    "species",
    "part_whole",
    "implementation_surface",
    "evidence_surface",
    "test_witness_template",
    "failure_mode",
    "storage_substrate",
    "protocol_action_surface"
  ],
  "noise_budget": "medium",
  "recall_precision_posture": "recall_biased"
}
```

### 13.3 Broker expansion

Canonical roots:

```text
program_behavior
command_ontology
CLI_flag
subcommand
positional_argument
config_file
environment_variable
default_value
config_precedence
parser_precedence
error_class
exit_code
stdout_output
stderr_output
output_artifact
file_side_effect
probe_log
test_witness_template
```

Example relations:

```text
CLI_flag
  species -> boolean_flag
  species -> value_flag
  species -> repeatable_flag

config_file
  storage_substrate -> JSON
  storage_substrate -> TOML
  storage_substrate -> YAML
  storage_substrate -> env

config_precedence
  evidence_surface -> docs
  evidence_surface -> tests
  evidence_surface -> probe_logs

error_class
  test_witness_template -> invalid_flag_probe
  test_witness_template -> missing_file_probe
  test_witness_template -> malformed_config_probe

output_artifact
  evidence_surface -> golden_files
  evidence_surface -> file_tree_diff
```

### 13.4 Store queries

The broker queries:

```text
README/docs
--help output, if allowed
tests
fixtures
source grep / AST
probe logs
generated outputs
git history, if allowed
```

### 13.5 Coverage report

Example report excerpt:

```text
O coverage:
- commands: found
- subcommands: partial
- flags: found
- config file: found
- environment variables: checked_no_witness
- defaults: partial
- precedence: unresolved
- errors: partial
- output artifacts: found
- side effects: unresolved

E coverage:
- help text witness found
- tests found for valid invocation
- no negative probe for malformed config
- no witness for env override precedence

D constraints:
- no precedence claim allowed without docs/test/probe witness
- no absence claim allowed unless checked_no_witness slot exists

U outcome:
- enough evidence for first ProgramODEUProfile draft
- not enough evidence for implementation parity claim
```

### 13.6 Worker result

The worker builds `ProgramODEUProfile` only from covered slots.

It marks unresolved slots explicitly:

```text
config precedence
malformed config error class
environment variable override
file side effects under failure
```

Then it requests targeted probes or deeper expansion rather than inventing behavior.

---

## 14. ADEU repo-search example

### 14.1 Intent

Task: find where runtime model/provider selection is persisted.

The worker should not merely search `provider`. It should request conceptual expansion.

```json
{
  "schema": "RetrievalIntent@1",
  "intent_id": "intent.adeu.runtime_provider_persistence",
  "objective": "Find where runtime model/provider selection is persisted.",
  "why": "A provider-selection change must update correct runtime, config, persistence, and UI surfaces.",
  "seed_terms": [
    "runtime provider selection",
    "model selection",
    "provider choice",
    "persist provider"
  ],
  "desired_odeu_lanes": ["O", "E"],
  "required_evidence": [
    "implementation_surface",
    "storage_substrate",
    "protocol_action_surface",
    "checked_no_witness"
  ],
  "preferred_axes": [
    "alias",
    "implementation_surface",
    "storage_substrate",
    "protocol_action_surface",
    "failure_mode"
  ],
  "forbidden_axes": ["deontic_law"],
  "allowed_stores": ["repo_grep", "schema_json", "docs", "tests"],
  "noise_budget": "medium"
}
```

### 14.2 Canonical expansion

Root:

```text
runtime_selection
```

Selected expansion:

```text
runtime_selection
  alias -> provider_choice
  alias -> model_selection
  alias -> profile_selection
  implementation_surface -> ProviderKind
  implementation_surface -> proposer backend
  implementation_surface -> Codex worker runtime
  implementation_surface -> frontend provider state
  storage_substrate -> SQLite worker run
  storage_substrate -> SQLite copilot session
  storage_substrate -> environment config
  storage_substrate -> policy profile
  protocol_action_surface -> propose endpoint
  protocol_action_surface -> worker run request
  failure_mode -> unsupported provider
  failure_mode -> fallback/default provider
```

### 14.3 Evidence candidates from targeted repo pass

This is not a whole-repo proof. It is an example of what the broker should report from a bounded pass.

| Slot                          | Observed candidate                                                                                                                                                                                                                                                                               | Candidate kind                                  |
| ----------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ----------------------------------------------- |
| Provider enum                 | `ProviderKind = Literal["mock", "openai", "codex"]` in `apps/api/src/adeu_api/main.py:403-415`                                                                                                                                                                                                   | implementation surface                          |
| Provider parity               | API validates provider support per frozen surface matrix in `apps/api/src/adeu_api/main.py:417-424` and `:766-805`                                                                                                                                                                               | implementation / failure-mode candidate         |
| API request defaults          | proposal request models default provider to `"mock"` in `apps/api/src/adeu_api/main.py:1045-1062`                                                                                                                                                                                                | fallback/default candidate                      |
| External proposer selection   | `_select_external_proposer` dispatches `openai` and `codex`, otherwise errors for unsupported external proposer in `apps/api/src/adeu_api/main.py:5890-5898`; `/propose` then uses selected external proposer in `:5901-5938`                                                                    | implementation surface                          |
| Worker runtime provider       | URM worker execution only admits `request.provider == "codex"` and rejects others in `packages/urm_runtime/src/urm_runtime/worker.py:301-307`                                                                                                                                                    | implementation / failure-mode witness           |
| Worker run persistence        | worker start persists `request.provider` through `persist_worker_run_start` in `packages/urm_runtime/src/urm_runtime/worker.py:381-392`                                                                                                                                                          | storage write path                              |
| SQLite worker provider column | `urm_worker_run` includes `provider TEXT NOT NULL` in `packages/urm_runtime/src/urm_runtime/storage.py:282-301`                                                                                                                                                                                  | storage substrate witness                       |
| SQLite worker provider insert | `persist_worker_run_start` inserts `provider` into `urm_worker_run` in `packages/urm_runtime/src/urm_runtime/storage.py:595-642`                                                                                                                                                                 | storage write witness                           |
| Copilot session persistence   | `urm_copilot_session` stores `codex_version`, `capability_probe_id`, `profile_id`, `profile_version`, and `profile_policy_hash` in `packages/urm_runtime/src/urm_runtime/storage.py:241-263` and `:1059-1093`                                                                                    | storage substrate witness                       |
| Capability probe              | `urm_codex_capability_probe` stores Codex version/capability probe JSON in `packages/urm_runtime/src/urm_runtime/storage.py:230-238`                                                                                                                                                             | capability evidence surface                     |
| Runtime config                | DB/evidence/Codex binary locations come from environment-backed config in `packages/urm_runtime/src/urm_runtime/config.py:54-65` and `:93-139`                                                                                                                                                   | config substrate                                |
| Policy profile substrate      | policy profiles `default`, `experimental`, and `safe_mode` are declared in `policy/profiles.v1.json:1-31`                                                                                                                                                                                        | profile substrate                               |
| Frontend provider selection   | inspected app pages use React `useState<"mock" \| "openai" \| "codex">("mock")` and buttons calling `setProvider(...)`; examples in `apps/web/src/app/page.tsx:288` and `:505-515`, `apps/web/src/app/papers/page.tsx:101` and `:551-571`, `apps/web/src/app/puzzles/page.tsx:85` and `:181-192` | UI selection candidate, not persistence witness |

### 14.4 Example coverage report

```text
coverage_status: open_with_gaps

closed relative to:
- roots: runtime_selection, provider_choice, persistence_substrate
- axes: alias, implementation_surface, storage_substrate, protocol_action_surface, failure_mode
- depth: 1
- stores: targeted repo_grep, schema_json, selected docs/source files
- source set: attached ADEU repo zip, targeted pass

found:
- API provider enum
- provider parity validation
- request-level default provider = mock
- external proposer dispatch for openai/codex
- worker runtime provider constraint: codex only
- SQLite persistence of worker_run.provider
- SQLite persistence of Codex session/profile/capability data
- environment config for DB/evidence/Codex binary paths
- frontend provider buttons using local React state

unresolved / not yet witnessed:
- user-facing persistent provider preference
- browser storage persistence for provider preference beyond targeted static grep
- IPC/update path for changing provider selection after runtime start
- shell-level provider preference
- whether provider parity matrix is treated only as repo fixture/package resource or as mutable config
- tests proving fallback/default behavior
- git history evidence for prior provider persistence changes

bounded worker-safe conclusion:
- provider choice is observed as request-level API state and as worker-run persistence.
- URM worker runs persist provider in SQLite.
- Codex session/profile/capability state is persisted separately.
- targeted frontend evidence shows local UI provider selection state but not a witnessed persistent frontend preference.
```

Forbidden stronger conclusion:

```text
The repo has no persistent provider preference anywhere.
```

That would require checked-no-witness coverage over UI, API, runtime config, storage, tests, git history, and possibly environment/shell integration.

---

## 15. Failure modes and mitigations

### 15.1 Bad canonical relations

**Failure:** `model_selection` is globally aliased to `provider_choice`, but in some tasks it means capability model selection.

**Mitigation:** domain-scoped aliases, ambiguity records, conflict refs, regression tests, deprecation path.

### 15.2 Over-expansion / noise

**Failure:** genus and sibling expansion pull in broad irrelevant concepts.

**Mitigation:** relation allowlists, depth limits, drift-risk scoring, branch caps, lexical-noise warnings.

### 15.3 Under-expansion / missed concept

**Failure:** worker selects only `alias`, missing `storage_substrate`.

**Mitigation:** broker option proposal shows unselected high-value axes; coverage report lists excluded axes.

### 15.4 Stale repo path hints

**Failure:** canonical DB path hint points to old source file.

**Mitigation:** path hints are not truth; adapter marks `stale_hint`; patch proposal updates hint with evidence.

### 15.5 Model selects wrong axis

**Failure:** worker selects `deontic_law` when it needs implementation surfaces.

**Mitigation:** objective/axis mismatch warning; auditor checks claim support.

### 15.6 Model over-trusts returned evidence

**Failure:** worker treats candidate chunk as proof.

**Mitigation:** candidate kind and admissibility status are mandatory; auditor rejects unsupported claims.

### 15.7 Broker treats lexical hit as semantic witness

**Failure:** term match becomes evidence.

**Mitigation:** lexical match is separate candidate kind; witness classification requires stronger criteria.

### 15.8 Canonical DB ossifies wrong ontology

**Failure:** early concept splits become institutional.

**Mitigation:** candidate/stabilized distinction, conflict records, split/merge proposals, regression tests.

### 15.9 Evidence store misses relevant item

**Failure:** grep misses symbol semantics; vector misses exact fields; AST adapter disabled.

**Mitigation:** coverage report lists stores searched and unsearched; absence claims require checked-no-witness over selected stores.

### 15.10 Hidden dependency across concepts not represented

**Failure:** provider persistence depends on profile policy, but DB lacks relation.

**Mitigation:** unresolved slot visible; worker proposes relation with evidence-backed patch.

### 15.11 Authority laundering

**Failure:** advisory prose retrieved as normative law.

**Mitigation:** authority-layer filters; ANM/D@1 integration; advisory candidates cannot satisfy D-lane claims.

### 15.12 Vector drift

**Failure:** vector results bypass typed relation graph.

**Mitigation:** vector adapter must attach results to existing `QueryBranch@1`; vector results cannot create untyped expansion.

### 15.13 Budget clipping hides missing evidence

**Failure:** branch clipped after max hits; worker assumes coverage complete.

**Mitigation:** clipping changes coverage status; clipped branches cannot support absence claims.

### 15.14 Bad worker query after broker report

**Failure:** worker performs additional freeform search and blends it into broker-covered evidence.

**Mitigation:** worker may use extra search only as `outside_plan_advisory` or must request a new plan branch.

### 15.15 Adapter over-classification

**Failure:** adapter emits `witness_candidate` based on shallow heuristics.

**Mitigation:** admissibility status remains separate from candidate kind; auditor review is required for claim support.

### 15.16 Canonical DB becomes too conservative

**Failure:** relations are so hard to promote that workers revert to vibe-search.

**Mitigation:** allow low-authority `candidate` relation proposals in explicit experimental plans while excluding them from default stabilized retrieval.

### 15.17 Domain packs fragment too far

**Failure:** every domain pack creates slightly different concepts, preventing reuse.

**Mitigation:** shared concept IDs plus domain-scoped relation overlays; conflict review before split/merge promotion.

---

## 16. Minimal implementation slices

### Slice 0 — Static concept DB seed + CLI broker over repo grep

Smallest useful slice.

Add:

```text
hand-authored CanonicalConceptRecord@1
hand-authored ConceptRelation@1
one domain pack: adeu_repo
one adapter: repo_grep
deterministic expansion
stable query branch generation
plain coverage report
```

Acceptance target: same intent/options produce same branch list and grep queries.

### Slice 1 — First-class plan and coverage artifacts

Add:

```text
ConceptualSearchPlan@1
QueryBranch@1
EvidenceCandidate@1
EvidenceCoverageReport@1
plan/report hashes
relation path preservation
lexical vs witness distinction
```

Acceptance target: worker can cite only evidence candidates linked to branches.

### Slice 2 — Confidence, provenance, and drift controls

Add:

```text
confidence tiers
provenance refs
domain profiles
drift score
excluded axes
budget clipping records
stale hint warnings
```

Acceptance target: high-risk expansions warn or clip deterministically.

### Slice 3 — Additional adapters

Add shallow adapters:

```text
schema_json
docs_anm
tests_fixtures
ast_symbol
git_history
optional vector_index
```

Acceptance target: all adapter outputs normalize into `EvidenceCandidate@1` without changing plan semantics.

### Slice 4 — Worker / broker / auditor loop

Integrate with agent harness:

```text
worker emits RetrievalIntent@1
broker emits plan/report
worker answer binds claims to evidence candidates
auditor checks support
unresolved slots can trigger another expansion
```

Acceptance target: worker cannot silently cite unexpanded concepts.

### Slice 5 — ProgramBench adapter

Add behavior-recovery domain pack and adapters:

```text
CLI/help adapter
probe log adapter
test/fixture adapter
file-tree side-effect adapter
ProgramODEUProfile handoff
```

Acceptance target: profile distinguishes discovered, inferred, unresolved, and contradicted behavior.

### Slice 6 — Concept DB patch proposal workflow

Add:

```text
ConceptDBPatchProposal@1
reviewer decision records
confidence promotion
deprecation
conflict handling
retrieval regression fixtures
```

Acceptance target: concept relation changes require provenance and review.

---

## 17. Acceptance criteria

### 17.1 Deterministic expansion

Given the same:

```text
concept DB hash
intent
selected axes
depth
confidence threshold
domain profile
source set
broker version
```

the broker emits the same `ConceptualSearchPlan@1`.

### 17.2 Query plan preserves relation types

Every branch records:

```text
root concept
expanded concept
relation path
relation types
store adapter
expected evidence surface
branch hash
```

No branch is just an unexplained query string.

### 17.3 Coverage report lists searched and unsearched slots

The report lists:

```text
searched concept slots
unsearched concept slots
searched stores
unsearched stores
excluded axes
skipped branches
unresolved terms
ambiguous terms
empty witness slots
budget clipping
adapter failures
```

### 17.4 Worker cannot silently use unexpanded vibes

Any factual worker claim must bind to one of:

```text
evidence candidate ref
explicit inference/advisory status
outside-plan marker
```

Unexpanded concepts cannot be cited as covered.

### 17.5 Concept relation changes require provenance

Adding, removing, promoting, deprecating, merging, or splitting concept relations requires:

```text
patch proposal
evidence refs or rationale
review status
DB version change
regression impact note for stabilized relations
```

### 17.6 Retrieval distinguishes lexical match from witness

Results must distinguish:

```text
lexical_match
structural_match
implementation_surface_candidate
witness_candidate
checked_no_witness
inadmissible
```

A lexical hit alone cannot satisfy a witness requirement.

### 17.7 Drift warnings trigger

Warnings trigger when:

```text
expansion crosses domain packs
low-confidence relations are included
branch count exceeds budget
hit volume exceeds noise threshold
relation depth approaches limit
model supplies uncanonical terms
vector adapter returns untyped similarity
authority boundary risk appears
```

### 17.8 Bounded exhaustiveness statement exists

Every coverage report must say what it is closed over and what it is not closed over.

### 17.9 Authority boundaries are respected

D-lane retrieval distinguishes:

```text
recognized authority blocks
architecture/decomposition docs
support docs
advisory prose
generated artifacts
implementation source
tests/fixtures
```

The broker must not treat advisory support text as lock-level normative law.

### 17.10 Adapter failure is visible

If an adapter fails, is disabled, or is outside scope, the report states that fact. The worker cannot make absence claims over that store.

### 17.11 Query branches are reproducible

A reviewer can rerun the same plan against the same source set and reproduce:

```text
query terms
branch order
searched stores
budget clipping
coverage status
```

### 17.12 Lexical outside-plan search is quarantined

If the worker performs extra search outside the broker plan, those results are marked:

```text
outside_plan_advisory
```

They cannot satisfy broker-covered evidence slots unless a new branch is admitted.

---

## 18. Non-goals

This v0 architecture does not attempt to:

```text
build a universal ontology
replace all search systems
replace vector retrieval
prove the canonical DB metaphysically complete
automate normative authority promotion
make advisory prose authoritative
implement ProgramBench itself
implement repo-wide semantic indexing in the first slice
let the broker silently mutate the concept DB
convert LLM prompt behavior into institutional authority by naming it a broker
treat retrieved chunks as proof without admissibility review
solve all long-context failures
remove worker judgment
remove auditor review
```

The broker narrows and audits retrieval. It does not eliminate reasoning.

---

## 19. Open questions

1. **Package boundary:** should this become a new `packages/adeu_conceptual_retrieval` package, or live under an existing harness / core IR lineage?

2. **Authority posture:** should concept DB seed files be support-level, architecture-level, or ANM-native governed artifacts once stabilized?

3. **Concept DB source format:** JSON only, `.adeu.md` source plus derived JSON, or hybrid?

4. **ANM integration:** for D-lane retrieval, should the broker consume compiled ANM artifacts instead of raw markdown?

5. **Domain pack governance:** who can publish or promote a domain pack?

6. **Confidence promotion rule:** what exact evidence is required for `seeded -> evidence_backed -> stabilized`?

7. **Auditor implementation:** deterministic policy first, human review first, model-assisted review, or mixed?

8. **Vector adapter boundary:** how should vector recall be admitted without bypassing typed relation paths?

9. **ProgramBench witness sufficiency:** which probes count as adequate behavioral witnesses?

10. **Regression corpus:** which ADEU repo-search tasks become golden retrieval fixtures?

11. **Operator projection:** what minimal UI exposes concept resolution and coverage gaps without implying ratification?

12. **External evidence stores:** which external tools are allowed, and how are their outputs hashed, bounded, and authority-scoped?

Recommended next move: define the v0 schema family and a hand-authored `adeu_repo` concept seed, then test it against two fixtures: runtime provider persistence retrieval and one ANM/D@1 normative retrieval task.
