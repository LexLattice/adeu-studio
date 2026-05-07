# ARCHITECTURE: ADEU Conceptual-First Retrieval Pipeline v0.1 Hardening Draft

**Status:** architecture / doctrine hardening draft.
**Baseline:** preserves the retained `ADEU Conceptual-First Retrieval Pipeline v0.md` architecture note and tightens its governability around concept identity, claim/evidence binding, absence claims, task-profile defaults, ProgramBench cleanroom admissibility, and Slice 0 limits.
**Authority posture:** this note proposes a hardened ADEU-native retrieval family. It does not authorize implementation, schema release, ANM authority promotion, runtime behavior, or canonical DB promotion by itself.

---

## 1. Executive thesis

Current retrieval makes the worker/model reconstruct its conceptual neighborhood every time. The worker must repeatedly guess aliases, implementation surfaces, witness forms, neighboring concepts, storage substrates, lifecycle concepts, and failure modes before it can even search. That behavior is unstable, prompt-sensitive, non-exhaustive, and difficult to audit.

ADEU should externalize that recurring burden into a canonical, auditable, additive semantic broker:

```text
worker declares retrieval intent
  -> broker resolves intent to canonical ODEU concepts
  -> broker applies task-profile defaults and legal option bounds
  -> worker selects or overrides axes / depth / budget / stores
  -> broker expands deterministically across selected typed axes
  -> broker realizes conceptual branches into store-specific queries
  -> broker queries shallow evidence stores
  -> broker returns evidence candidates + store coverage + coverage report
  -> worker binds claims to evidence candidates
  -> auditor checks claim/evidence/coverage/admissibility alignment
```

The core v0.1 correction is:

```text
The Canonical ODEU Concept DB must define concept identity,
not merely concept relatedness.
```

Without concept boundary law, deterministic expansion can deterministically expand the wrong ontology.

The worker should not have to invent the whole conceptual zone. It should declare:

```text
what it needs to know
why it needs to know it
which O/E/D/U lanes are active
which task profile applies
which typed conceptual axes may expand
how far expansion may go
what evidence would count
what drift/noise budget is acceptable
which evidence stores are admissible
which claim types it expects to make
```

The broker should then serve a deterministic retrieval result relative to:

```text
a versioned canonical concept graph
concept boundary records
a retrieval task profile
a declared source set
selected relation axes
store-specific query realizations
evidence admissibility rules
store coverage manifests
```

**Observed repo grounding**

Targeted inspection in the retained baseline found adjacent doctrine but no first-class `CanonicalODEUConceptDB`, `SemanticBroker`, `ConceptualSearchPlan`, `ClaimEvidenceBinding`, or `EvidenceCoverageReport` surface.

Relevant observed grounding preserved from v0:

```text
O/E/D/U decomposition
typed IR
explicit evidence
fail-closed validation
stable hashes
ANM authority-layer discipline
D@1 normative block discipline
schema meta-grammar posture
operator projection non-ratification
resident-agent continuation boundaries
brokered reflexive execution precedent
```

**Inferred:** conceptual-first retrieval should become a bounded institutional retrieval component, not another LLM prompt style.

**Recommended:** introduce a small v0.1 family centered on:

```text
CanonicalODEUConceptDB
ConceptBoundary
RetrievalTaskProfile
SemanticBroker
ConceptualSearchPlan
QueryBranch
StoreQueryRealization
EvidenceCandidate
StoreCoverageManifest
EvidenceCoverageReport
ClaimEvidenceBinding
ConceptDBPatchProposal
DriftWarning
```

This is still a small v0 family. The added objects exist to make the retrieval circuit governable, not to create a giant schema universe.

---

## 2. Conceptual-first retrieval v0 laws

These laws are compact normative doctrine for the v0.1 architecture.

1. **Intent law:** a worker **MUST** declare `RetrievalIntent@1` before brokered search.

2. **Resolution law:** a broker **MUST** resolve retrieval intent to canonical concepts or report ambiguity and unresolved terms.

3. **Typed expansion law:** a broker **MUST** expand only over selected typed axes admitted by the active task profile, authority boundary, and drift policy.

4. **Branch preservation law:** a query branch **MUST** preserve root concept, expanded concept, relation path, store, and expected witness kind.

5. **Lexical insufficiency law:** a lexical match **MUST NOT** satisfy a witness requirement.

6. **Absence law:** a `checked_no_witness` result **MUST** include source/store coverage sufficient for the absence claim type.

7. **Coverage law:** a worker **MUST NOT** claim coverage outside the `EvidenceCoverageReport@1`.

8. **D-lane admissibility law:** a D-lane claim **MUST** use authority-admissible evidence.

9. **Concept DB mutation law:** a concept DB mutation **MUST** occur only through `ConceptDBPatchProposal@1` and review.

10. **Bounded exhaustiveness law:** every coverage report **MUST** state what is closed and what is not closed.

These are not implementation details. They are the doctrine the implementation must preserve.

---

## 3. Problem statement

The retrieval problem is not merely “bad keywords.” Normal search collapses several distinct acts into one unstable prompt:

```text
identify relevant concepts
  + define concept boundaries
  + distinguish nearest confusables
  + invent aliases
  + infer neighboring concepts
  + decide which relation axes matter
  + generate store-specific queries
  + retrieve chunks
  + classify evidence
  + bind evidence to claims
  + remember coverage gaps
```

This causes ADEU-specific failures:

| Domain                                | Failure                                                                                                                                               |
| ------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------- |
| Repo search                           | Worker searches one phrase and misses implementation surfaces, persistence surfaces, read/write paths, or local vocabulary.                           |
| Agent harness state recovery          | Transcript memory or continuity context is confused with typed continuation state.                                                                    |
| ProgramBench-style black-box recovery | Command ontology, config precedence, defaults, side effects, negative behavior, and parser precedence are missed or inferred from forbidden evidence. |
| ANM / D@1 retrieval                   | Support prose, architecture drafts, generated views, and recognized normative authority blocks are conflated.                                         |
| Long-context / sparse-attention runs  | Lexical hits are retrieved but witness slots remain uncovered.                                                                                        |
| Test/witness discovery                | Worker misses negative probes, fixture surfaces, edge cases, or no-witness checks.                                                                    |
| Capability-probe routing              | Tests, probe templates, edge classes, witness forms, and failure modes are not expanded consistently.                                                 |
| Absence claims                        | “Nothing found by grep” is treated as “nothing exists.”                                                                                               |
| Claim support                         | Evidence chunks are collected, but no explicit edge records which claim they support.                                                                 |

The core failure is conceptual coverage and claim/evidence governance, not string matching.

ADEU already separates ontology, evidence, deontic authority, and utility tradeoffs. Retrieval should preserve the same separation.

---

## 4. Core doctrine

### 4.1 Retrieval begins from canonical concepts

The worker may say:

```text
I need to find where runtime model/provider selection is persisted.
```

The worker should not have to manually invent:

```text
provider choice
model selection
runtime profile
policy profile
frontend local state
persisted user preference
fallback/default
runtime config
environment variable
SQLite row
worker run
copilot session
capability probe
provider parity
IPC update path
storage substrate
read path
write path
```

The broker should resolve the intent against canonical ODEU concepts and expose a bounded option space.

### 4.2 Concept identity precedes concept expansion

A canonical concept is not just a node with neighbors.

It must answer:

```text
what exactly is this concept?
how is it distinguished from nearest confusables?
what positive examples count?
what negative examples do not count?
what evidence would prove we found this concept rather than a cousin?
what probes would distinguish it from adjacent concepts?
```

Without this boundary law, deterministic expansion can deterministically amplify a wrong ontology.

### 4.3 Relation axes are closed and typed

The canonical DB is not a synonym table. It is a typed graph with concept boundaries.

The worker does not ask for “related things.” The worker or task profile selects typed axes:

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

Profile-level subaxes may compile into these relation types plus expected witness kinds.

Example:

```text
write_path
  compiles to:
    relation type: implementation_surface
    expected witness kind: storage_write_witness

read_path
  compiles to:
    relation type: implementation_surface
    expected witness kind: storage_read_witness

fallback/default
  compiles to:
    relation type: failure_mode
    expected witness kind: default_value_or_fallback_witness

tests_fixtures
  compiles to:
    relation types: evidence_surface, test_witness_template
```

This avoids expanding the global relation enum prematurely.

### 4.4 Worker axis selection must be task-profile shaped

The architecture must not move from:

```text
vibing search terms
```

to:

```text
vibing expansion axes
```

A `RetrievalTaskProfile@1` supplies default roots, default axes, required witness kinds, forbidden axes, store defaults, drift limits, and claim admissibility expectations for recurring task classes.

Worker selection remains allowed, but it occurs inside a broker-proposed and profile-shaped option space.

### 4.5 Lexical hits are not evidence witnesses

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
  vs
source absence was checked under an explicit store coverage manifest
```

This follows ADEU witness discipline:

```text
raw transcript is not native witness
support docs do not mint runtime authority
projection is not ratification
generated views are not authority by themselves
candidate evidence is not proof
lexical match is not witness
checked-no-witness is not grep-found-nothing
```

### 4.6 Claims must bind to evidence

Evidence retrieval is not complete until claims bind to evidence.

The key question is not merely:

```text
what chunks were found?
```

It is:

```text
which exact claim does this evidence support,
under which admissibility rule,
with what support strength,
with what remaining gaps,
relative to which coverage report?
```

Workers may cite `EvidenceCandidate@1` records only through `ClaimEvidenceBinding@1` when making factual, implementation, persistence, runtime, normative, or absence claims.

### 4.7 Exhaustiveness is bounded

The broker cannot say:

```text
all relevant evidence has been found
```

It can say:

```text
all selected concepts, relation axes, depths, confidence tiers,
store query realizations, and evidence stores in this plan were expanded
and searched, except the listed skipped / clipped / failed branches
```

That is the ADEU form of retrieval exhaustiveness: closed relative to an explicit plan envelope and source/store universe.

### 4.8 No authority laundering

The broker retrieves and classifies. It does not promote prose into law, chunks into proof, UI projection into authority, hidden tests into inference evidence, or candidate relations into canonical ontology.

For D-lane retrieval, only authority-admissible sources can satisfy normative claims. ANM/D@1 authority posture must remain explicit.

---

## 5. End-to-end pipeline

### 5.1 Primary data flow

```text
RetrievalTaskProfile@1
  -> RetrievalIntent@1
  -> concept resolution
  -> ConceptBoundary@1 review / boundary warning
  -> expansion option set
  -> profile defaults + worker-selected expansion envelope
  -> ConceptualSearchPlan@1
  -> deterministic graph expansion
  -> QueryBranch@1 records
  -> StoreQueryRealization@1 records
  -> shallow store adapter calls
  -> EvidenceCandidate@1 records
  -> StoreCoverageManifest@1 records
  -> EvidenceCoverageReport@1
  -> ClaimEvidenceBinding@1
  -> worker answer / further expansion / audit
  -> optional ConceptDBPatchProposal@1
```

### 5.2 Primary control flow

The protocol is intentionally staged.

**Stage A — Task frame and profile**

The harness establishes an active task frame and chooses a retrieval task profile.

Example profiles:

```text
repo_implementation_location_search
repo_persistence_search
programbench_behavior_recovery
anm_d1_normative_retrieval
agent_harness_state_recovery
test_witness_discovery
capability_probe_routing
```

**Stage B — Intent and concept resolution**

The worker declares what it needs. The broker resolves canonical concepts and reports ambiguity or unresolved terms.

**Stage C — Boundary check**

The broker checks whether resolved concepts have boundary definitions.

If a concept is boundary-incomplete, the broker may still proceed, but it must emit a drift warning and reduce permissible claim strength.

**Stage D — Profile-shaped expansion selection**

The broker proposes legal expansion options. The task profile supplies defaults and required high-value axes. The worker may select, exclude, or override axes, but exclusions are recorded.

**Stage E — Deterministic expansion and query planning**

The broker expands the graph deterministically and emits conceptual query branches.

**Stage F — Store-specific query realization**

Each conceptual branch is realized into store-specific queries. `repo_grep`, `ast_symbol`, `docs_anm`, `tests_fixtures`, and ProgramBench probe stores require different realizers.

**Stage G — Evidence retrieval and classification**

Adapters return evidence candidates plus store coverage manifests. Candidates are not claims.

**Stage H — Coverage and claim binding**

The broker emits a coverage report. The worker binds claims to evidence candidates through `ClaimEvidenceBinding@1`.

**Stage I — Audit or further expansion**

The auditor checks support. The worker may reason, request another expansion, or propose a concept DB patch.

### 5.3 Worker / harness responsibilities

The worker or harness provides:

```text
active task frame
retrieval task profile
retrieval objective
reason for retrieval
desired O/E/D/U lanes
expected claim types
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
cleanroom boundary, where applicable
prior coverage report refs, if continuing
```

The worker may formulate intent and choose from broker options. It must not silently introduce unexpanded concepts as if they were covered.

### 5.4 Broker responsibilities

The broker must:

```text
validate RetrievalIntent@1
validate RetrievalTaskProfile@1
resolve terms to canonical concepts
report ambiguity and unresolved terms
check ConceptBoundary@1 availability
report boundary-incomplete concepts
propose bounded expansion options
apply task-profile defaults
expand the concept graph deterministically
generate stable QueryBranch@1 records
realize branches into StoreQueryRealization@1 records
call shallow evidence-store adapters
classify returned chunks as candidates
preserve branch provenance and relation paths
distinguish lexical matches from witnesses
emit StoreCoverageManifest@1 records
emit drift warnings
emit coverage accounting
report unresolved slots
produce deterministic hashes for plans, realizations, manifests, and reports
```

The broker must not:

```text
invent new canonical relations during retrieval
widen selected axes silently
treat vector similarity as a typed relation
treat lexical hits as semantic support
treat grep failure as absence proof
make advisory text authoritative
mutate the canonical DB directly
hide skipped, clipped, or failed branches
query forbidden ProgramBench evidence stores
collapse concept boundary warnings into normal confidence
```

### 5.5 Auditor responsibilities

The auditor checks whether downstream claims are supported by served evidence and coverage.

The auditor asks:

```text
Did the worker cite evidence through ClaimEvidenceBinding@1?
Does candidate kind support the claim type?
Does the support relation match the admissibility rule?
Are D-lane claims backed by authority-admissible sources?
Are absence claims backed by checked-no-witness plus StoreCoverageManifest@1?
Did lexical matches get overstated as witnesses?
Are unresolved or boundary-incomplete slots material?
Did drift warnings invalidate or weaken the answer?
Were required task-profile axes excluded?
Is a concept DB patch proposal evidence-backed?
```

The auditor may be deterministic policy, human, model-assisted, or mixed. The audit record must be explicit either way.

### 5.6 Shallow store adapter responsibilities

Adapters retrieve and annotate. They do not become semantic authorities.

Initial adapter classes:

| Adapter              | Role                                                                 |
| -------------------- | -------------------------------------------------------------------- |
| `repo_grep`          | Exact / alias / canonical term search over declared repo source set. |
| `docs_anm`           | ANM/D@1 block extraction and authority-layer-aware docs search.      |
| `schema_json`        | JSON schema and model-field search.                                  |
| `ast_symbol`         | Language-aware symbol/class/function/type lookup.                    |
| `tests_fixtures`     | Tests, fixtures, golden files, probe fixtures.                       |
| `git_history`        | Commit/diff/log search, when allowed.                                |
| `vector_index`       | Optional recall aid, always attached to a typed branch.              |
| `programbench_probe` | Cleanroom-visible command execution and probe logs.                  |
| `external_tool`      | Allowed only under explicit task/tool authority.                     |

Every adapter returns:

```text
source refs
spans where available
source hashes
store coverage manifest refs
query provenance
adapter limitations
budget clipping status
failed branches
```

---

## 6. Component architecture

### 6.1 `CanonicalODEUConceptDB`

A versioned typed concept graph plus boundary records.

It stores canonical concepts, concept boundaries, relation edges, aliases, evidence surfaces, witness templates, failure modes, domain packs, task-profile affordances, confidence tiers, provenance, deprecation records, and conflict records.

It is an O-lane substrate with E-lane provenance and D-lane admissibility metadata. It is not a vector DB and not a normative authority source by itself.

### 6.2 `ConceptBoundary`

Defines concept identity and nearest-confusable distinctions.

The boundary object prevents deterministic expansion from amplifying an underspecified or wrong concept.

### 6.3 `RetrievalTaskProfile`

Shapes broker defaults so the worker does not vibe expansion axes.

It supplies:

```text
default roots
default axes
required high-value axes
default stores
forbidden stores
claim-type admissibility rules
drift policy
coverage expectations
cleanroom constraints, where applicable
```

### 6.4 `SemanticBroker`

The deterministic retrieval coordinator.

Consumes:

```text
RetrievalIntent@1
RetrievalTaskProfile@1
CanonicalODEUConceptDB version/hash
ConceptBoundary refs
active task frame
domain profile
authority/admissibility policy
adapter registry
optional prior coverage report
```

Emits:

```text
concept resolution result
boundary warnings
expansion options
ConceptualSearchPlan@1
QueryBranch@1 records
StoreQueryRealization@1 records
EvidenceCandidate@1 records
StoreCoverageManifest@1 records
EvidenceCoverageReport@1
DriftWarning@1 records
optional ConceptDBPatchProposal@1
```

### 6.5 Concept resolver

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

### 6.6 Boundary evaluator

Checks whether resolved concepts have sufficient identity law for the active task.

Outputs:

```text
boundary_complete
boundary_incomplete
boundary_conflict
boundary_task_mismatch
confusable_requires_disambiguation
```

Boundary-incomplete concepts may be used for exploratory retrieval, but factual claim strength is reduced unless the worker/auditor supplies a binding with adequate evidence.

### 6.7 Expansion engine

Walks the typed concept graph under selected controls:

```text
root concepts
allowed relation types
denied relation types
profile-required axes
max depth
confidence threshold
domain pack
drift budget
store allowlist
authority boundary
cleanroom boundary
```

Output:

```text
expanded concept closure
preserved relation paths
skipped edges with reasons
excluded high-value axes
drift warnings
deterministic ordering trace
```

Stable ordering should be:

```text
root concept ID
  -> relation type canonical order
  -> relation ID
  -> target concept ID
  -> profile subaxis order
  -> store adapter order
```

### 6.8 Query planner

Turns expansion closure into `QueryBranch@1` records.

A query branch is conceptual, not a store-specific query string. It records why retrieval exists:

```text
root concept
expanded concept
relation path
relation types
profile subaxis
expected evidence surface
expected witness kind
admissibility filter
budget
drift risk
branch hash
```

### 6.9 Store query realizer

Turns `QueryBranch@1` into `StoreQueryRealization@1`.

Different stores require different realizers:

| Store                | Realization examples                                                                             |
| -------------------- | ------------------------------------------------------------------------------------------------ |
| `repo_grep`          | Literal aliases, canonical labels, snake_case, camelCase, path terms.                            |
| `ast_symbol`         | Class names, function names, type names, exported symbols, call sites.                           |
| `docs_anm`           | Headings, D@1 selectors, authority blocks, prose zones, support boundaries.                      |
| `tests_fixtures`     | Test names, fixture names, golden file paths, assertion terms.                                   |
| `programbench_probe` | Command invocations, invalid inputs, stdout/stderr/exit-code probes, filesystem mutation probes. |
| `schema_json`        | Field names, enum values, schema IDs, object paths.                                              |

This prevents the broker from pretending that canonical concept to query string is trivial.

### 6.10 Evidence candidate classifier

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
forbidden_evidence
worker_generated_evidence
evaluation_only_evidence
```

Classification can use deterministic rules first and optional model review second. The record must say how classification was made.

### 6.11 Coverage reporter

The coverage reporter is the broker’s audit spine.

It records:

```text
roots selected
axes selected
axes profile-required
axes excluded
excluded high-value axes
depth
confidence tier
stores selected
stores excluded
store coverage manifests
branches generated
branches realized
branches searched
branches skipped
branches clipped
candidates found
lexical-only branches
witness slots filled
empty witness slots
checked-no-witness slots
unresolved terms
ambiguous concepts
boundary-incomplete concepts
drift warnings
adapter failures
bounded exhaustiveness statement
```

### 6.12 Claim/evidence binder

The binder records the explicit relation between a worker claim and supporting evidence.

It is the bridge from retrieval to reasoning.

A worker answer should not cite raw evidence candidates directly for factual, implementation, persistence, runtime, normative, or absence claims. It should cite `ClaimEvidenceBinding@1` records.

### 6.13 Operator / projection surface

A future UI may project:

```text
concept resolution
concept boundaries
confusables
expansion options
profile defaults
plan branches
store query realizations
candidate evidence
store coverage
coverage gaps
claim/evidence bindings
drift warnings
patch proposals
```

Projection does not ratify concepts, relations, claims, evidence, or authority.

---

## 7. Canonical ODEU Concept DB

### 7.1 What is stored

`CanonicalODEUConceptDB` stores a curated typed graph plus concept boundary records.

Each concept record should include:

```text
concept_id
canonical_label
short_definition
boundary_ref
boundary_status
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

The DB should not store only synonyms. It should store typed semantic affordances and identity boundaries for retrieval.

### 7.2 Required relation types

| Relation type                | Meaning                                                     | Example                                                                  |
| ---------------------------- | ----------------------------------------------------------- | ------------------------------------------------------------------------ |
| `alias`                      | Alternate term for same concept, scoped where needed.       | `provider_choice` ↔ `model_selection`, only if scoped and boundary-safe. |
| `genus`                      | Broader class.                                              | `CLI_flag` → `command_interface_element`.                                |
| `species`                    | Narrower class.                                             | `config_file` → `toml_config_file`.                                      |
| `sibling`                    | Adjacent concept under shared parent.                       | `stdout` ↔ `stderr`.                                                     |
| `part_whole`                 | Component or aggregate relation.                            | `subcommand` → `command_ontology`.                                       |
| `implementation_surface`     | Code/symbol/API surface likely to implement concept.        | `provider_choice` → `ProviderKind`.                                      |
| `evidence_surface`           | Source class likely to evidence concept.                    | `config_precedence` → docs/tests/probe logs.                             |
| `deontic_law`                | Relevant rule, prohibition, obligation, authority boundary. | `D@1_block` → `authority_zone`.                                          |
| `utility_axis`               | Objective/tradeoff axis.                                    | `recall` → `broad_expansion`.                                            |
| `test_witness_template`      | Expected test/probe witness shape.                          | `error_behavior` → invalid-input probe.                                  |
| `failure_mode`               | Known failure pattern.                                      | `lexical_hit_as_witness`.                                                |
| `lifecycle_phase`            | Concept status or phase.                                    | `candidate_relation` → `promotion_review`.                               |
| `storage_substrate`          | Persistence layer.                                          | `runtime_selection` → SQLite/env/config.                                 |
| `protocol_action_surface`    | Action/API/IPC/CLI surface.                                 | `provider_update` → request endpoint.                                    |
| `domain_specific_edge_class` | Domain-local edge taxonomy.                                 | ADEU witness / edge / obligation class ref.                              |

### 7.3 Relation record requirements

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
boundary_dependency_refs
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
boundary-incomplete source or target concepts trigger drift warnings
```

### 7.4 Confidence tiers

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

### 7.5 Boundary statuses

Minimal v0 statuses:

| Status                | Meaning                                                                |
| --------------------- | ---------------------------------------------------------------------- |
| `boundary_complete`   | Has sufficient definition and confusable distinctions for default use. |
| `boundary_incomplete` | Usable for exploratory retrieval; claim strength reduced.              |
| `boundary_conflicted` | Known disagreement; requires disambiguation.                           |
| `boundary_deprecated` | Retained for audit; excluded by default.                               |

### 7.6 Domain packs

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

A concept may appear in multiple packs, but relation semantics and aliases should be scoped when meaning differs.

Example:

```text
model_selection
  in adeu_repo:
    ambiguous among provider choice, proposer backend, Codex worker runtime,
    policy profile, frontend local state, and capability model

  in programbench_cli:
    may mean CLI/config model parameter only if task evidence supports it
```

### 7.7 O/E/D/U posture of the DB

| Lane  | DB role                                                                                                  |
| ----- | -------------------------------------------------------------------------------------------------------- |
| **O** | Canonical concepts, concept boundaries, relation graph, domain packs, concept slots.                     |
| **E** | Provenance refs, supporting evidence refs, witness templates, boundary examples.                         |
| **D** | Relation admissibility, authority posture, forbidden expansions, boundary requirements, promotion rules. |
| **U** | Retrieval utility hints, drift risk, recall/precision affordances, task-profile defaults.                |

The DB itself is primarily O-lane. It can carry E/D/U metadata, but it should not become D-lane authority by existence.

---

## 8. Concept identity and boundary law

### 8.1 Doctrine

Conceptual-first retrieval fails if canonical concepts are only neighborhood hubs.

A canonical concept must define:

```text
what is inside the concept
what is outside the concept
what nearby concepts are easily confused
what questions distinguish the concept from its neighbors
what evidence would count as a witness
what evidence would only be a cousin or surface similarity
```

This is necessary because deterministic expansion only makes the selected ontology more repeatable. It does not make the ontology correct.

```text
Wrong concept boundary
  -> deterministic wrong expansion
  -> reproducible wrong coverage
  -> overconfident wrong claim
```

### 8.2 `ConceptBoundary@1`

Purpose: identity law for a canonical concept.

Minimal fields:

```text
schema
boundary_id
concept_id
formal_definition
positive_examples[]
negative_examples[]
neighboring_confusables[]
distinguishing_questions[]
distinguishing_probe_templates[]
boundary_conditions[]
known_overgeneralizations[]
known_undergeneralizations[]
required_witness_kinds[]
invalid_witness_kinds[]
domain_scope_refs[]
authority_posture
provenance_refs[]
review_status
boundary_hash
```

Rules:

```text
boundary is part of concept identity
concept_id is identity; label is not identity
aliases must not override boundary law
boundary-incomplete concepts trigger drift warnings
boundary-conflicted concepts require disambiguation before strong claims
positive examples are not exhaustive
negative examples prevent cousin concepts from being treated as witnesses
```

### 8.3 ADEU provider-selection boundary example

Concept family:

```text
provider_choice
model_selection
runtime_profile
capability_model
policy_profile
frontend_local_state
persisted_preference
worker_run_provider_field
```

Boundary distinction:

| Concept                     | Inside boundary                                                                | Outside boundary                                                                                |
| --------------------------- | ------------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------- |
| `provider_choice`           | Selection among supported provider backends such as `mock`, `openai`, `codex`. | Any model parameter, UI state, policy profile, or capability profile unless linked by evidence. |
| `model_selection`           | Ambiguous term requiring domain scoping.                                       | Must not be global alias for provider choice.                                                   |
| `runtime_profile`           | Runtime execution profile or mode.                                             | Not automatically provider choice.                                                              |
| `capability_model`          | Capability/probe model or capability profile.                                  | Not a user/provider selection unless evidence links it.                                         |
| `policy_profile`            | Deontic/policy configuration profile.                                          | Not a runtime provider setting by default.                                                      |
| `frontend_local_state`      | UI component state.                                                            | Not persistence without storage or reload witness.                                              |
| `persisted_preference`      | Durable user/system preference across sessions.                                | Not request payload, local transient state, or worker-run historical field alone.               |
| `worker_run_provider_field` | Provider value stored for a specific worker run.                               | Not necessarily a global preference.                                                            |

Distinguishing questions:

```text
Is this value selected by the user/operator, by a request default, or by policy?
Is it durable across sessions?
Is it stored before execution, during a run, or after a run?
Is it read back to determine future behavior?
Is it merely recorded as history?
Is it frontend-local state without storage?
Is it a provider backend, a model name, a capability probe result, or a policy profile?
```

Distinguishing probe templates:

```text
set provider -> reload UI -> observe persisted state
start worker run with provider -> inspect worker_run.provider
change policy profile -> observe whether provider changes
change capability probe result -> observe whether provider changes
inspect read path that selects provider for future run
inspect write path that records provider after request
```

Known overgeneralization:

```text
Any occurrence of "model" or "provider" means persisted provider preference.
```

Known undergeneralization:

```text
Only direct string "provider preference" counts, missing worker_run.provider,
profile policy, or request default paths.
```

### 8.4 ProgramBench boundary example

Concept family:

```text
config_file
default_config
environment_variable
CLI_flag_override
runtime_state
generated_output_artifact
```

Boundary distinction:

| Concept                     | Inside boundary                                       | Outside boundary                                                          |
| --------------------------- | ----------------------------------------------------- | ------------------------------------------------------------------------- |
| `config_file`               | Input artifact read by program to configure behavior. | Generated output, runtime memory, docs-only defaults.                     |
| `default_config`            | Default values applied without explicit input.        | User-provided config file unless default file is documented/probed.       |
| `environment_variable`      | Host environment key read by program.                 | CLI flag, config file field, shell alias.                                 |
| `CLI_flag_override`         | Command-line input that changes behavior.             | Environment variable or config file unless precedence witness links them. |
| `runtime_state`             | In-memory state during execution.                     | Persisted config or output artifact unless written/read.                  |
| `generated_output_artifact` | File/directory produced by execution.                 | Config file input, unless program mutates config intentionally.           |

Distinguishing questions:

```text
Was the artifact read before behavior occurred or written after behavior occurred?
Can a CLI flag override it?
Can an environment variable override it?
Does the value persist across invocations?
Is the artifact part of task input or generated output?
Was behavior observed through cleanroom-visible probes?
```

Distinguishing probe templates:

```text
run without config -> observe defaults
run with config -> observe changed behavior
run with env var only -> observe behavior
run with config + env + CLI flag -> observe precedence
run and diff filesystem before/after
run malformed config -> observe error class, stderr, exit code
```

### 8.5 Boundary and claim strength

Boundary status affects claim strength.

| Boundary status       |        Retrieval allowed? |                          Strong claim allowed? |
| --------------------- | ------------------------: | ---------------------------------------------: |
| `boundary_complete`   |                       Yes | Yes, if evidence/admissibility support exists. |
| `boundary_incomplete` |          Yes, exploratory |                  Only weak or qualified claim. |
| `boundary_conflicted` | Only after disambiguation |         No, until conflict resolved or scoped. |
| `boundary_deprecated` |            No default use |                                            No. |

Example:

```text
Claim:
  "Provider choice is persisted as a worker-run field."

Allowed if:
  provider_choice boundary distinguishes worker-run historical field from global persisted preference,
  evidence candidate shows storage schema/write path,
  claim wording does not overstate global preference.
```

Forbidden overclaim:

```text
"Provider choice is persisted as a user preference."
```

unless read/write preference evidence exists.

---

## 9. Runtime protocol

### 9.1 Step 0 — Establish active task frame

The harness creates an active task frame:

```text
task_id
source_set_ref
source_set_hash
repo commit or artifact snapshot
worker role
retrieval_task_profile_ref
domain profile
authority boundary
cleanroom boundary, if applicable
allowed stores
forbidden stores
allowed tools
budget
prior coverage reports
expected claim types
```

This prevents retrieval from escaping the task.

### 9.2 Step 1 — Select `RetrievalTaskProfile@1`

The orchestrator or harness selects a task profile before expansion.

Examples:

#### Repo implementation-location search

Default axes:

```text
alias
implementation_surface
evidence_surface
tests_fixtures
```

Default stores:

```text
repo_grep
ast_symbol
schema_json
tests_fixtures
docs
```

High-value exclusions to report:

```text
tests_fixtures
ast_symbol
schema_json
```

#### Persistence-law search

Profile subaxes:

```text
alias
storage_substrate
write_path
read_path
fallback/default
tests_fixtures
```

Compiled relation types:

```text
alias
storage_substrate
implementation_surface
evidence_surface
test_witness_template
failure_mode
```

Required witness kinds:

```text
storage_schema_witness
storage_write_witness
storage_read_witness
default_value_witness
test_or_probe_witness
```

#### ProgramBench behavior recovery

Profile subaxes:

```text
command_ontology
input_class
output_class
error_class
side_effect
probe_template
config_precedence
parser_precedence
```

Default cleanroom-visible stores:

```text
task_docs
help_output
executable_probes
generated_outputs
filesystem_side_effect_diffs
candidate_local_tests
local_probe_logs
```

Forbidden inference stores:

```text
hidden_evaluator_tests
original_source_repo
online_repo_docs_issues
internet_search
git_history_outside_cleanroom_artifact
external_package_source_lookup
host_secrets
docker_socket
task_external_code_repositories
```

#### Normative ANM/D@1 retrieval

Profile subaxes:

```text
authority_surface
D@1_block
selector
compiled_D_IR
obligation_ledger
support_prose_boundary
```

Required witness kinds:

```text
recognized_authority_block
compiled_authority_artifact
authority_profile
obligation_ledger_entry
support_prose_boundary_marker
```

High-risk default:

```text
D-lane search requires explicit authority_boundary_ref.
```

### 9.3 Step 2 — Worker declares `RetrievalIntent@1`

Example:

```json
{
  "schema": "RetrievalIntent@1",
  "intent_id": "intent.adeu.runtime_provider_persistence",
  "active_task_frame_ref": "task.repo_search.provider_selection",
  "retrieval_task_profile_ref": "profile.repo_persistence_search",
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
  "expected_claim_types": [
    "implementation_location",
    "persistence_substrate",
    "absence_or_unwitnessed_gap"
  ],
  "required_evidence": [
    "implementation_surface",
    "storage_schema_witness",
    "storage_write_witness",
    "storage_read_witness",
    "checked_no_witness"
  ],
  "preferred_axes": [
    "alias",
    "storage_substrate",
    "write_path",
    "read_path",
    "fallback/default"
  ],
  "forbidden_axes": ["deontic_law"],
  "allowed_stores": ["repo_grep", "schema_json", "docs", "tests"],
  "recall_precision_posture": "recall_biased",
  "noise_budget": "medium"
}
```

### 9.4 Step 3 — Broker resolves concepts and checks boundaries

Example result:

```text
Resolved:
- runtime_selection
- provider_choice
- persistence_substrate

Boundary status:
- provider_choice: boundary_complete
- persistence_substrate: boundary_complete
- runtime_selection: boundary_incomplete; ambiguous with runtime_profile and frontend local state

Ambiguous:
- model_selection:
    may mean API proposer provider, Codex worker runtime, UI provider button,
    policy profile, or capability model

Unresolved:
- shell preference:
    not in active domain pack unless developer_environment is enabled
```

The broker does not hide unresolved, ambiguous, or boundary-incomplete concepts.

### 9.5 Step 4 — Broker proposes profile-shaped expansion options

| Axis / subaxis      | Source              | Default depth | Estimated concepts | Drift risk | Notes                                               |
| ------------------- | ------------------- | ------------: | -----------------: | ---------- | --------------------------------------------------- |
| `alias`             | profile default     |             1 |                  6 | low        | Provider/model/profile vocabulary.                  |
| `storage_substrate` | profile default     |             1 |                  5 | low        | SQLite/env/config/profile.                          |
| `write_path`        | profile default     |             1 |                  4 | low/medium | Compiles to implementation surface + write witness. |
| `read_path`         | profile default     |             1 |                  4 | medium     | Compiles to implementation surface + read witness.  |
| `fallback/default`  | profile default     |             1 |                  3 | medium     | Compiles to failure/default witness.                |
| `tests_fixtures`    | profile high-value  |             1 |                  5 | medium     | Useful for behavior/default validation.             |
| `deontic_law`       | forbidden by intent |             1 |                  7 | high       | Not needed for persistence search.                  |

### 9.6 Step 5 — Worker selects expansion envelope

Example:

```json
{
  "selected_axes": [
    "alias",
    "storage_substrate",
    "write_path",
    "read_path",
    "fallback/default",
    "tests_fixtures"
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
    "absence_claim_requires": [
      "checked_no_witness",
      "store_coverage_manifest",
      "no_relevant_budget_clipping"
    ]
  }
}
```

### 9.7 Step 6 — Broker emits `ConceptualSearchPlan@1`

The plan records:

```text
concept DB version/hash
resolved roots
concept boundary refs and statuses
retrieval task profile
selected axes
profile-default axes
excluded axes
excluded high-value axes
relation paths
query branches
stores
budget
drift policy
cleanroom policy, if applicable
deterministic ordering profile
plan hash
```

Same inputs must yield the same plan.

### 9.8 Step 7 — Broker emits `QueryBranch@1` and `StoreQueryRealization@1`

Conceptual branch example:

```text
root: provider_choice
expanded concept: worker_run_provider_field
relation path:
  provider_choice
    -> storage_substrate
    -> worker_run_provider_field
expected witness kind:
  storage_schema_witness or storage_write_witness
```

Store realizations:

```text
repo_grep:
  terms: provider, ProviderKind, worker_run, persist_worker_run_start
  normalization: case-sensitive + snake_case/camelCase expansion

schema_json:
  terms: provider, worker_run, storage, persistence
  expected shape: field definition / enum / schema object

ast_symbol:
  terms: ProviderKind, persist_worker_run_start
  expected shape: type alias / function definition / call site
```

### 9.9 Step 8 — Broker queries shallow stores

The broker dispatches only admitted realizations to adapters:

```text
repo_grep
schema_json
docs_anm
tests_fixtures
ast_symbol
git_history, if allowed
vector_index, if allowed and typed to a branch
programbench_probe, if cleanroom profile allows it
```

Each query is tied to a branch, relation path, expected witness kind, and store coverage manifest.

### 9.10 Step 9 — Broker classifies evidence candidates

Example distinction:

```text
"provider" appears in a path
  -> lexical_match

ProviderKind = Literal["mock", "openai", "codex"]
  -> implementation_surface_candidate

SQLite table `urm_worker_run` contains provider TEXT NOT NULL
  -> storage_schema_witness_candidate

persist_worker_run_start inserts request.provider into urm_worker_run
  -> storage_write_witness_candidate

API rejects unsupported provider
  -> failure_mode_witness_candidate

Frontend button calls setProvider("codex")
  -> protocol/UI selection candidate, not persistence witness

No localStorage/sessionStorage hit in targeted frontend pass
  -> checked_no_witness only if:
       source/store universe is declared,
       branches include frontend storage terms,
       no relevant clipping occurred,
       adapter limitations are recorded
```

### 9.11 Step 10 — Broker emits `EvidenceCoverageReport@1`

The report says:

```text
what was searched
what was not searched
what was found
what was lexical only
what was witness-like
what was checked and empty
what was ambiguous
what was boundary-incomplete
what was clipped
what stores failed or were excluded
what high-value profile axes were excluded
what absence claims are admissible or inadmissible
```

### 9.12 Step 11 — Worker binds claims or expands again

The worker may:

```text
create ClaimEvidenceBinding@1 records
answer using supported bindings
request another axis
deepen selected axes
add a store
ask for ambiguity resolution
submit a patch proposal
stop because evidence is insufficient
```

The worker may not silently fill gaps with vibes.

---

## 10. Schema sketches

These are minimal v0 schemas, not a giant schema universe.

They should follow the observed ADEU schema posture:

```text
required schema field
closed root
explicit anchors
governance posture
evidence / lineage refs
O/E/D/U realization
named residuals only
```

### 10.1 `CanonicalConceptRecord@1`

Purpose: canonical O-lane concept node.

```text
schema
concept_id
canonical_label
short_definition
boundary_ref
boundary_status
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
boundary_ref is expected for promoted concepts
aliases do not imply global equivalence
advisory notes cannot create relations
boundary_incomplete concepts reduce claim strength
```

### 10.2 `ConceptBoundary@1`

Purpose: identity and boundary law for a canonical concept.

```text
schema
boundary_id
concept_id
formal_definition
positive_examples[]
negative_examples[]
neighboring_confusables[]
distinguishing_questions[]
distinguishing_probe_templates[]
boundary_conditions[]
known_overgeneralizations[]
known_undergeneralizations[]
required_witness_kinds[]
invalid_witness_kinds[]
domain_scope_refs[]
authority_posture
provenance_refs[]
review_status
boundary_hash
```

Rules:

```text
boundary law constrains alias and relation use
boundary-incomplete concepts trigger DriftWarning@1
neighboring confusables must be surfaced during ambiguity resolution
```

### 10.3 `ConceptRelation@1`

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
boundary_dependency_refs[]
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
relation must not contradict source or target ConceptBoundary@1
```

### 10.4 `RetrievalTaskProfile@1`

Purpose: task-shaped defaults so axis selection is not vibes one level up.

```text
schema
profile_id
profile_label
task_class
domain_profile_refs[]
default_root_concepts[]
default_axes[]
required_high_value_axes[]
forbidden_axes[]
default_store_refs[]
forbidden_store_refs[]
required_witness_kinds[]
claim_type_admissibility_rules[]
default_depth
default_confidence_tier
default_budget
drift_policy_ref
cleanroom_policy_ref?
authority_boundary_required
profile_hash
```

Rules:

```text
worker may override profile defaults only explicitly
excluded required_high_value_axes appear in coverage report
auditor may reject claims when required axes were excluded
profile subaxes compile to canonical relation types and expected witness kinds
```

### 10.5 `RetrievalIntent@1`

Purpose: worker declaration of retrieval need.

```text
schema
intent_id
active_task_frame_ref
retrieval_task_profile_ref
worker_role
objective
why
seed_terms[]
seed_concept_ids[]
desired_odeu_lanes[]
expected_claim_types[]
required_evidence[]
allowed_stores[]
forbidden_stores[]
preferred_axes[]
forbidden_axes[]
recall_precision_posture
noise_budget
max_cost?
authority_boundary_ref?
cleanroom_boundary_ref?
prior_coverage_report_refs[]
freeform_context_advisory?
```

Rules:

```text
freeform context is advisory
D-lane retrieval requires authority boundary
ProgramBench retrieval requires cleanroom boundary
unresolved terms must be reported
```

### 10.6 `ConceptualSearchPlan@1`

Purpose: deterministic retrieval plan.

```text
schema
plan_id
intent_ref
retrieval_task_profile_ref
concept_db_ref
concept_db_hash
active_task_frame_ref
resolved_root_concept_ids[]
concept_boundary_refs[]
boundary_statuses[]
ambiguous_terms[]
unresolved_terms[]
selected_axes[]
profile_default_axes[]
excluded_axes[]
excluded_high_value_axes[]
max_depth
min_confidence_tier
domain_profile_ref
store_adapter_refs[]
query_branch_refs[]
budget
drift_policy_ref
cleanroom_policy_ref?
deterministic_ordering_profile
plan_hash
```

Rules:

```text
same inputs produce same plan_hash
selected axes are explicit
profile-default exclusions are explicit
skipped expansions are reportable
```

### 10.7 `QueryBranch@1`

Purpose: one conceptual search branch.

```text
schema
branch_id
plan_ref
root_concept_id
expanded_concept_id
relation_path[]
relation_types[]
profile_subaxis?
expected_evidence_surface
required_witness_kind?
admissibility_filter_ref?
store_adapter_refs[]
max_hits
branch_drift_risk
branch_hash
```

Rules:

```text
QueryBranch is conceptual, not store-specific syntax
relation path must preserve relation types
worker-supplied manual terms are marked noncanonical
store-specific realization occurs in StoreQueryRealization@1
```

### 10.8 `StoreQueryRealization@1`

Purpose: store-specific realization of a conceptual branch.

```text
schema
realization_id
branch_ref
store_adapter
canonical_terms[]
generated_terms[]
normalization_rules[]
query_filters
query_syntax
expected_result_shape
expected_witness_kind?
limitations[]
realization_hash
```

Rules:

```text
canonical concept does not directly equal query string
realization must be tied to a QueryBranch@1
store adapter limitations must be explicit
realization cannot add untyped concepts
```

### 10.9 `EvidenceCandidate@1`

Purpose: retrieved chunk, candidate witness, forbidden evidence marker, or negative check.

```text
schema
candidate_id
plan_ref
branch_ref
realization_ref
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
cleanroom_status?
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
forbidden_evidence
worker_generated_evidence
evaluation_only_evidence
```

Rules:

```text
excerpt text is bounded
summaries are advisory
lexical matches are not witnesses
candidate evidence is not proof
forbidden evidence cannot support inference claims
```

### 10.10 `StoreCoverageManifest@1`

Purpose: source/store coverage record required for checked-no-witness and absence claims.

```text
schema
manifest_id
plan_ref
store_ref
source_set_ref
source_set_hash
source_snapshot_ref
file_count?
object_count?
included_globs[]
excluded_globs[]
generated_vendor_binary_exclusions[]
query_normalization[]
case_sensitivity
adapter_limitations[]
budget_clipping_status
failed_branch_refs[]
unsearched_branch_refs[]
searched_branch_refs[]
timestamp_or_snapshot_ref
manifest_hash
```

Rules:

```text
checked_no_witness is not grep found nothing
absence claims require manifest coverage over relevant stores and branches
budget clipping prevents strong absence claims
adapter limitations must be included in coverage report
```

### 10.11 `EvidenceCoverageReport@1`

Purpose: retrieval accounting and bounded exhaustiveness statement.

```text
schema
report_id
plan_ref
concept_db_ref
source_set_ref
store_coverage_manifest_refs[]
searched_concept_slots[]
unsearched_concept_slots[]
searched_relation_axes[]
excluded_relation_axes[]
excluded_high_value_axes[]
searched_store_refs[]
unsearched_store_refs[]
branch_results[]
store_query_realization_refs[]
evidence_candidate_refs[]
resolved_concepts[]
ambiguous_concepts[]
unresolved_concepts[]
boundary_incomplete_concepts[]
empty_witness_slots[]
checked_no_witness_slots[]
invalid_absence_claim_slots[]
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
blocked_by_boundary_incompleteness
blocked_by_authority
blocked_by_cleanroom_policy
blocked_by_adapter_failure
clipped_by_budget
drift_limit_exceeded
```

### 10.12 `ClaimEvidenceBinding@1`

Purpose: explicit edge between a claim and the evidence used to support it.

```text
schema
binding_id
claim_id
claim_text_or_ref
claim_type
evidence_candidate_refs[]
support_relation
admissibility_rule_ref
admissibility_status
support_strength
unresolved_counterevidence_slots[]
coverage_report_ref
auditor_verdict
limitations[]
binding_hash
```

Claim types:

```text
implementation_location
persistence_substrate
storage_write_path
storage_read_path
runtime_behavior
normative_rule
authority_boundary
absence_claim
concept_db_promotion
deprecation
cleanroom_behavior_inference
```

Support strengths:

```text
unsupported
lexical_only
candidate_support
witness_support
authority_admissible_support
bounded_absence_support
contradicted
```

Rules:

```text
workers may cite EvidenceCandidate records only through ClaimEvidenceBinding
D-lane claims require authority-admissible support
absence claims require checked_no_witness plus StoreCoverageManifest
boundary-incomplete concepts reduce support strength unless resolved
```

### 10.13 `ConceptDBPatchProposal@1`

Purpose: additive improvement proposal.

```text
schema
proposal_id
proposal_kind
target_concept_id?
target_relation_id?
target_boundary_id?
proposed_concept_record?
proposed_relation_record?
proposed_boundary_record?
reason
supporting_evidence_candidate_refs[]
claim_evidence_binding_refs[]
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
add_boundary
revise_boundary
add_witness_template
deprecate_relation
deprecate_alias
split_concept
merge_concept
raise_confidence
lower_confidence
```

### 10.14 `DriftWarning@1`

Purpose: explicit drift/noise warning.

```text
schema
warning_id
plan_ref
branch_ref?
concept_id?
relation_id?
boundary_ref?
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
boundary_incomplete
boundary_conflict
depth_limit_pressure
budget_clipping
lexical_noise
authority_boundary_risk
cleanroom_boundary_risk
ambiguous_alias
stale_path_hint
adapter_undercoverage
model_supplied_uncanonical_term
vector_untyped_similarity
profile_required_axis_excluded
```

---

## 11. Deterministic/model/auditor split

### 11.1 Deterministic broker-owned operations

These must be deterministic:

```text
schema validation
retrieval task profile validation
canonical ID lookup
exact alias lookup
domain-scoped alias lookup
boundary status lookup
relation filtering
task-profile axis compilation
depth-limited graph expansion
confidence-tier filtering
domain-pack filtering
query branch generation from canonical terms
store query realization from declared rules
query ordering
store adapter dispatch order
source span hashing
de-duplication
budget clipping
store coverage accounting
drift scoring from declared formula
coverage accounting
plan/realization/manifest/report hashing
```

Given the same concept DB hash, boundary records, task profile, source set, broker version, intent, and selected options, the plan and coverage accounting should be reproducible.

### 11.2 Model-mediated operations

The model may perform:

```text
intent formulation
explanation of why retrieval is needed
initial seed term generation
selection among broker-proposed axes
explicit override of task-profile defaults
ambiguity adjudication when broker offers choices
semantic relevance review of evidence candidates
drafting ClaimEvidenceBinding records
decision to request another expansion
proposal of new candidate relations, concepts, or boundaries
```

Model outputs remain advisory unless admitted through deterministic or auditor-mediated workflow.

### 11.3 Auditor-mediated operations

The auditor decides:

```text
whether evidence candidates support downstream claims
whether claim type matches candidate kind
whether support relation matches admissibility rule
whether D-lane claims used authority-admissible sources
whether absence claims satisfy store coverage requirements
whether lexical hits were overstated
whether unresolved slots matter
whether boundary-incomplete concepts weaken or invalidate claims
whether excluded task-profile axes invalidate claims
whether drift warnings invalidate the answer
whether DB patch proposals are promotable
```

### 11.4 Human/operator responsibilities

Human or operator review is required for:

```text
canonical DB promotion
concept boundary promotion
high-impact concept splits/merges
deontic-law relation changes
authority grants
domain pack publication
task profile publication
ProgramBench cleanroom policy changes
promotion to stabilized
relation conflict settlement
deprecation of widely used relations
```

Operator projection may make cases visible. It must not ratify them by display.

---

## 12. Evidence, claim binding, and coverage semantics

### 12.1 Evidence classes

| Class                              | Meaning                                                              | Claim support posture                                    |
| ---------------------------------- | -------------------------------------------------------------------- | -------------------------------------------------------- |
| `lexical_match`                    | Term appears.                                                        | Never sufficient alone.                                  |
| `alias_match`                      | Alias appears.                                                       | Weak candidate.                                          |
| `structural_match`                 | Code/schema/prose shape aligns.                                      | Sometimes, with review.                                  |
| `implementation_surface_candidate` | Likely implementation location.                                      | Supports “where to inspect.”                             |
| `evidence_surface_candidate`       | Likely source of evidence.                                           | Supports further retrieval.                              |
| `witness_candidate`                | Likely direct support.                                               | Supports claim after admissibility check.                |
| `negative_witness_candidate`       | Evidence of failure/absence behavior.                                | Supports negative behavior after check.                  |
| `checked_no_witness`               | Declared slot searched and no witness found under explicit manifest. | Supports bounded gap / absence claim only with manifest. |
| `inadmissible`                     | Found but not allowed for claim.                                     | Cannot support claim.                                    |
| `stale_hint`                       | Old path/name likely stale.                                          | Warning only.                                            |
| `ambiguous`                        | Context insufficient.                                                | Requires review.                                         |
| `forbidden_evidence`               | Evidence exists but violates task boundary.                          | Cannot support inference.                                |
| `worker_generated_evidence`        | Produced by worker during local probes/tests.                        | Supports candidate behavior, not hidden truth by itself. |
| `evaluation_only_evidence`         | Hidden/evaluator-only signal.                                        | External court, not inference evidence.                  |

### 12.2 Claim-dependent admissibility

| Claim type                   | Required evidence                                                                        |
| ---------------------------- | ---------------------------------------------------------------------------------------- |
| Implementation location      | Source span, symbol span, schema span, or structural witness.                            |
| Persistence substrate        | Storage schema, write path, read path, config binding, or environment binding.           |
| Runtime behavior             | Test, probe log, fixture, executable witness, negative witness.                          |
| Normative rule               | Recognized authority block or compiled authority artifact.                               |
| Authority boundary           | ANM authority profile, policy artifact, lock, or compiled D artifact.                    |
| Absence claim                | `checked_no_witness` over declared source set and stores plus `StoreCoverageManifest@1`. |
| Cleanroom behavior inference | Cleanroom-visible docs/help/probes/generated outputs/side-effect diffs.                  |
| Concept DB promotion         | Evidence refs, claim/evidence bindings, coverage report, review decision.                |
| Deprecation                  | Failed retrieval examples or contrary evidence plus review.                              |

### 12.3 Claim/evidence binding rule

A worker answer should bind every substantive claim.

Example:

```text
Claim:
  URM worker runs persist the selected provider in SQLite.

Claim type:
  persistence_substrate

Evidence candidates:
  storage schema candidate for worker_run.provider
  write path candidate for persist_worker_run_start(request.provider)

Support relation:
  storage_schema_plus_write_path_supports_persistence_substrate

Admissibility:
  storage schema and write path are admissible for bounded persistence claim

Limitations:
  does not prove global user preference persistence
  does not prove frontend persistence
  does not prove read path for future provider selection unless read path candidate is bound
```

Forbidden binding:

```text
Claim:
  The repo has no persistent provider preference anywhere.

Evidence:
  grep found no "persistent provider preference"

Reason invalid:
  lexical absence only
  missing store coverage manifest
  missing frontend/browser/runtime/config/git/test coverage
  no checked-no-witness over required relation paths
```

### 12.4 Checked-no-witness and absence claims

A `checked_no_witness` result is valid only if the store universe is explicit.

Required for absence claims:

```text
checked_no_witness candidate
StoreCoverageManifest@1
source_set_hash
included/excluded globs
query normalization
case sensitivity
adapter limitations
no relevant budget clipping
no failed required branches
no unsearched required branches
required adapters enabled
query branches tied to all required relation paths
```

Invalid absence claims:

```text
"The repo has no persistent provider preference anywhere."
  Invalid unless UI, API, runtime config, storage, tests, git history,
  and environment/shell integration were covered or explicitly scoped out.

"No D-lane authority exists for this rule."
  Invalid unless ANM/D@1 authority stores, compiled D artifacts, obligation
  ledgers, selectors, and authority profiles were searched under a D-lane profile.

"ProgramBench task has no environment-variable behavior."
  Invalid unless cleanroom-visible docs/help/probes include env-var branches,
  env probes were run, and forbidden stores were not used.
```

Valid bounded absence form:

```text
No witness for frontend localStorage/sessionStorage provider persistence was found
within the declared frontend source files, using the listed storage-related query
branches, with no relevant clipping, under source_set_hash X.
```

### 12.5 Coverage statement form

Every coverage report must include a bounded statement like:

```text
Coverage is closed relative to:
- concept DB hash: X
- boundary hashes: B1, B2
- task profile: repo_persistence_search
- roots: runtime_selection, provider_choice
- axes: alias, storage_substrate, write_path, read_path
- depth: 1
- confidence tier: >= seeded
- stores: repo_grep, schema_json, docs
- store manifests: M1, M2, M3
- source set hash: Y

Coverage is not closed over:
- vector search
- git history
- external docs
- D-lane relations
- depth > 1
- unresolved term: shell preference
- excluded store: frontend runtime browser execution beyond static source grep
- boundary-incomplete concept: runtime_selection
```

### 12.6 Bounded exhaustiveness

Allowed statement:

```text
All selected relation paths matching the plan envelope were expanded,
all generated query branches were realized for selected stores,
and all realized branches were run against selected stores,
except the listed skipped/clipped/failed branches.
```

Forbidden statement:

```text
All relevant evidence has been found.
```

### 12.7 O/E/D/U mapping

| Lane  | Retrieval role                                                                                                                       |
| ----- | ------------------------------------------------------------------------------------------------------------------------------------ |
| **O** | Concept inventory, concept boundary, relation graph, active task frame, source/store identities, conceptual slots.                   |
| **E** | Retrieved chunks, source spans, witnesses, no-witness checks, store coverage manifests, claim/evidence bindings, provenance.         |
| **D** | Allowed axes, forbidden axes, authority boundaries, cleanroom boundaries, admissibility filters, store permissions, promotion rules. |
| **U** | Retrieval objective, noise budget, recall/precision posture, task-profile defaults, budget allocation, stop criteria.                |

This lane separation is the central reason the broker should exist.

---

## 13. Drift control

### 13.1 Drift sources

Retrieval drift occurs when:

```text
concept boundaries are incomplete
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
ProgramBench cleanroom boundaries are violated
advisory sources are used for authority claims
task-profile required axes are excluded without audit impact
```

### 13.2 Required controls

The broker enforces:

```text
ConceptBoundary@1 presence or warning
max_depth
max_concepts
max_branches
max_hits_per_branch
relation allowlist
relation denylist
confidence threshold
domain profile
retrieval task profile
store allowlist
store denylist
authority boundary
cleanroom boundary
evidence admissibility filter
active task frame binding
drift score threshold
budget clipping record
adapter failure record
store coverage manifest
```

### 13.3 Drift scoring

A simple deterministic v0 formula is enough:

```text
drift_score =
  boundary_incompleteness_penalty
  + relation_type_base_risk
  + confidence_penalty
  + depth_penalty
  + domain_crossing_penalty
  + store_weakness_penalty
  + lexical_noise_penalty
  + task_frame_mismatch_penalty
  + profile_required_axis_exclusion_penalty
  + cleanroom_boundary_penalty
  + hit_explosion_penalty
```

The exact weights are less important than determinism, recording, and regression tests.

### 13.4 High-risk relation types

Default v0 risk posture:

| Relation type                | Default risk                      |
| ---------------------------- | --------------------------------- |
| `alias`                      | Low, if scoped and boundary-safe. |
| `implementation_surface`     | Low/medium.                       |
| `storage_substrate`          | Low/medium.                       |
| `evidence_surface`           | Medium.                           |
| `protocol_action_surface`    | Medium.                           |
| `test_witness_template`      | Medium.                           |
| `failure_mode`               | Medium.                           |
| `species`                    | Medium.                           |
| `part_whole`                 | Medium.                           |
| `sibling`                    | Medium/high.                      |
| `genus`                      | High beyond depth 1.              |
| `utility_axis`               | High unless task requires it.     |
| `deontic_law`                | High, authority-bound.            |
| `domain_specific_edge_class` | Domain-dependent.                 |

### 13.5 Forbidden silent widening

The broker must warn or fail closed when:

```text
an unknown relation type appears
a concept has no boundary record
a concept boundary is conflicted
an alias resolves to multiple concepts
model adds an uncanonical term
a profile-required axis is excluded
a store adapter searches outside source set
D-lane retrieval lacks authority boundary
ProgramBench retrieval attempts forbidden evidence
a branch crosses a domain pack
vector search returns untyped similarity
branch count or hit volume exceeds budget
budget clipping affects absence claims
```

---

## 14. Canonical DB evolution workflow

### 14.1 Additive improvement

The DB improves through proposals, not silent mutation.

Workers may propose:

```text
new concept
new boundary
boundary revision
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
task-profile addition
```

Every proposal must include evidence candidates, claim/evidence bindings where applicable, and coverage report refs.

### 14.2 Promotion path

```text
candidate observation
  -> ConceptDBPatchProposal@1
  -> evidence/admissibility review
  -> boundary review
  -> conflict check
  -> retrieval regression check
  -> operator/human approval if high-impact
  -> promoted DB version
  -> changelog + semantic hash
```

### 14.3 Bad relation or boundary deprecation

Bad relations and bad boundaries are deprecated, not erased.

Deprecation record includes:

```text
relation_id or boundary_id
reason
failed retrieval examples
contrary evidence refs
replacement relation or boundary?
affected domain packs
affected task profiles
regression fixture added?
review decision
```

### 14.4 Confidence lifecycle

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

### 14.5 Boundary lifecycle

Recommended lifecycle:

```text
boundary_incomplete
  -> boundary_candidate
  -> boundary_reviewed
  -> boundary_stabilized

boundary_reviewed/stabilized -> boundary_deprecated
boundary_candidate -> boundary_rejected
```

Promoted concepts should not remain boundary-incomplete without a warning or explicit exception.

### 14.6 Domain pack governance

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

### 14.7 Retrieval regression tests

Every promoted relation and stabilized boundary should support at least one retrieval regression fixture.

Examples:

```text
root provider_choice + axis storage_substrate
  emits query branches for worker_run.provider

provider_choice boundary
  distinguishes worker-run provider field from global persisted user preference

root authority_zone + axis evidence_surface
  does not treat ordinary prose as normative

root error_behavior + axis test_witness_template
  includes negative probes

deprecated alias
  is excluded from default expansion

vector adapter
  cannot introduce an untyped concept branch

ProgramBench cleanroom profile
  blocks original source repo and hidden evaluator tests during inference
```

### 14.8 Conflict handling

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
add confusable boundary
require worker disambiguation
deprecate one relation
```

The broker should prefer explicit ambiguity to false unification.

---

## 15. ProgramBench cleanroom example

**Grounding status:** ProgramBench was not observed as an existing ADEU repo artifact in the targeted baseline pass. This section is a recommended adapter/profile pattern for ProgramBench-style black-box specification recovery.

### 15.1 Cleanroom doctrine

For ProgramBench-style tasks, retrieval must obey a cleanroom boundary.

The worker is trying to reconstruct behavior from admissible task-visible evidence, not from hidden implementation or evaluator artifacts.

Default inference-clean stores:

```text
task docs
help output
executable probes
generated outputs
filesystem side-effect diffs
candidate/local tests authored by worker
local probe logs
```

Default forbidden during inference:

```text
hidden evaluator tests
original source repo
online repo/docs/issues
internet search
git history unless included inside the allowed cleanroom artifact
external package/source lookup
host secrets
Docker socket
task-external code repositories
```

Source grep, AST search, and git history are allowed only over:

```text
worker-created candidate source
cleanroom-visible artifacts
task-provided source, if explicitly part of the task artifact
```

They are not allowed over the original hidden source.

The broker distinguishes:

| Evidence status              | Meaning                                          | Inference posture                                              |
| ---------------------------- | ------------------------------------------------ | -------------------------------------------------------------- |
| `cleanroom_visible_evidence` | Task docs/help/probes/outputs visible to worker. | Admissible.                                                    |
| `worker_generated_evidence`  | Worker-created tests/probes/candidate outputs.   | Useful but must trace to cleanroom evidence or explicit probe. |
| `evaluation_only_evidence`   | Hidden tests/evaluator outcome.                  | External court, not inference evidence.                        |
| `forbidden_evidence`         | Violates cleanroom boundary.                     | Cannot support inference.                                      |

Hidden tests are an external court. They are not inference evidence.

### 15.2 Task

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

No implementation should begin until the O-entity inventory and boundary definitions are good enough to avoid implementing a cousin behavior.

### 15.3 Worker intent

```json
{
  "schema": "RetrievalIntent@1",
  "intent_id": "intent.programbench.behavior_recovery",
  "retrieval_task_profile_ref": "profile.programbench_behavior_recovery_cleanroom",
  "objective": "Recover the program behavior ontology before implementation.",
  "why": "Build a ProgramODEUProfile from cleanroom-visible evidence rather than guessing behavior or using forbidden sources.",
  "seed_terms": [
    "CLI behavior",
    "config precedence",
    "default values",
    "error behavior",
    "output artifact",
    "file side effect"
  ],
  "desired_odeu_lanes": ["O", "E", "D", "U"],
  "expected_claim_types": [
    "cleanroom_behavior_inference",
    "runtime_behavior",
    "absence_claim"
  ],
  "required_evidence": [
    "help_text",
    "task_docs",
    "probe_logs",
    "generated_outputs",
    "filesystem_side_effect_diffs",
    "negative_witness"
  ],
  "preferred_axes": [
    "command_ontology",
    "input_class",
    "output_class",
    "error_class",
    "side_effect",
    "probe_template",
    "config_precedence",
    "parser_precedence"
  ],
  "allowed_stores": [
    "task_docs",
    "help_output",
    "programbench_probe",
    "generated_outputs",
    "filesystem_side_effect_diffs",
    "local_probe_logs"
  ],
  "forbidden_stores": [
    "hidden_evaluator_tests",
    "original_source_repo",
    "internet_search",
    "task_external_code_repositories"
  ],
  "noise_budget": "medium",
  "recall_precision_posture": "recall_biased"
}
```

### 15.4 Broker expansion

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

Example concept boundaries:

```text
config_file
  distinct from:
    default_config
    environment_variable
    CLI_flag_override
    runtime_state
    generated_output_artifact

output_artifact
  distinct from:
    config input
    log output
    stdout text
    temporary runtime state
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

config_precedence
  evidence_surface -> task docs
  evidence_surface -> help output
  test_witness_template -> config_plus_env_plus_cli_probe

environment_variable
  test_witness_template -> env_only_probe
  test_witness_template -> env_plus_config_probe

error_class
  test_witness_template -> invalid_flag_probe
  test_witness_template -> missing_file_probe
  test_witness_template -> malformed_config_probe

output_artifact
  evidence_surface -> generated_outputs
  test_witness_template -> file_tree_diff_probe
```

### 15.5 Store queries

The broker may query or generate:

```text
README/task docs
--help output, if allowed
executable probes
local probe logs
generated outputs
filesystem before/after diffs
worker-authored local tests
candidate source AST only after worker writes candidate source
```

The broker must not query:

```text
hidden evaluator tests
original source repo
online issues/docs
internet search
external package source
host secrets
Docker socket
task-external code repositories
```

### 15.6 Coverage report

Example report excerpt:

```text
coverage_status: open_with_gaps

O coverage:
- commands: found
- subcommands: partial
- flags: found
- config file: found
- environment variables: checked_no_witness only for env probes run
- defaults: partial
- precedence: unresolved
- errors: partial
- output artifacts: found
- side effects: unresolved

Boundary coverage:
- config_file boundary: complete enough for probes
- generated_output_artifact boundary: complete enough for file-diff probes
- parser_precedence boundary: incomplete

E coverage:
- help text witness found
- task docs witness found
- valid invocation probe found
- generated output witness found
- no negative probe for malformed config
- no witness for env override precedence

D constraints:
- hidden tests are forbidden inference evidence
- original source repo is forbidden inference evidence
- no precedence claim allowed without docs/help/probe witness
- no absence claim allowed unless checked_no_witness slot plus manifest exists

U outcome:
- enough evidence for first ProgramODEUProfile draft
- not enough evidence for implementation parity claim
```

### 15.7 Worker result

The worker builds `ProgramODEUProfile` only from covered slots.

It marks unresolved slots explicitly:

```text
config precedence
malformed config error class
environment variable override
parser precedence
file side effects under failure
```

Unresolved behavior slots must trigger probes or remain marked unknown.

No implementation should begin if the O-entity inventory and boundary definitions are too weak to distinguish:

```text
input artifact vs output artifact
config file vs default config
environment variable vs CLI flag override
stdout output vs generated file
error class vs generic failure
```

---

## 16. ADEU repo-search example

### 16.1 Intent

Task: find where runtime model/provider selection is persisted.

The worker should not merely search `provider`. It should request conceptual expansion under a persistence-oriented task profile.

```json
{
  "schema": "RetrievalIntent@1",
  "intent_id": "intent.adeu.runtime_provider_persistence",
  "retrieval_task_profile_ref": "profile.repo_persistence_search",
  "objective": "Find where runtime model/provider selection is persisted.",
  "why": "A provider-selection change must update correct runtime, config, persistence, and UI surfaces.",
  "seed_terms": [
    "runtime provider selection",
    "model selection",
    "provider choice",
    "persist provider"
  ],
  "desired_odeu_lanes": ["O", "E"],
  "expected_claim_types": [
    "implementation_location",
    "persistence_substrate",
    "absence_or_unwitnessed_gap"
  ],
  "required_evidence": [
    "implementation_surface",
    "storage_schema_witness",
    "storage_write_witness",
    "storage_read_witness",
    "checked_no_witness"
  ],
  "preferred_axes": [
    "alias",
    "storage_substrate",
    "write_path",
    "read_path",
    "fallback/default",
    "tests_fixtures"
  ],
  "forbidden_axes": ["deontic_law"],
  "allowed_stores": ["repo_grep", "schema_json", "docs", "tests"],
  "noise_budget": "medium"
}
```

### 16.2 Concept boundary posture

Relevant confusables:

```text
provider_choice
model_selection
runtime_profile
capability_model
policy_profile
frontend_local_state
persisted_preference
worker_run_provider_field
```

The broker must not collapse these into one concept.

Examples:

```text
Frontend useState provider value
  -> UI local state candidate
  -> not persisted preference witness

worker_run.provider SQLite field
  -> run-history persistence witness
  -> not global user preference witness

policy profile field
  -> policy/profile substrate candidate
  -> not provider choice unless read path links it

capability probe model/version
  -> capability evidence surface
  -> not provider choice unless selection logic links it
```

### 16.3 Canonical expansion

Root:

```text
runtime_selection
```

Selected expansion:

```text
runtime_selection
  alias -> provider_choice
  alias -> model_selection, marked ambiguous / boundary-sensitive
  alias -> profile_selection
  storage_substrate -> SQLite worker run
  storage_substrate -> SQLite copilot session
  storage_substrate -> environment config
  storage_substrate -> policy profile
  implementation_surface -> ProviderKind
  implementation_surface -> proposer backend
  implementation_surface -> Codex worker runtime
  implementation_surface -> frontend provider state
  protocol_action_surface -> propose endpoint
  protocol_action_surface -> worker run request
  failure_mode -> unsupported provider
  failure_mode -> fallback/default provider
```

Profile subaxes:

```text
write_path
  expected witness:
    storage_write_witness

read_path
  expected witness:
    storage_read_witness

fallback/default
  expected witness:
    default_value_or_fallback_witness
```

### 16.4 Evidence candidates from targeted repo pass

This remains a bounded example, not a whole-repo proof.

| Slot                          | Observed candidate                                                                                                                                                                                                                                                                                | Candidate kind                                                |
| ----------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------- |
| Provider enum                 | `ProviderKind = Literal["mock", "openai", "codex"]` in `apps/api/src/adeu_api/main.py:403-415`.                                                                                                                                                                                                   | implementation surface                                        |
| Provider parity               | API validates provider support per frozen surface matrix in `apps/api/src/adeu_api/main.py:417-424` and `:766-805`.                                                                                                                                                                               | implementation / failure-mode candidate                       |
| API request defaults          | proposal request models default provider to `"mock"` in `apps/api/src/adeu_api/main.py:1045-1062`.                                                                                                                                                                                                | fallback/default candidate                                    |
| External proposer selection   | `_select_external_proposer` dispatches `openai` and `codex`, otherwise errors for unsupported external proposer in `apps/api/src/adeu_api/main.py:5890-5898`; `/propose` then uses selected external proposer in `:5901-5938`.                                                                    | implementation surface                                        |
| Worker runtime provider       | URM worker execution only admits `request.provider == "codex"` and rejects others in `packages/urm_runtime/src/urm_runtime/worker.py:301-307`.                                                                                                                                                    | implementation / failure-mode witness                         |
| Worker run persistence        | Worker start persists `request.provider` through `persist_worker_run_start` in `packages/urm_runtime/src/urm_runtime/worker.py:381-392`.                                                                                                                                                          | storage write path                                            |
| SQLite worker provider column | `urm_worker_run` includes `provider TEXT NOT NULL` in `packages/urm_runtime/src/urm_runtime/storage.py:282-301`.                                                                                                                                                                                  | storage schema witness                                        |
| SQLite worker provider insert | `persist_worker_run_start` inserts `provider` into `urm_worker_run` in `packages/urm_runtime/src/urm_runtime/storage.py:595-642`.                                                                                                                                                                 | storage write witness                                         |
| Copilot session persistence   | `urm_copilot_session` stores `codex_version`, `capability_probe_id`, `profile_id`, `profile_version`, and `profile_policy_hash` in `packages/urm_runtime/src/urm_runtime/storage.py:241-263` and `:1059-1093`.                                                                                    | storage substrate witness for session/profile/capability data |
| Capability probe              | `urm_codex_capability_probe` stores Codex version/capability probe JSON in `packages/urm_runtime/src/urm_runtime/storage.py:230-238`.                                                                                                                                                             | capability evidence surface                                   |
| Runtime config                | DB/evidence/Codex binary locations come from environment-backed config in `packages/urm_runtime/src/urm_runtime/config.py:54-65` and `:93-139`.                                                                                                                                                   | config substrate                                              |
| Policy profile substrate      | Policy profiles `default`, `experimental`, and `safe_mode` are declared in `policy/profiles.v1.json:1-31`.                                                                                                                                                                                        | profile substrate                                             |
| Frontend provider selection   | Inspected app pages use React `useState<"mock" \| "openai" \| "codex">("mock")` and buttons calling `setProvider(...)`; examples in `apps/web/src/app/page.tsx:288` and `:505-515`, `apps/web/src/app/papers/page.tsx:101` and `:551-571`, `apps/web/src/app/puzzles/page.tsx:85` and `:181-192`. | UI selection candidate, not persistence witness               |

### 16.5 Example coverage report

```text
coverage_status: open_with_gaps

closed relative to:
- roots: runtime_selection, provider_choice, persistence_substrate
- boundaries:
    provider_choice: boundary_complete
    persisted_preference: boundary_complete
    runtime_selection: boundary_incomplete
- axes: alias, storage_substrate, write_path, read_path, fallback/default
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
- read path proving a persisted preference determines later provider selection
- IPC/update path for changing provider selection after runtime start
- shell-level provider preference
- whether provider parity matrix is treated only as repo fixture/package resource or as mutable config
- tests proving fallback/default behavior
- git history evidence for prior provider persistence changes

invalid absence claims under this report:
- "The repo has no persistent provider preference anywhere."
- "Frontend provider state is not persisted anywhere."
- "No read path exists for provider preference."

bounded worker-safe conclusion:
- targeted evidence found provider choice as request-level API state.
- targeted evidence found worker-run provider recorded in SQLite.
- targeted evidence found Codex session/profile/capability state persisted separately.
- targeted frontend evidence shows local UI provider selection state.
- persistent frontend/user preference remains unwitnessed under this bounded pass.
```

### 16.6 Example claim/evidence bindings

```text
Claim:
  Provider choice is recorded for URM worker runs.

Claim type:
  persistence_substrate

Evidence:
  worker_run.provider schema witness
  persist_worker_run_start write witness

Support:
  witness_support

Limitations:
  does not establish global persisted user preference
  does not establish frontend persistence
  does not establish provider preference read path
```

```text
Claim:
  Persistent frontend/user provider preference remains unwitnessed under this bounded pass.

Claim type:
  absence_or_unwitnessed_gap

Evidence:
  coverage report unresolved slots
  targeted frontend local state candidates

Support:
  candidate_support for unwitnessed gap, not bounded_absence_support

Limitations:
  not a repository-wide absence claim
  no complete frontend runtime/browser storage manifest
  git history and full tests not searched
```

Forbidden stronger conclusion:

```text
The repo has no persistent provider preference anywhere.
```

That would require checked-no-witness coverage over UI, API, runtime config, storage, tests, git history, and possibly environment/shell integration.

---

## 17. Failure modes and mitigations

### 17.1 Bad canonical relations

**Failure:** `model_selection` is globally aliased to `provider_choice`, but in some tasks it means capability model selection.

**Mitigation:** domain-scoped aliases, concept boundaries, ambiguity records, conflict refs, regression tests, deprecation path.

### 17.2 Bad concept boundary

**Failure:** `persisted_preference` includes any stored historical field, so worker-run history is mistaken for user preference.

**Mitigation:** `ConceptBoundary@1`, negative examples, distinguishing questions, boundary regression fixtures.

### 17.3 Over-expansion / noise

**Failure:** genus and sibling expansion pull in broad irrelevant concepts.

**Mitigation:** relation allowlists, depth limits, Slice 0 restricted kernel, drift-risk scoring, branch caps, lexical-noise warnings.

### 17.4 Under-expansion / missed concept

**Failure:** worker selects only `alias`, missing `storage_substrate`, `write_path`, or `read_path`.

**Mitigation:** task-profile defaults, required high-value axes, coverage report excluded-axis listing, auditor rejection for unsupported claim types.

### 17.5 Axis selection becomes vibes one level up

**Failure:** worker chooses axes based on prompt intuition rather than task needs.

**Mitigation:** `RetrievalTaskProfile@1` supplies defaults and required axes; overrides are explicit and auditable.

### 17.6 Stale repo path hints

**Failure:** canonical DB path hint points to old source file.

**Mitigation:** path hints are not truth; adapter marks `stale_hint`; patch proposal updates hint with evidence.

### 17.7 Model selects wrong axis

**Failure:** worker selects `deontic_law` when it needs implementation surfaces.

**Mitigation:** objective/axis mismatch warning; task profile recommends axes; auditor checks claim support.

### 17.8 Model over-trusts returned evidence

**Failure:** worker treats candidate chunk as proof.

**Mitigation:** candidate kind, admissibility status, `ClaimEvidenceBinding@1`, and auditor verdict are mandatory for claims.

### 17.9 Broker treats lexical hit as semantic witness

**Failure:** term match becomes evidence.

**Mitigation:** lexical match is a separate candidate kind; witness classification requires stronger criteria.

### 17.10 Absence claim from weak search

**Failure:** “grep found nothing” becomes “nothing exists.”

**Mitigation:** `StoreCoverageManifest@1`; absence claims require checked-no-witness, relevant branches, no clipping, and enabled adapters.

### 17.11 Canonical DB ossifies wrong ontology

**Failure:** early concept splits become institutional.

**Mitigation:** candidate/stabilized distinction, boundary lifecycle, conflict records, split/merge proposals, regression tests.

### 17.12 Evidence store misses relevant item

**Failure:** grep misses symbol semantics; vector misses exact fields; AST adapter disabled.

**Mitigation:** coverage report lists stores searched and unsearched; absence claims require checked-no-witness over selected relevant stores.

### 17.13 Hidden dependency across concepts not represented

**Failure:** provider persistence depends on profile policy, but DB lacks relation.

**Mitigation:** unresolved slot visible; worker proposes relation with evidence-backed patch.

### 17.14 Authority laundering

**Failure:** advisory prose retrieved as normative law.

**Mitigation:** authority-layer filters; ANM/D@1 integration; advisory candidates cannot satisfy D-lane claims.

### 17.15 ProgramBench cleanroom violation

**Failure:** worker uses hidden evaluator tests, original source repo, internet search, or external source lookup during inference.

**Mitigation:** cleanroom profile store denylist; forbidden evidence classification; auditor rejection.

### 17.16 Vector drift

**Failure:** vector results bypass typed relation graph.

**Mitigation:** vector adapter must attach results to existing `QueryBranch@1`; vector results cannot create untyped expansion.

### 17.17 Budget clipping hides missing evidence

**Failure:** branch clipped after max hits; worker assumes coverage complete.

**Mitigation:** clipping changes coverage status; clipped branches cannot support absence claims.

### 17.18 Bad worker query after broker report

**Failure:** worker performs additional freeform search and blends it into broker-covered evidence.

**Mitigation:** worker may use extra search only as `outside_plan_advisory` or must request a new plan branch.

### 17.19 Adapter over-classification

**Failure:** adapter emits `witness_candidate` based on shallow heuristics.

**Mitigation:** admissibility status remains separate from candidate kind; auditor review is required for claim support.

### 17.20 Canonical DB becomes too conservative

**Failure:** relations are so hard to promote that workers revert to vibe-search.

**Mitigation:** allow low-authority `candidate` relation proposals in explicit experimental plans while excluding them from default stabilized retrieval.

### 17.21 Domain packs fragment too far

**Failure:** every domain pack creates slightly different concepts, preventing reuse.

**Mitigation:** shared concept IDs plus domain-scoped relation overlays; conflict review before split/merge promotion.

---

## 18. Minimal implementation slices

### Slice 0 — Static concept DB seed + CLI broker over repo grep

Smallest useful slice.

Add:

```text
hand-authored CanonicalConceptRecord@1
hand-authored ConceptBoundary@1 for used concepts, or boundary_incomplete flag
hand-authored ConceptRelation@1
one domain pack: adeu_repo
one or two RetrievalTaskProfile@1 records
one adapter: repo_grep
deterministic expansion
QueryBranch@1
StoreQueryRealization@1 for repo_grep
basic EvidenceCandidate@1
basic StoreCoverageManifest@1
basic EvidenceCoverageReport@1
```

Slice 0 default relation kernel:

```text
alias
implementation_surface
evidence_surface
storage_substrate
test_witness_template
failure_mode
```

Gated / high-risk until later slices or explicit opt-in:

```text
genus
species
sibling
part_whole
deontic_law
utility_axis
domain_specific_edge_class
```

Reason:

```text
The biggest early drift risks come from over-broad genus/sibling expansion
and premature D-lane expansion.
```

Acceptance target: same intent/options produce same branch list, grep realizations, evidence candidates, and coverage report.

### Slice 1 — First-class plan, realization, and coverage artifacts

Add:

```text
ConceptualSearchPlan@1
QueryBranch@1
StoreQueryRealization@1
EvidenceCandidate@1
StoreCoverageManifest@1
EvidenceCoverageReport@1
plan/realization/manifest/report hashes
relation path preservation
lexical vs witness distinction
checked-no-witness discipline
```

Acceptance target: worker can cite only evidence candidates linked to branches and store realizations.

### Slice 2 — Claim/evidence binding and profile gates

Add:

```text
ClaimEvidenceBinding@1
claim type enum
admissibility rule refs
RetrievalTaskProfile@1 enforcement
excluded high-value axes in coverage report
auditor rejection hooks
```

Acceptance target: factual claims require claim/evidence bindings.

### Slice 3 — Confidence, provenance, boundaries, and drift controls

Add:

```text
confidence tiers
provenance refs
boundary lifecycle
domain profiles
drift score
excluded axes
budget clipping records
stale hint warnings
boundary-incomplete warnings
```

Acceptance target: high-risk expansions warn or clip deterministically.

### Slice 4 — Additional adapters

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

### Slice 5 — Worker / broker / auditor loop

Integrate with agent harness:

```text
worker emits RetrievalIntent@1
broker emits plan/report
worker answer binds claims to evidence candidates
auditor checks support
unresolved slots can trigger another expansion
```

Acceptance target: worker cannot silently cite unexpanded concepts or raw candidates.

### Slice 6 — ProgramBench cleanroom adapter

Add behavior-recovery domain pack and cleanroom profile:

```text
CLI/help adapter
programbench_probe adapter
probe log adapter
generated output adapter
filesystem side-effect diff adapter
ProgramODEUProfile handoff
forbidden store enforcement
```

Acceptance target: profile distinguishes cleanroom-visible evidence, worker-generated evidence, evaluation-only evidence, and forbidden evidence.

### Slice 7 — Canonical DB patch proposal workflow

Add:

```text
ConceptDBPatchProposal@1
boundary patch proposals
reviewer decision records
confidence promotion
deprecation
conflict handling
retrieval regression fixtures
```

Acceptance target: concept, boundary, and relation changes require provenance and review.

---

## 19. Acceptance criteria

### 19.1 Deterministic expansion

Given the same:

```text
concept DB hash
concept boundary hashes
retrieval task profile
intent
selected axes
depth
confidence threshold
domain profile
source set
broker version
```

the broker emits the same `ConceptualSearchPlan@1`.

### 19.2 Concept boundaries are present or warned

Every canonical concept used in a plan has either:

```text
ConceptBoundary@1
```

or:

```text
boundary_status: boundary_incomplete
DriftWarning@1: boundary_incomplete
```

Boundary-incomplete concepts reduce claim strength unless resolved by admissible evidence and auditor review.

### 19.3 Query plan preserves relation types

Every branch records:

```text
root concept
expanded concept
relation path
relation types
profile subaxis, if applicable
expected evidence surface
expected witness kind
branch hash
```

No branch is just an unexplained query string.

### 19.4 Store-specific query realization is explicit

Every store query records:

```text
branch ref
store adapter
canonical terms
generated terms
normalization rules
query syntax
expected result shape
limitations
realization hash
```

### 19.5 Coverage report lists searched and unsearched slots

The report lists:

```text
searched concept slots
unsearched concept slots
searched stores
unsearched stores
store coverage manifests
excluded axes
excluded high-value axes
skipped branches
unresolved terms
ambiguous terms
boundary-incomplete concepts
empty witness slots
checked-no-witness slots
budget clipping
adapter failures
```

### 19.6 Worker cannot silently use unexpanded vibes

Any factual worker claim must bind to one of:

```text
ClaimEvidenceBinding@1
explicit inference/advisory status
outside-plan marker
```

Unexpanded concepts cannot be cited as covered.

### 19.7 Claim/evidence bindings are required

Every factual, implementation, persistence, runtime, normative, cleanroom, or absence claim records:

```text
claim type
evidence candidate refs
support relation
admissibility rule ref
admissibility status
support strength
coverage report ref
limitations
auditor verdict, when required
```

### 19.8 Concept relation and boundary changes require provenance

Adding, removing, promoting, deprecating, merging, or splitting concepts, boundaries, aliases, or relations requires:

```text
patch proposal
evidence refs or rationale
claim/evidence binding refs where applicable
review status
DB version change
regression impact note for stabilized records
```

### 19.9 Retrieval distinguishes lexical match from witness

Results must distinguish:

```text
lexical_match
structural_match
implementation_surface_candidate
witness_candidate
checked_no_witness
inadmissible
forbidden_evidence
```

A lexical hit alone cannot satisfy a witness requirement.

### 19.10 Checked-no-witness requires coverage manifest

A `checked_no_witness` claim requires:

```text
StoreCoverageManifest@1
source_set_hash
included/excluded globs
normalization rules
case sensitivity
no relevant clipping
no failed required branches
no unsearched required branches
relevant adapters enabled
```

### 19.11 Drift warnings trigger

Warnings trigger when:

```text
expansion crosses domain packs
concept boundary is incomplete
concept boundary is conflicted
low-confidence relations are included
branch count exceeds budget
hit volume exceeds noise threshold
relation depth approaches limit
model supplies uncanonical terms
profile-required axes are excluded
vector adapter returns untyped similarity
authority boundary risk appears
cleanroom boundary risk appears
```

### 19.12 Bounded exhaustiveness statement exists

Every coverage report must say what it is closed over and what it is not closed over.

### 19.13 Authority boundaries are respected

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

### 19.14 ProgramBench cleanroom profile blocks forbidden evidence

The ProgramBench cleanroom profile must block:

```text
hidden evaluator tests
original source repo
internet search
online repo/docs/issues
external package/source lookup
host secrets
Docker socket
task-external code repositories
```

Forbidden evidence cannot support inference claims.

### 19.15 Adapter failure is visible

If an adapter fails, is disabled, or is outside scope, the report states that fact. The worker cannot make absence claims over that store.

### 19.16 Slice 0 cannot use high-risk relation types by default

Slice 0 default relation kernel is limited to:

```text
alias
implementation_surface
evidence_surface
storage_substrate
test_witness_template
failure_mode
```

High-risk relation types require explicit opt-in and drift warning.

### 19.17 Query branches are reproducible

A reviewer can rerun the same plan against the same source set and reproduce:

```text
query branches
store realizations
query terms
branch order
searched stores
budget clipping
coverage status
```

### 19.18 Lexical outside-plan search is quarantined

If the worker performs extra search outside the broker plan, those results are marked:

```text
outside_plan_advisory
```

They cannot satisfy broker-covered evidence slots unless a new branch is admitted.

---

## 20. Non-goals

This v0.1 architecture does not attempt to:

```text
build a universal ontology
prove the canonical DB metaphysically complete
replace all search systems
replace vector retrieval
automate normative authority promotion
make advisory prose authoritative
make hidden tests ProgramBench inference evidence
implement ProgramBench itself
implement repo-wide semantic indexing in the first slice
activate all relation types in Slice 0
let the broker silently mutate the concept DB
convert LLM prompt behavior into institutional authority by naming it a broker
treat retrieved chunks as proof without admissibility review
treat checked-no-witness as grep-found-nothing
solve all long-context failures
remove worker judgment
remove auditor review
```

The broker narrows and audits retrieval. It does not eliminate reasoning.

---

## 21. Open questions

1. **Package boundary:** should this become a new `packages/adeu_conceptual_retrieval` package, or live under an existing harness / core IR lineage?

2. **Authority posture:** should concept DB seed files be support-level, architecture-level, or ANM-native governed artifacts once stabilized?

3. **Concept DB source format:** JSON only, `.adeu.md` source plus derived JSON, or hybrid?

4. **Boundary authoring:** who writes and reviews `ConceptBoundary@1` records for promoted concepts?

5. **Boundary sufficiency:** what minimum positive/negative examples and confusables are required before a boundary is `boundary_complete`?

6. **Task profile publication:** who can publish or alter `RetrievalTaskProfile@1` defaults?

7. **ANM integration:** for D-lane retrieval, should the broker consume compiled ANM artifacts instead of raw markdown?

8. **Domain pack governance:** who can publish or promote a domain pack?

9. **Confidence promotion rule:** what exact evidence is required for `seeded -> evidence_backed -> stabilized`?

10. **Auditor implementation:** deterministic policy first, human review first, model-assisted review, or mixed?

11. **Vector adapter boundary:** how should vector recall be admitted without bypassing typed relation paths?

12. **ProgramBench witness sufficiency:** which cleanroom-visible probes count as adequate behavioral witnesses?

13. **ProgramBench cleanroom enforcement:** how should forbidden stores be detected and blocked in practice?

14. **Regression corpus:** which ADEU repo-search tasks become golden retrieval fixtures?

15. **Operator projection:** what minimal UI exposes concept boundaries, confusables, coverage gaps, and claim/evidence bindings without implying ratification?

16. **External evidence stores:** which external tools are allowed, and how are their outputs hashed, bounded, cleanroom-scoped, and authority-scoped?

Recommended next move: define the v0.1 schema family and a hand-authored `adeu_repo` concept seed with `ConceptBoundary@1` records, then test it against two fixtures: runtime provider persistence retrieval and one ANM/D@1 normative retrieval task.
