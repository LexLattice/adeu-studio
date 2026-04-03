I grounded this against the current repo surfaces, especially:

* `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`
* `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`
* `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`
* `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py`
* `packages/adeu_agent_harness/tests/fixtures/v48a/reference_taskpack_binding_spec.json`
* `packages/adeu_agent_harness/tests/fixtures/v48a/reference_anm_taskpack_binding_profile.json`
* `packages/adeu_commitments_ir/tests/fixtures/v47e/reference_anm_policy_consumer_binding_profile.json`
* `apps/api/fixtures/repo_description/vnext_plus105/repo_descriptive_normative_binding_frame_v105_reference.json`

I also drafted a small external prototype bundle and sample artifacts here:

* [prototype bundle](sandbox:/mnt/data/adeu_semantic_forms_v0_bundle.zip)
* [sample parse profile](sandbox:/mnt/data/adeu_semantic_forms_v0/samples/sample_semantic_parse_profile.json)
* [sample parse result](sandbox:/mnt/data/adeu_semantic_forms_v0/samples/sample_semantic_parse_result.json)
* [sample ambiguous parse result](sandbox:/mnt/data/adeu_semantic_forms_v0/samples/sample_semantic_parse_result_ambiguous.json)
* [sample transform result](sandbox:/mnt/data/adeu_semantic_forms_v0/samples/sample_semantic_transform_result.json)

## 1. Module / family framing

The missing layer after the released `V45` + `V47` + `V48` stack is not another policy compiler and not another execution boundary. It is a **bounded semantic intent layer** that can sit between loose user/operator language and the already-released formal ADEU artifact families.

Today the repo already has:

* `V45`: released descriptive scope surfaces and descriptive-to-normative binding frame.
* `V47`: authoritative policy source via ANM / `D@1`, normalized `d1_normalized_ir@1`, consumer doctrine, facts/results/ledger.
* `V48`: policy+scope binding into `anm_taskpack_binding_profile@1`, then `compiled_policy_taskpack_binding@1`, then worker execution envelope / provenance / topology.

What is still missing is a canonical object for statements like:

> “Prepare a read-only taskpack seed over the released symbol catalog under the owner policy, with default codex worker, allow only these paths, forbid network.”

Right now that intent is either:

* loose natural language, or
* already-lowered formal payloads like `reference_taskpack_binding_spec.json`, or
* free-text fields inside formal payloads like `task_scope_summary`.

That is the gap.

So the new family I would propose is:

**`adeu_semantic_forms`**
A bounded canonical semantic language layer for **intent statements**, not normative policy source.

This family is ADEU-native because it gives:

* **O**: typed semantic clauses, released anchor handles, target artifact seeds
* **E**: matched aliases, recovered refs, ambiguity sets, provenance of recovery
* **D**: equivalence law, canonicalization law, hash law, transform law, reject law
* **U**: paraphrase collapse, stable semantic identity, deterministic downstream transforms, fewer hidden intent drifts

The critical distinction is:

* `NL -> ADEU` is **semantic recovery**
* `ADEU -> ADEU` is **governed transformation**

The first is fallible and ambiguity-bearing.
The second is deterministic once the source ADEU form is fixed.

That separation is non-negotiable.

## 2. Chosen bounded v0 scope

### Chosen language

Python package + JSON artifacts.

### Chosen starter domain

**`repo_policy_work`**

This is a tiny domain for statements that mean:

* bind one released repo scope anchor
* bind one released policy anchor
* keep the work read-only
* use one fixed worker kind
* optionally add allow/forbid boundary constraints
* emit a typed seed for later `V48`-adjacent compilation

### Real bounded repo slice used for grounding

I would bind v0 to the existing released/fixture surfaces that already sit on the `V45 -> V47 -> V48A` seam:

* `packages/adeu_agent_harness/tests/fixtures/v48a/reference_taskpack_binding_spec.json`
* `packages/adeu_agent_harness/tests/fixtures/v48a/reference_anm_taskpack_binding_profile.json`
* `packages/adeu_commitments_ir/tests/fixtures/v47e/reference_anm_policy_consumer_binding_profile.json`
* `apps/api/fixtures/repo_description/vnext_plus101/repo_symbol_catalog_v101_reference.json`
* `apps/api/fixtures/repo_description/vnext_plus105/repo_descriptive_normative_binding_frame_v105_reference.json`

### Included in v0

Exactly this semantic surface:

* one scope anchor
* one policy anchor
* one worker anchor
* one mutation posture, frozen to `read_only`
* one deliverable kind, frozen to `taskpack_binding_spec_seed`
* zero or more `allow_path`
* zero or more `forbid_path`
* zero or more `forbid_effect`

### Excluded in v0

Intentionally excluded:

* general semantic language
* deontic policy authoring, because `D@1` already owns that
* multi-policy or multi-scope joins
* temporal or conditional logic
* open-ended boolean composition
* utility tradeoff language
* command/evidence-slot recovery from loose NL
* write/mutate/execute claims
* benchmark consumer world
* runtime event world
* multi-worker topology requests
* auto-approval or execution entitlement claims

### Why this is the right v0 cut

Because it is exactly adjacent to a released stack boundary that already exists in the repo:

* `anm.py` already handles authoritative normative source syntax.
* `anm_models.py` already defines policy-normalized artifacts.
* `taskpack_binding.py` already builds a typed binding profile from a structured spec.
* What does **not** exist is the canonical semantic object above that spec.

So v0 should not try to solve “semantics in general.” It should solve:

> “How do we canonicalize a bounded repo-work intent into a stable semantic object that can then deterministically lower into a `V48`-adjacent seed?”

## 3. Worked architecture

### End-to-end pipeline

1. **Load a frozen semantic parse profile**
   This is authoritative for:

   * released anchor vocabulary
   * alias tables
   * supported relations
   * unsupported patterns
   * snapshot identity
   * equivalence universe

2. **`NL -> ADEU` semantic recovery**
   Parse loose text into one of:

   * `resolved_singleton`
   * `typed_alternatives`
   * `clarification_required`
   * `rejected_unsupported`

3. **Materialize `adeu_semantic_normal_form@1` candidate(s)**
   Each candidate is a canonical clause set.

4. **Canonicalize and hash**
   Only now does a semantic hash become meaningful.

5. **Apply an explicit transform contract**
   `adeu_semantic_normal_form@1 -> adeu_taskpack_binding_spec_seed@1`

6. **Resolve released anchors to released refs**
   Deterministically, through the parse profile.

7. **Emit transform result**
   Either:

   * `transformed`, with target payload and target hash
   * or explicit blocked status with reason codes

8. **Optional downstream bridge**
   A later deterministic pass can take the seed plus additional structured overlays and build the full `anm_taskpack_binding_profile@1` through existing harness code.

### A. Smallest useful ADEU sentence calculus for v0

The smallest useful atomic unit is a **typed semantic clause**.

I would freeze v0 to this clause shape:

```json
{
  "relation_kind": "bind_scope_anchor",
  "lane_tag": "scope",
  "object_kind": "scope_anchor",
  "object_value": "repo_symbol_catalog"
}
```

The clause set is the semantic sentence.

Supported `relation_kind` values in v0:

* `bind_scope_anchor`
* `bind_policy_anchor`
* `use_worker_subject`
* `set_mutation_posture`
* `allow_path`
* `forbid_path`
* `forbid_effect`
* `produce_artifact_kind`

Frozen lane tags:

* `scope`
* `policy`
* `worker`
* `mutation`
* `constraint`
* `deliverable`

This is a **clause-set calculus**, not a universal grammar.

It is enough to say:

* which released scope the work is about
* which released policy anchor constrains it
* which worker kind it assumes
* whether mutation is allowed
* which boundary constraints exist
* what typed target artifact seed should be emitted

### B. Canonicalization and equivalence

Semantic equivalence in v0 is **profile-relative**.

Two recovered statements count as the same canonical semantic object iff, under the same `parse_profile_id`:

* they produce the same normalized clause multiset
* clause order differences are normalized away
* duplicate identical clauses are deduped
* alias wording is normalized away
* input prose is not part of the semantic hash subject

Normalized away:

* word order in the source sentence
* punctuation and case
* alias variation like `read-only` vs `no writeback`
* alias variation like `release_surface:owner` vs `owner policy`
* repeated mention of identical constraints

Not normalized away:

* different scope anchors
* different policy anchors
* different mutation posture
* different allow/forbid path sets
* different forbidden effects
* different deliverable kind

Ambiguity is not collapsed away.
If “catalog” matches both `repo_symbol_catalog` and `repo_entity_catalog`, v0 emits typed alternatives.

### C. Semantic identity and hashing

Hashing is meaningful only after canonicalization.

What gets hashed:

* **Not semantic identity**: raw NL string
* **Semantic identity**: canonical normal form
* **Transform identity**: canonical target payload under a transform contract

Canonical hash subject for the normal form:

```python
basis = {
    "schema": "adeu_semantic_normal_form@1",
    "profile_id": profile_id,
    "domain_kind": "repo_policy_work",
    "clauses": [
        {"relation_kind": "...", "object_value": "..."},
        ...
    ],
}
semantic_hash = sha256_canonical_json(basis)
```

So the hash asserts only this:

> Under parse profile `P`, this exact canonical clause set is the semantic object.

It does **not** assert universal semantic truth.

### D. Separation of the two work surfaces

This v0 should be architected as two separate modules.

#### Surface 1: `NL -> ADEU`

`adeu_semantic_forms.nl_recovery`

Responsibilities:

* alias matching
* anchor recovery
* clause recovery
* ambiguity typing
* unsupported construct rejection

This surface is fallible.

#### Surface 2: `ADEU -> ADEU`

`adeu_semantic_forms.transforms.taskpack_binding_seed`

Responsibilities:

* singleton cardinality checks
* anchor resolution
* default field insertion
* deterministic target payload construction
* target hashing

This surface is deterministic once the source normal form is fixed.

The current repo already embodies this general split elsewhere:

* `adeu_semantic_source/anm.py` recovers authoritative policy syntax from fenced `D@1`
* `adeu_agent_harness/taskpack_binding.py` deterministically lowers structured binding input into `AnmTaskpackBindingProfile`

The new family should preserve that pattern, not blur it.

### E. Ambiguity posture

v0 should have exactly four parse outcomes:

* `resolved_singleton`
* `typed_alternatives`
* `clarification_required`
* `rejected_unsupported`

#### True paraphrase collapse

Different source texts collapse if they yield the same normal form hash.

#### Typed alternatives

When multiple released anchors tie, return multiple candidates.

Example:
“prepare a read-only binding seed for the catalog under the owner rule”
can legitimately produce:

* candidate A: `repo_entity_catalog`
* candidate B: `repo_symbol_catalog`

#### Clarification-required

Use when required anchors are absent.

Example:
“prepare a read-only binding seed”
has no scope anchor and no policy anchor.

#### Unsupported

Use when the request asks for constructs outside v0.

Examples:

* “pick whatever policy seems closest”
* “modify the repo if needed”
* “if policy A fails, then try policy B”
* “compare all catalogs and choose the best one”

### G. One real bounded starter domain

The starter domain is:

**policy-bound repo work statements over released `V45` / `V47` / `V48A` surfaces**

That means:

* scope anchors resolve to released descriptive scope surfaces
* policy anchors resolve to released policy source / consumer doctrine anchors
* output lowers into a `V48A`-adjacent binding seed

This is not domain-free metalanguage.
It is tightly coupled to the actual released stack.

### H. One concrete first benchmark / experiment

I would create:

**`repo_policy_work_v0.reference_v48a` paraphrase benchmark**

The benchmark fixture contains three buckets:

1. paraphrase group expected to collapse to one normal form hash
2. ambiguous cases expected to emit typed alternatives
3. unsupported cases expected to reject

And it measures:

* paraphrase collapse determinism
* ambiguity classification determinism
* semantic hash stability
* transform determinism into `adeu_taskpack_binding_spec_seed@1`

The prototype bundle includes a draft benchmark seed:
[benchmark cases](sandbox:/mnt/data/adeu_semantic_forms_v0/samples/benchmark_cases.json)

## 4. Authoritative artifact family

### `adeu_semantic_parse_profile@1`

**Purpose**
Authoritative recovery vocabulary and released anchor universe.

**Authority posture**
Authoritative for what counts as a valid recovery space in a bounded domain.
Not authoritative for natural-language truth.

**Key fields**

* `profile_id`
* `domain_kind`
* `snapshot_id`
* `snapshot_sha256`
* `scope_anchors[]`
* `policy_anchors[]`
* `worker_anchors[]`
* `mutation_lexicon[]`
* `artifact_kind_lexicon[]`
* `effect_lexicon[]`
* `unsupported_patterns[]`
* `semantic_hash`

**Stop-gate role**
All semantic identity is profile-relative. Change the profile, and hash identity may change.

### `adeu_semantic_parse_result@1`

**Purpose**
Canonical record of the `NL -> ADEU` recovery outcome.

**Authority posture**
Authoritative for what the parser recovered and how it classified ambiguity.
Not authoritative for semantic correctness.

**Key fields**

* `parse_result_id`
* `profile_id`
* `input_kind`
* `input_text`
* `input_text_hash`
* `parse_status`
* `candidates[]`
* `ambiguities[]`
* `rejected_reason_codes[]`
* `notices[]`

**Stop-gate role**
Only `resolved_singleton` may proceed automatically to deterministic transform.

### `adeu_semantic_normal_form@1`

**Purpose**
The canonical semantic object.

**Authority posture**
Authoritative for semantic identity within the bounded profile.

**Key fields**

* `normal_form_id`
* `profile_id`
* `domain_kind`
* `clauses[]`
* `semantic_hash`
* `confidence_band`
* `uncertainty_notes[]`

`clauses[]` use:

* `relation_kind`
* `lane_tag`
* `object_kind`
* `object_value`
* `evidence[]`

**Stop-gate role**
This is the first object whose hash is semantically meaningful.

### `adeu_semantic_transform_contract@1`

**Purpose**
Explicit deterministic lowering law from one ADEU form to another.

**Authority posture**
Authoritative for transform legality.

**Key fields**

* `contract_id`
* `source_schema`
* `target_schema`
* `profile_id`
* `required_singleton_relations[]`
* `supported_multi_relations[]`
* `fixed_defaults{}`
* `unsupported_relation_kinds[]`
* `semantic_hash`

**Stop-gate role**
If required relations are missing or unsupported relations appear, transform blocks.

### `adeu_semantic_transform_result@1`

**Purpose**
Authoritative record of a transform attempt.

**Authority posture**
Authoritative for whether the transform ran and what target it emitted.

**Key fields**

* `transform_result_id`
* `contract_id`
* `source_semantic_hash`
* `target_schema`
* `transform_status`
* `blocking_issues[]`
* `target_payload`
* `target_semantic_hash`

**Stop-gate role**
`transform_status` must be `transformed` for downstream consumption.

### `adeu_taskpack_binding_spec_seed@1`

**Purpose**
The first domain-specific target artifact for this family.

**Authority posture**
Authoritative typed bridge from semantic form to the existing `V48A` lane.
It is not a replacement for `anm_taskpack_binding_profile@1`.

**Key fields**

* `seed_id`
* `profile_id`
* `snapshot_id`
* `snapshot_sha256`
* `binding_subject_id`
* `scope_anchor_id`
* `scope_source_ref`
* `scope_binding_entry_ref`
* `policy_anchor_id`
* `policy_source_ref`
* `policy_authority_clause_ref`
* `worker_subject_ref`
* `mutation_posture`
* `allowlist_projection[]`
* `forbidden_projection`
* `prompt_projection_posture`
* `lineage_resolution_posture`
* `unsupported_mapping_posture`
* `semantic_hash`

This artifact is the right v0 bridge because it is smaller than the full V48 binding profile and still directly useful.

## 5. Arc and slice plan

### V0 arc

`v0.semantic_form_seed_for_repo_policy_work`

### Slice A — released anchor profile

Deliver:

* `adeu_semantic_parse_profile@1`
* fixed released anchor handles over the real V45/V47/V48A fixture surfaces
* snapshot-bound hash

Acceptance:

* same profile bytes -> same `semantic_hash`
* same anchor set each run
* no duplicate anchor ids
* no alias-table nondeterminism

### Slice B — canonical normal form + equivalence law

Deliver:

* clause model
* normal form model
* canonical hash law
* dedupe/sort behavior

Acceptance:

* clause order does not affect `semantic_hash`
* duplicate identical clauses normalize away
* paraphrase variants that recover same clause set have identical `semantic_hash`

### Slice C — bounded NL recovery

Deliver:

* profile-relative parser
* ambiguity classification
* unsupported rejection

Acceptance:

* resolved singleton case succeeds
* “catalog” ambiguity returns exactly two typed alternatives in the reference profile
* missing required anchors yields `clarification_required`
* unsupported mutation request yields `rejected_unsupported`

### Slice D — deterministic ADEU->ADEU transform

Deliver:

* `adeu_semantic_transform_contract@1`
* `adeu_taskpack_binding_spec_seed@1`
* deterministic lowering logic

Acceptance:

* same source normal form + same contract -> same target bytes
* different scope anchor -> different target hash
* missing singleton relation -> blocked status
* non-`read_only` mutation posture -> blocked

### Slice E — benchmark harness

Deliver:

* benchmark fixture
* replay harness
* expected hash groups

Acceptance:

* paraphrase group collapses to one hash
* ambiguity cases remain ambiguous
* unsupported cases reject
* transform determinism remains 100%

### Non-goals

* general semantic language
* direct execution approval
* general policy inference
* natural-language command synthesis
* replacing `D@1`
* replacing `V48`
* autonomous taskpack emission from ambiguous text

## 6. Projected package / code structure

```text
packages/adeu_semantic_forms/
  pyproject.toml
  schema/
    adeu_semantic_parse_profile.v1.json
    adeu_semantic_parse_result.v1.json
    adeu_semantic_normal_form.v1.json
    adeu_semantic_transform_contract.v1.json
    adeu_semantic_transform_result.v1.json
    adeu_taskpack_binding_spec_seed.v1.json
  src/adeu_semantic_forms/
    __init__.py
    models.py
    export_schema.py
    profiles/
      repo_policy_work_v0.py
    nl_recovery.py
    canonicalize.py
    equivalence.py
    transforms/
      taskpack_binding_seed.py
      v48a_overlay.py
    cli.py
    benchmark.py
  tests/
    fixtures/repo_policy_work_v0/
      benchmark_cases.json
    test_parse_profile.py
    test_paraphrase_collapse.py
    test_ambiguity_typing.py
    test_rejection_posture.py
    test_transform_to_binding_seed.py
    test_v48a_overlay_replay.py
```

Artifact emission:

```text
artifacts/semantic_forms/v0/repo_policy_work/
  parse_profile.json
  parse_result.json
  normal_form.json
  transform_contract.json
  transform_result.json
  binding_spec_seed.json
  benchmark_report.json
```

CLI shape:

```bash
python -m adeu_semantic_forms.cli parse \
  --profile repo_policy_work_v0.reference_v48a \
  --text-file input.txt \
  --out artifacts/semantic_forms/v0/repo_policy_work/parse_result.json

python -m adeu_semantic_forms.cli transform \
  --profile repo_policy_work_v0.reference_v48a \
  --normal-form artifacts/semantic_forms/v0/repo_policy_work/normal_form.json \
  --contract repo_policy_work_v0_to_taskpack_binding_spec_seed@1 \
  --out artifacts/semantic_forms/v0/repo_policy_work/transform_result.json
```

## 7. Actual minimal implementation proposal

The prototype bundle I generated is external and not repo-integrated, but it is real enough to show the intended shape.

### Canonical normal form and semantic hash

```python
class SemanticClause(BaseModel):
    relation_kind: RelationKind
    object_value: str
    lane_tag: LaneTag
    object_kind: ObjectKind
    evidence: list[str] = Field(default_factory=list)

class SemanticNormalForm(BaseModel):
    schema: Literal["adeu_semantic_normal_form@1"] = "adeu_semantic_normal_form@1"
    profile_id: str
    domain_kind: SemanticDomainKind = "repo_policy_work"
    clauses: list[SemanticClause]
    semantic_hash: str

    @model_validator(mode="after")
    def _validate(self) -> "SemanticNormalForm":
        self.clauses = dedupe_and_sort(self.clauses)
        basis = {
            "schema": self.schema,
            "profile_id": self.profile_id,
            "domain_kind": self.domain_kind,
            "clauses": [
                {"relation_kind": c.relation_kind, "object_value": c.object_value}
                for c in self.clauses
            ],
        }
        self.semantic_hash = sha256_canonical_json(basis)
        return self
```

That is the core identity law.

### Profile-relative NL recovery

```python
def parse_nl_to_semantic_form(*, text: str, profile: SemanticParseProfile) -> SemanticParseResult:
    normalized = _normalize_text(text)

    unsupported_hits = []
    for pattern in profile.unsupported_patterns:
        pat = _normalize_text(pattern)
        if re.search(rf"(?<![a-z0-9_]){re.escape(pat)}(?![a-z0-9_])", normalized):
            unsupported_hits.append(pattern)

    if unsupported_hits:
        return rejected_unsupported(...)

    scope_matches = _best_anchor_matches(profile.scope_anchors, normalized)
    policy_matches = _best_anchor_matches(profile.policy_anchors, normalized)
    worker_matches = _best_anchor_matches(profile.worker_anchors, normalized) or [DEFAULT_WORKER]
    mutation_matches = _collect_lexicon_matches(profile.mutation_lexicon, normalized) or ["read_only"]
    artifact_kind_matches = _collect_lexicon_matches(profile.artifact_kind_lexicon, normalized) or ["taskpack_binding_spec_seed"]
    effect_matches = _collect_lexicon_matches(profile.effect_lexicon, normalized)
    path_matches = _collect_repo_paths(text)

    if not scope_matches or not policy_matches:
        return clarification_required(...)

    candidates = [
        materialize_normal_form(...)
        for scope_anchor, policy_anchor in product(scope_matches, policy_matches)
    ]
    return resolved_singleton_or_typed_alternatives(...)
```

What this does not pretend to solve:

* open-domain language understanding
* latent semantics
* general path inference
* conditional semantics

It is intentionally a bounded alias-and-anchor recovery engine.

### Deterministic transform

```python
def transform_normal_form_to_binding_seed(
    *,
    normal_form: SemanticNormalForm,
    profile: SemanticParseProfile,
    contract: SemanticTransformContract,
) -> SemanticTransformResult:
    scope_anchor_id = require_singleton(normal_form, "bind_scope_anchor")
    policy_anchor_id = require_singleton(normal_form, "bind_policy_anchor")
    worker_subject_ref = require_singleton(normal_form, "use_worker_subject")
    mutation_posture = require_singleton(normal_form, "set_mutation_posture")
    artifact_kind = require_singleton(normal_form, "produce_artifact_kind")

    if mutation_posture != "read_only":
        return blocked_unsupported_relation(...)

    scope_anchor = resolve_scope_anchor(profile, scope_anchor_id)
    policy_anchor = resolve_policy_anchor(profile, policy_anchor_id)

    seed = TaskpackBindingSpecSeed.model_validate({
        "profile_id": profile.profile_id,
        "snapshot_id": profile.snapshot_id,
        "snapshot_sha256": profile.snapshot_sha256,
        "scope_source_ref": scope_anchor.resolved_scope_ref,
        "scope_binding_entry_ref": scope_anchor.resolved_binding_entry_ref,
        "policy_source_ref": policy_anchor.resolved_policy_consumer_ref,
        "policy_authority_clause_ref": policy_anchor.resolved_clause_ref,
        "worker_subject_ref": worker_subject_ref,
        "allowlist_projection": allow_paths(...),
        "forbidden_projection": {...},
        "prompt_projection_posture": "projection_only_non_authoritative",
        "lineage_resolution_posture": "fail_closed_on_unresolved_or_stale_lineage",
        "unsupported_mapping_posture": "fail_closed",
    })
    return transformed(seed)
```

This is the important separation line:

* ambiguity recovery ended before this function ran
* from here onward the transform is deterministic

### Honest limitations of the prototype

The prototype is intentionally partial:

* path extraction is regex-based and not yet parity-hardened to harness-grade repo-root normalization
* command/evidence-slot recovery from NL is not implemented
* the parse profile is fixed to a tiny released-anchor universe
* ambiguity handling is deliberate but still lexicon-driven, not grammar-complete

That is still a valid v0 because the laws are explicit and bounded.

## 8. Worked examples

### Example 1 — resolved singleton

Input text:

> Prepare a read-only taskpack binding seed for the released symbol catalog under release_surface:owner. Use the default codex worker. Allow `packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py` and `packages/adeu_agent_harness/tests/test_taskpack_binding.py`. Forbid network calls and multi-worker topology.

Recovered normal form:

* `bind_scope_anchor(repo_symbol_catalog)`
* `bind_policy_anchor(release_surface:owner)`
* `use_worker_subject(worker:repo_internal_single_codex_worker:default)`
* `set_mutation_posture(read_only)`
* `produce_artifact_kind(taskpack_binding_spec_seed)`
* `allow_path(packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py)`
* `allow_path(packages/adeu_agent_harness/tests/test_taskpack_binding.py)`
* `forbid_effect(network_calls)`
* `forbid_effect(multi_worker_topology)`

Sample artifact: [normal form](sandbox:/mnt/data/adeu_semantic_forms_v0/samples/sample_semantic_normal_form.json)

Resulting semantic hash:

* `fbf63c0e4fae309a24be8d751c2b44b43ea5be5506231b2ee822565e69830cf9`

Deterministic transform output resolves to real repo-grounded refs:

* `scope_source_ref` → `apps/api/fixtures/repo_description/vnext_plus101/repo_symbol_catalog_v101_reference.json`
* `scope_binding_entry_ref` → `...repo_descriptive_normative_binding_frame_v105_reference.json#binding_entry_d9b4bd5b1693dea4ec3c09cd`
* `policy_source_ref` → `packages/adeu_commitments_ir/tests/fixtures/v47e/reference_anm_policy_consumer_binding_profile.json#consumer_rows[0]`
* `policy_authority_clause_ref` → `release_surface:owner`

Sample artifact: [transform result](sandbox:/mnt/data/adeu_semantic_forms_v0/samples/sample_semantic_transform_result.json)

### Example 2 — typed ambiguity

Input text:

> Prepare a read-only binding seed for the catalog under the owner rule. Use the default codex worker.

In the reference profile, `catalog` is intentionally ambiguous between:

* `repo_entity_catalog`
* `repo_symbol_catalog`

So v0 returns:

* `parse_status = typed_alternatives`
* two candidate normal forms
* no silent collapse

Sample artifact: [ambiguous parse result](sandbox:/mnt/data/adeu_semantic_forms_v0/samples/sample_semantic_parse_result_ambiguous.json)

That is the correct posture.
Completion here means the ambiguity is represented, not erased.

### Example 3 — unsupported

Input text:

> Pick whatever policy seems closest and modify the repo if needed.

v0 returns:

* `parse_status = rejected_unsupported`
* reason code for unsupported recovery

Because:

* “whatever policy” attempts free policy selection
* “modify the repo” violates the frozen read-only posture

That is the correct fail-closed behavior.

### Upward projection example

A deterministic natural-language rendering from the normal form could be:

> Produce a read-only taskpack binding seed for `repo_symbol_catalog` under `release_surface:owner`, using `worker:repo_internal_single_codex_worker:default`, allowing `taskpack_binding.py` and `test_taskpack_binding.py`, and forbidding `multi_worker_topology` and `network_calls`.

That rendering is derived from the canonical form.
It is not the authority source for semantic identity.

## 9. Acceptance criteria and failure modes

### Acceptance criteria

v0 is successful if all of the following hold:

* the parse profile is deterministic and hash-stable
* paraphrases in the benchmark collapse to the same normal-form hash
* raw NL text hashes are never used as semantic identity
* ambiguity is represented as typed alternatives, not silently collapsed
* unsupported constructs are explicitly rejected
* `adeu_semantic_normal_form@1` validates strictly
* `adeu_semantic_transform_contract@1` defines required singleton relations explicitly
* `adeu_semantic_transform_result@1` is deterministic for fixed source hash + contract
* the emitted `adeu_taskpack_binding_spec_seed@1` resolves to real released V45/V47 refs
* no automatic execution, mutation, or approval authority is implied

### Important failure modes

* **Alias overreach**: a generic alias like “catalog” matches too much.
* **Alias underreach**: a natural paraphrase fails to recover a valid anchor.
* **Profile-relative semantics mistaken for universal semantics**: the same phrase may parse differently under a different profile.
* **Released anchor drift**: the profile hardcodes released refs that later change.
* **Path normalization weakness**: extracted repo paths may be lexically present but not policy-safe until stronger normalization is added.
* **Transform overreach**: transform resolves a binding entry where multiple matches should have blocked.
* **Truth inflation**: recovery candidates are treated as “the meaning” rather than hypotheses under a bounded profile.
* **D@1 confusion**: users may mistake this family for policy authoring; it is not.
* **Execution inflation**: a valid binding seed could be misread as approval to run a taskpack; it is not.
* **Hidden default creep**: too many defaults in the transform contract can silently widen meaning.

The main guardrail is to keep the laws explicit and the domain tiny.

## 10. Forward path after v0

### What v1 should add

1. **A tiny authorable ADEU sentence syntax**
   Not just JSON artifacts.
   A small textual form like:

   ```text
   BIND_SCOPE repo_symbol_catalog
   BIND_POLICY release_surface:owner
   MUTATION read_only
   USE_WORKER worker:repo_internal_single_codex_worker:default
   ALLOW_PATH packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py
   FORBID_EFFECT network_calls
   EMIT taskpack_binding_spec_seed
   ```

   Then `NL -> ADEU` can target that textual form as well as JSON normal form.

2. **Command/evidence-slot semantic clauses**
   Enough to replay the full `reference_taskpack_binding_spec.json` without a manual overlay.

3. **Released-anchor loaders**
   Instead of a fixed reference profile, load anchor handles from released registries and artifacts.

4. **Equivalence-diff tooling**
   A derived report that explains exactly why two semantic normal forms differ.

5. **Optional bridge into `build_v48a_taskpack_binding_profile`**
   Once seed + overlays are complete.

### What remains intentionally unsolved after v0

* general semantics
* open-domain natural-language understanding
* automatic policy selection
* deontic reasoning outside `D@1`
* write/execute intent
* multi-domain semantic language
* universal semantic identity across profiles

### How Codex in ADEU harness should iterate next

The right next pass is methodological:

* audit the six schemas
* adversarially test alias collisions
* verify that paraphrase groups really collapse and ambiguous groups do not
* verify that `semantic_hash` excludes NL provenance
* verify transform determinism over repeated runs
* only then widen the anchor universe or add command/evidence-slot clauses

There is a clean relation to the earlier symbol-audit direction: both want deterministic closure over a bounded universe. But here the bounded universe is not “all parsed symbols”; it is “all supported semantic clauses under a frozen profile.” That is the right way to make semantics governable without pretending free prose already has canonical identity.
