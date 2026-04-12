### A. Hardening verdict

No direct contradiction was found in the retained draft.

What remains fixed:

* the substrate is still **not** a new general DB kernel,
* it is still a **market-data schema-family substrate**,
* the thin-stack carrier profile is still retained:

  * raw immutable `jsonl.zst`,
  * normalized immutable family-local `Parquet`,
  * `Postgres` catalog/control plane,
  * `DuckDB` historical/runtime layer,
* the released and deferred family cut lines remain unchanged,
* the raw / normalized / manifest triple split remains unchanged,
* the `logical_hash` vs `carrier_bytes_hash` split remains unchanged,
* the family-aware operator surface remains unchanged,
* the roadmap shape remains unchanged.

What is repaired:

* the market-data family system is now positioned explicitly as a **descendant domain-family constitution** under the broader ADEU schema-authoring laws, not a peer constitutional center;
* source binding, listing identity, listing terms, endpoint mapping, publication semantics, and unit/multiplier bindings become first-class versioned artifacts rather than adapter-hidden logic;
* normalization is hardened into an explicit **semantic outcome algebra** aligned with the repo’s newer semantic-form regime;
* empirical convergence is widened from carrier tuning to **family-boundary, subfamily-promotion, and IR-boundary** tuning;
* derived features now sit behind an explicit **deontic force barrier** that prevents strategy laundering.

The hardened position is therefore:

> the retained v0 is one **lower-order ADEU domain-family cluster for replay-sensitive market data**, realized in v0 by the retained carrier profile, governed by explicit binding artifacts, fail-closed normalization state law, and a hard descriptive/advisory barrier around derived features.

---

### B. Repo-wide doctrinal placement

#### B.1 Doctrinal descent

The market-data substrate is:

* **not** a new meta-schema,
* **not** a peer constitutional center,
* **not** an alternative repo-wide authoring doctrine.

It is a **lower-order descendant** under the broader ADEU schema-family grammar.

The descent chain is:

```text
repo-wide schema-authoring laws
  -> repo-wide schema-family doctrine
    -> repo-wide descriptive/normative binding frame
      -> domain-family cluster: market_data
        -> market_data_schema_family_registry@1
          -> market_data_family_definition@N
            -> family-local submodes / subfamilies
              -> market_data_family_instance_manifest@N
                -> runtime/evidence artifacts
                -> projection artifacts
                -> benchmark/evolution artifacts
```

This is the same kind of descendant role other concrete schema families play under the higher-order authoring grammar. The market-data cluster specializes the general authoring laws for **replay-sensitive exchange-originated market data**, just as other concrete families specialize those laws for their own bounded domains.

At repo-wide role-form level, the market-data artifact stack also follows the same carrier-role pattern already used elsewhere:

* registries, manifests, catalogs: **CuratedSet**
* source-binding and publication contracts: **ContractGate**
* raw/normalized/runtime records: **TraceRecord**
* family-local IR declarations and feature-set definitions: **StructuralModel**
* benchmark/evolution decisions: **Adjudication**

So the market-data substrate is best understood as a **descendant carrier-overlay bundle plus domain-law bundle**, not a parallel constitution.

#### B.2 Inherited coordinate envelope

The market-data cluster should either carry directly, or be derivably classifiable by, the same recursive-coordinate envelope:

```json
{
  "node_kind": "...",
  "placement_basis": { "...": "..." },
  "coverage_scope": { "...": "..." },
  "force_profile": { "...": "..." },
  "normalized_carrier": "...",
  "lifecycle_overlay": "...",
  "visibility_overlay": "...",
  "trust_overlay": "...",
  "phase_overlay": "..."
}
```

This envelope is inherited from the broader authoring line. Market-data specializes it; it does not redefine it.

#### B.3 Field ownership by layer

| Layer                                    | Owned fields                                                                                                                                                                                                                                                                                                                |
| ---------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Universal / inherited constitutional** | `schema`, artifact ids, content hashes, `classification_posture`, `classification_method`, `source_artifact_refs`, `supporting_evidence_refs`, `placement_basis`, `coverage_scope`, `force_profile`, `normalized_carrier`, `transition_law`, `occupancy_law`, descriptive/normative binding fields, `amendment_entitlement` |
| **Market-data-domain constitutional**    | `world_object_kind`, `family_assignment_law`, `source_binding_basis`, `listing_identity_basis`, `temporal_indexing_model`, `replay_model`, `identity_axes`, `canonical_timestamp_policy`, `logical_hash_equivalence_mode`, `compaction_law`, `rollup_resampling_law`, `normalization_state_algebra`, segment-lowering law   |
| **Family-local**                         | payload contract, native invariants, dominant operator algebra, mutation profile, publication/revision semantics, admissible source endpoint kinds, unit kinds, submodes/subfamilies                                                                                                                                        |
| **Instance-local**                       | `venue_listing_ref`, `interval_ref`, `metric_kind`, `feature_set_ref`, exact binding-contract refs, exact listing-terms refs, exact unit/multiplier refs, placement plan, carrier-profile ref, quality-policy thresholds                                                                                                    |

Two clarifications matter here.

First, `placement_basis` and `coverage_scope` are **not** the same thing. `coverage_scope` says what semantic region an artifact covers. `placement_basis` says how it is placed, partitioned, and retrieved.

Second, `occupancy_law` and `admissibility_law` must now be explicit.

* `occupancy_law` answers: what may lawfully occupy one position inside a family instance.
* `admissibility_law` answers: what may lawfully cross from raw capture into that occupancy.

Examples already implicit in the retained draft now become explicit:

* trade family: one semantic execution event occupies one event identity; conflicting duplicates divert to anomaly/evidence, not second canonical occupancy.
* bar family: one semantic slot may carry a revision chain, but only one latest-final occupant in the latest projection.
* reference/OI families: point or interval sample occupancy is explicit by metric kind and unit kind.
* derived feature family: one anchor grid position may carry one row per `(feature_set_ref, derivation_spec_hash)`.

#### B.4 Recursive-coordinate crosswalk

Artifact-level node kinds for this domain should be read as:

* `registry_node`
* `family_node`
* `instance_node`
* `binding_node`
* `runtime_evidence_node`
* `projection_node`
* `decision_node`

These artifact node kinds are orthogonal to family taxonomic nodes such as `family`, `subfamily`, and instance.

| Artifact class                                                                              | Node kind               | Placement basis / coverage scope                                                                                  | Force profile                                                                                            | Carrier                                        | Overlays                                                                                                                                     |
| ------------------------------------------------------------------------------------------- | ----------------------- | ----------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------- | ---------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------- |
| `market_data_schema_family_registry`                                                        | `registry_node`         | placement by `domain_cluster=market_data`; coverage is released family cluster                                    | normative descendant registry; no self-amendment                                                         | Postgres row + JSON export                     | lifecycle `released`; visibility `governance_visible`; trust `adjudicated/settled`; phase `authoring/release`                                |
| `market_data_family_definition`                                                             | `family_node`           | placement by `family_name + family_version`; coverage is one family or subfamily tree                             | hard family law inside substrate runtime                                                                 | Postgres row + JSON/schema export              | lifecycle `released_v0_core` / `specified_deferred`; visibility `control_plane + governance`; trust `adjudicated/settled`; phase `authoring` |
| `market_data_family_instance_manifest`                                                      | `instance_node`         | placement by `family_ref + venue_listing_ref + interval/metric/feature scope`; coverage is one concrete instance  | compiled operational authority for routing, pruning, and replay selection; not semantic invention        | Postgres row + JSON export                     | lifecycle `active/superseded`; visibility `control_plane_internal`; trust `compiled`; phase `ingest/query`                                   |
| `market_identity_binding`, `market_data_source_binding_contract`, sibling binding contracts | `binding_node`          | placement by `venue_id + endpoint_kind + raw symbol/market metadata`; coverage is one binding rule or one listing | hard fail-closed for family assignment, identity resolution, unit resolution, and construction semantics | Postgres rows + JSON exports                   | lifecycle `versioned/active/superseded`; visibility `control_plane_internal`; trust `observed + adjudicated`; phase `binding/normalization`  |
| `market_data_raw_capture_segment_manifest`                                                  | `runtime_evidence_node` | placement by `venue + source_kind + utc_time_span`; coverage is one immutable raw segment                         | descriptive source truth for observed bytes only; zero semantic promotion authority                      | Postgres row + `jsonl.zst`                     | lifecycle `immutable`; visibility `audit_visible`; trust `source_observation`; phase `capture`                                               |
| `market_data_replay_segment_manifest`                                                       | `runtime_evidence_node` | placement by `family_instance_ref + utc_day/hour`; coverage is one immutable normalized segment                   | compiled query/replay authority inside accepted family law; not normative                                | Postgres row + `Parquet`                       | lifecycle `active/compacted/superseded`; visibility `query_visible`; trust `compiled_deterministic`; phase `normalize/query/compact`         |
| `market_data_ingestion_normalization_record`                                                | `runtime_evidence_node` | placement by normalization batch or raw segment                                                                   | evidence and gating summary only                                                                         | Postgres row + JSON                            | lifecycle `immutable`; visibility `audit_visible`; trust `compiled_deterministic`; phase `normalize`                                         |
| `market_data_compaction_record`                                                             | `runtime_evidence_node` | placement by `family_instance_ref + compaction_run`                                                               | equivalence-evidence only; no semantic amendment entitlement                                             | Postgres row + JSON                            | lifecycle `immutable`; visibility `audit_visible`; trust `compiled_deterministic`; phase `compact`                                           |
| `market_data_feature_derivation_record`                                                     | `runtime_evidence_node` | placement by `feature_set_ref + anchor_grid + derivation_spec_hash`                                               | compiled/advisory only by default                                                                        | Postgres row + output `Parquet` refs           | lifecycle `immutable/superseded`; visibility `research_visible`; trust `compiled_deterministic`; phase `derive`                              |
| `market_data_projection_manifest`                                                           | `projection_node`       | placement by `consumer_target + source_refs + projection_kind`                                                    | consumer-bound; may only preserve or strengthen upstream force profile                                   | Postgres row + DuckDB/Arrow/Parquet descriptor | lifecycle `active/superseded`; visibility `consumer_scoped`; trust `compiled`; phase `serve`                                                 |
| benchmark decision artifacts                                                                | `decision_node`         | placement by `candidate_point_kind + family/IR scope + workload class + host class`                               | advisory unless separately accepted; never self-amending                                                 | Postgres rows + JSON/Markdown                  | lifecycle `candidate/accepted/replaced`; visibility `governance_visible`; trust `tooling/adjudication`; phase `benchmark/evolve`             |

#### B.5 O / E / D / U realization map

The market-data substrate should now make its ODEU realization explicit.

**O — Ontology / object law**

* `world_object_kind`
* family and subfamily definitions
* identity axes
* native invariants
* occupancy law
* family/subfamily distinctions
* listing terms and unit semantics
* family-local IR payload contracts

Primary artifacts:
`market_data_family_definition`, `market_identity_binding`, `market_venue_listing_terms`, `market_data_feature_set_definition`.

**E — Evidence / observation / replay**

* raw capture truth
* normalization outcome state
* provenance
* anomaly surfaces
* replay determinism
* logical hash equivalence
* compaction evidence
* derivation evidence

Primary artifacts:
`market_data_raw_capture_segment_manifest`, `market_data_ingestion_normalization_record`, `market_data_normalization_resolution_record`, `market_data_replay_segment_manifest`, `market_data_compaction_record`, `market_data_provenance_record`, `market_data_quality_anomaly_record`.

**D — Deontics / binding / admissibility**

* source-binding law
* family-assignment law
* force profiles
* admissibility law
* descriptive/normative binding frame
* promotion barriers
* downstream consumer-binding law

Primary artifacts:
`market_data_source_binding_contract`, `market_endpoint_field_mapping_contract`, `market_publication_semantics_contract`, `market_unit_multiplier_binding`, `market_data_descriptive_normative_binding_frame`, `market_data_downstream_consumer_binding`.

**U — Utility / operator / serving**

* family-aware operator algebra
* query/runtime lowering
* benchmark decision surfaces
* serving/projection layers
* feature materialization
* carrier-profile decisions

Primary artifacts:
`market_data_query_plan_record`, `market_data_projection_manifest`, `market_data_benchmark_run_record`, `market_data_benchmark_decision_report`, `market_data_ir_boundary_review`, `market_data_family_evolution_decision_report`.

The membrane/adjudication picture in the runtime is therefore:

```text
raw_capture_segment (E source truth)
  -> binding/adjudication membrane (D)
       source_binding_contract
       + identity_binding
       + listing_terms
       + endpoint_field_mapping_contract
       + publication_semantics_contract
       + unit_multiplier_binding
  -> family-local IR rows (O)
  -> replay segments / replay determinism / provenance (E)
  -> operators / projections / benchmarks (U, always bounded by D)
```

#### B.6 Carrier-profile non-constitutionality

The retained v0 carrier profile remains:

* raw immutable `jsonl.zst`
* normalized immutable `Parquet`
* `Postgres` control plane
* `DuckDB` historical/runtime execution

That choice stays fixed for v0.

But it is **not** the constitutional identity of the substrate.

Under the repo-wide “core envelope plus carrier overlays” line, this is one realized carrier-overlay bundle beneath the market-data family grammar.

A later carrier-profile replacement is admissible in principle only if it preserves:

* family law,
* identity law,
* source-binding law,
* normalization state law,
* replay law,
* logical-hash equivalence,
* released native-operator equivalence,
* descriptive/normative binding law.

A new carrier profile may change:

* byte layout,
* storage engine,
* compaction implementation,
* serving cache design,
* query executor backend,

but it may not silently change:

* family assignment,
* listing identity,
* unit semantics,
* revision law,
* canonical replay order,
* or the deontic posture of projections and derived features.

---

### C. New or repaired artifact family set

These are **not** new market-data families. They are the missing control/binding artifacts required to stop semantic authority from hiding in code.

#### C.1 Source-binding and listing semantics artifacts

**`market_data_source_binding_contract@1`**
Level: family-level contract with instance-resolution hooks.
Posture: compiled, usually `derived_deterministically`, escalatable to `adjudicated`.
Purpose: bind `(venue_id, adapter_kind, endpoint_kind)` to exactly one target family or subfamily mode, one endpoint-field mapping contract, one publication-semantics contract, and one identity-resolution basis.
Prevents: raw-shape family guessing and adapter-only semantic authority.

Key fields:

```json
{
  "schema": "market_data_source_binding_contract@1",
  "source_binding_contract_id": "...",
  "venue_id": "binance",
  "adapter_kind": "live_stream_connector",
  "endpoint_kind": "ws_kline_1m",
  "target_family_ref": "market_bar_family@1",
  "target_submode_ref": "exchange_published_bar",
  "identity_resolution_basis": {
    "lookup_keys": ["payload.symbol", "endpoint.market_kind"]
  },
  "field_mapping_contract_ref": "...",
  "publication_semantics_contract_ref": "...",
  "admissibility_conditions": ["listing_binding_required", "unit_binding_complete"],
  "classification_posture": "derived_deterministically",
  "classification_method": "semantic_function",
  "supporting_evidence_refs": ["..."]
}
```

**`market_identity_binding@1`**
Level: instance-local binding artifact.
Posture: mixed; `venue_listing_ref` binding is descriptive/compiled, optional `canonical_instrument_ref` promotion is separately governed.
Purpose: bind raw venue symbol/materialized market metadata to stable `venue_listing_ref`.
Prevents: symbol-string laundering across spot/perp/futures and across venues.

**`market_venue_listing_terms@1`**
Level: instance-local semantic terms artifact.
Posture: mixed descriptive + adjudicated.
Purpose: make market kind, settlement semantics, contract-size, multiplier, and unit basis explicit.
Prevents: market-kind collapse and unit ambiguity.

Key fields:

```json
{
  "schema": "market_venue_listing_terms@1",
  "venue_listing_ref": "binance.linear_perpetual.BTCUSDT",
  "raw_symbol": "BTCUSDT",
  "market_kind": "linear_perpetual",
  "base_asset_ref": "BTC",
  "quote_asset_ref": "USDT",
  "settlement_asset_ref": "USDT",
  "quantity_unit_kind": "contracts",
  "price_unit_kind": "quote_per_base",
  "notional_unit_kind": "quote_notional",
  "contract_size": "0.001 BTC",
  "multiplier_ref": "...",
  "canonical_instrument_ref": null,
  "classification_posture": "adjudicated"
}
```

**`market_endpoint_field_mapping_contract@1`**
Level: family-local binding contract.
Posture: compiled/adjudicated.
Purpose: declare how raw source fields map to canonical family-local IR fields, including timestamp axes, sequence axes, null policy, coercions, and required/fallback fields.
Prevents: field semantics living only in adapter code.

**`market_publication_semantics_contract@1`**
Level: family-local publication/transition contract.
Posture: compiled/adjudicated.
Purpose: declare publication form and revision semantics explicitly. For example:

* `point_event`
* `forming_slot_update`
* `closed_slot_snapshot`
* `point_sample`
* `interval_assignment`

Carries:

* `construction_basis`
* `revision_semantics`
* `late_correction_policy`
* `duplicate_policy`
* `ordering_policy`
* deferred `snapshot_bootstrap_policy` for order-book lines.

Prevents: source publication style and bar construction semantics from hiding in code.

**`market_unit_multiplier_binding@1`**
Level: instance-local or listing-local binding artifact.
Posture: descriptive + compiled.
Purpose: make contract-size, multiplier, decimal scale, and unit conversion explicit for OI, trade quantities, notional fields, and reference metrics.
Prevents: silent contracts-to-notional or contracts-to-base reinterpretation.

#### C.2 Family-assignment relation among binding artifacts

At ingest, family assignment is no longer “the normalizer knows.”

It becomes:

```text
1. select market_data_source_binding_contract
   by (venue_id, adapter_kind, endpoint_kind)

2. resolve market_identity_binding
   using the contract’s declared identity_resolution_basis

3. load market_venue_listing_terms
   for the resolved venue_listing_ref

4. apply market_endpoint_field_mapping_contract
   to obtain family-local field candidates

5. apply market_publication_semantics_contract
   to bind construction_basis, revision law, and temporal form

6. apply market_unit_multiplier_binding
   where the family requires unit or multiplier semantics

7. emit market_data_normalization_resolution_record
   and only lower when the outcome is resolved_singleton
```

Two hard laws follow.

**Adapter non-authority law.**
Adapters may decode transport payloads and persist raw capture. They may not be the sole authority for family selection, listing identity, units, construction basis, or revision semantics.

**Binding completeness law.**
If a packet needs one of the required binding artifacts and the artifact is absent, the outcome is not “best effort.” It is `clarification_required`.

#### C.3 Normalization and gating artifacts

**`market_data_ingestion_normalization_record@1`** — repaired
Level: runtime/evidence-level.
Purpose: batch summary over one normalization pass.
New required content:

* outcome histogram by normalization state,
* refs to per-subject resolution records,
* counts of rows actually lowered to replay segments,
* counts blocked by ambiguity, missing binding, or unsupported law.

**`market_data_normalization_resolution_record@1`** — new
Level: runtime/evidence-level.
Purpose: per raw packet or per decomposed normalization subject, emit the exact semantic outcome state and candidate interpretations.
Prevents: collapsing ambiguous or unsupported semantics into casual flags.

Key fields:

```json
{
  "schema": "market_data_normalization_resolution_record@1",
  "resolution_id": "...",
  "raw_capture_ref": "...",
  "source_binding_contract_ref": "...",
  "resolution_state": "typed_alternatives",
  "candidate_interpretations": [
    {
      "candidate_id": "...",
      "family_ref": "mark_index_funding_family@1",
      "submode_ref": "point_reference_metric",
      "payload_contract_hash": "..."
    },
    {
      "candidate_id": "...",
      "family_ref": "mark_index_funding_family@1",
      "submode_ref": "interval_assigned_rate",
      "payload_contract_hash": "..."
    }
  ],
  "ambiguity_records": [
    {
      "ambiguity_kind": "multiple_typed_interpretations",
      "severity": "high",
      "status": "unresolved"
    }
  ],
  "lowering_posture": "evidence_only_ambiguous",
  "required_new_contract_kinds": [],
  "rejected_reason_codes": []
}
```

#### C.4 Evolution / IR-boundary artifacts

**`market_data_benchmark_run_record@1`** — extended
Now supports `candidate_point_kind` values:

* `carrier_profile`
* `family_boundary`
* `ir_boundary`
* `subfamily_promotion`

**`market_data_benchmark_decision_report@1`** — extended
Still advisory by default, but now may justify:

* carrier-profile preference,
* proposed family split,
* subfamily promotion,
* IR boundary refinement.

It does **not** amend family law by itself.

**`market_data_ir_boundary_review@1`** — new
Level: decision/evidence.
Purpose: record empirical review of a family-local IR cut.

Key contents:

* incumbent family ref,
* candidate IR profiles,
* raw-field drop map,
* payload occupancy/null-sparsity analysis,
* operator consumption map,
* native-operator escape rate,
* recommended action: `retain`, `narrow`, `widen`, `split_payload`, `promote_submode`.

**`market_data_family_evolution_decision_report@1`** — new
Level: decision/evidence.
Purpose: compare candidate family boundaries or subfamily promotions.

Required posture:

* `amendment_entitlement = not_authorized_by_this_artifact`
* explicit `migration_equivalence_mode`
* explicit `authority_posture = advisory_until_acceptance`

#### C.5 Feature force-profile and promotion artifacts

**`market_data_feature_set_definition@1`** — new
Level: family-local artifact for `derived_feature_family`.
Posture: compiled/normative inside the feature family, but not execution-authoritative.
Purpose: declare the exact feature columns, causal window policy, alignment grid, null/warmup law, and default force profile.
Prevents: freeform feature naming and accidental action semantics.

**`market_data_descriptive_normative_binding_frame@1`** — repaired
Level: constitutional support artifact.
This is the market-data descendant of the repo-wide binding-frame pattern.

It should reuse the same posture fields already established repo-wide:

* `binding_posture`
* `authority_source_kind`
* `promotion_law_posture`

and extend only the domain-local input and consumer vocabularies.

**`market_data_projection_manifest@1`** — repaired
Now must carry:

* `consumer_class`
* `binding_posture`
* `authority_source_kind`
* `promotion_law_posture`
* `upstream_force_profile_ref`
* optional `downstream_consumer_binding_ref`

**`market_data_downstream_consumer_binding@1`** — new
Level: projection-level boundary artifact.
Purpose: explicitly bind a projection to a downstream consumer system and state what that consumer may and may not do with it.
This is the artifact that later strategy systems must bring before consuming derived features in any execution-significant path.

Key fields:

```json
{
  "schema": "market_data_downstream_consumer_binding@1",
  "consumer_binding_id": "...",
  "projection_ref": "...",
  "consumer_system_ref": "strategy_system_alpha",
  "consumer_class": "strategy_consumer",
  "binding_posture": "separate_normative_authority_required",
  "authority_source_kind": "separate_normative_artifact_required",
  "promotion_law_posture": "settled_authority_required_before_execution",
  "allowed_use_summary": "shadow evaluation and separately authorized execution gating only",
  "forbidden_use_summary": "no direct order submission, no identity rebinding, no family-law mutation",
  "authorizing_artifact_refs": ["..."]
}
```

---

### D. Normalization state algebra

The retained spec’s accepted / flagged / quarantined language is operationally useful but constitutionally too weak.

Normalization now needs a proper semantic-state algebra aligned with the repo’s semantic-form regime.

#### D.1 Outcome states

Use these four states directly:

* `resolved_singleton`
* `typed_alternatives`
* `clarification_required`
* `rejected_unsupported`

They mean the following in market-data normalization.

| State                    | Meaning                                                                                                   | May lower to replay segment?                           | Required outputs                                                |
| ------------------------ | --------------------------------------------------------------------------------------------------------- | ------------------------------------------------------ | --------------------------------------------------------------- |
| `resolved_singleton`     | Exactly one admissible family interpretation, one payload contract, and all required bindings are present | Yes, if no unresolved high/critical ambiguities remain | normalized rows, replay segment manifest, normalization records |
| `typed_alternatives`     | Two or more typed interpretations are lawfully possible under current bindings                            | No                                                     | normalization resolution record + ambiguity evidence only       |
| `clarification_required` | Normalization is blocked because a required binding or term contract is missing                           | No                                                     | normalization resolution record + missing-contract evidence     |
| `rejected_unsupported`   | The packet is outside current released family law or deferred by v0 cut line                              | No                                                     | normalization resolution record + rejected reason evidence      |

Examples:

* a trade packet with one source binding contract, one listing identity, and one field mapping contract is `resolved_singleton`;
* a metric packet that could be interpreted as two typed reference forms under incomplete publication semantics is `typed_alternatives`;
* an OI packet with missing unit binding is `clarification_required`;
* canonical order-book lowering in v0 core is `rejected_unsupported` even if raw capture is preserved.

#### D.2 Ambiguity register and lowering readiness

Each normalization resolution record should carry an `ambiguity_records[]` array with ASIR-style fields:

* `severity`: `low | medium | high | critical`
* `status`: `resolved | unresolved`

This enables a clean lowering law:

> A subject is admissible for replay-segment lowering iff
> `resolution_state = resolved_singleton`
> and there is no unresolved `high` or `critical` ambiguity.

So the normalizer has two distinct surfaces:

* **quality/anomaly surface** for descriptive issues that do not destroy semantic uniqueness,
* **ambiguity surface** for semantic uncertainty that blocks lowering.

This prevents low-level issues like late arrival or duplicate-exact collapse from being confused with unresolved semantic interpretation.

#### D.3 Lowering posture

To make runtime behavior explicit, each resolution record should also carry:

* `admissible_to_replay_segment`
* `evidence_only_ambiguous`
* `evidence_only_pending_binding`
* `evidence_only_unsupported`

Mapping:

* `resolved_singleton` -> `admissible_to_replay_segment`
* `typed_alternatives` -> `evidence_only_ambiguous`
* `clarification_required` -> `evidence_only_pending_binding`
* `rejected_unsupported` -> `evidence_only_unsupported`

#### D.4 What runtime must not do

The runtime must not:

* select one candidate out of `typed_alternatives` by heuristics,
* fill missing listing identity or units from raw values alone,
* promote `rejected_unsupported` into a generic fallback family,
* treat feature or benchmark success as a substitute for missing binding law.

If a new contract is needed, the outcome must say so explicitly.

---

### E. Family evolution and empirical convergence law

The retained draft already benchmarked carrier profiles. The hardening widens that to the actual thesis: empirical work must also refine **family boundaries**, **subfamily promotion**, and **IR boundaries**.

#### E.1 Candidate point kinds

The benchmark/evolution loop now operates over four candidate point kinds:

* `carrier_profile`
* `family_boundary`
* `ir_boundary`
* `subfamily_promotion`

Examples:

* carrier profile: hourly vs daily segment spans, row-group sizing, compression profile;
* family boundary: whether `mark_index_funding_family` should remain combined or split in a later version;
* IR boundary: whether one payload contract is too sparse or too lossy;
* subfamily promotion: whether a recurring submode deserves first-class explicit promotion.

#### E.2 Benchmark classes

The workload set now needs more than latency/storage tests.

Required benchmark classes:

* **storage/runtime fit**

  * scan latency
  * compaction cost
  * bytes on disk
  * replay throughput

* **operator-fit**

  * native-operator coverage ratio
  * operator escape rate
  * need for cross-family ad hoc post-processing

* **semantic-resolution fit**

  * `resolved_singleton` rate
  * `typed_alternatives` concentration
  * `clarification_required` concentration
  * `rejected_unsupported` concentration

* **IR-fit**

  * field occupancy / null sparsity
  * raw-field drop map
  * downstream feature/operator consumption map
  * record-width pressure

* **boundary-stability**

  * anomaly concentration by endpoint or family
  * repeated submode divergence
  * incompatibility between temporal forms inside one family

This is how the system approaches the “optimal semantic IR point” empirically rather than only tuning Parquet layout.

#### E.3 Family split / merge admissibility law

Empirical evidence may motivate boundary change, but it may not enact it silently.

**Family split admissibility**

* requires a `market_data_family_evolution_decision_report@1`,
* requires explicit reasons from operator fit, IR fit, or ambiguity concentration,
* requires new family definitions or new family versions,
* may not silently relabel historical segments,
* requires explicit `migration_equivalence_mode`.

**Family merge admissibility**

* is allowed only when identity law, replay law, transition law, and operator law are congruent enough to justify one shared family;
* otherwise forbidden even if storage performance would improve.

**Subfamily promotion admissibility**

* is allowed when one recurrent submode accumulates distinct invariants, operators, or failure modes;
* promotion creates new explicit subfamily law, not a prose note.

**IR refinement admissibility**

* is allowed only through new versioned payload contracts or family definition versions;
* requires raw-to-IR loss evidence and operator-consumption evidence.

#### E.4 What empirical evidence may do

Empirical evidence may:

* choose a currently preferred carrier profile,
* propose a family split or merge,
* propose subfamily promotion,
* propose IR narrowing/widening,
* justify new placement-basis defaults.

It may not:

* rewrite family law by itself,
* reinterpret historical data without explicit versioned migration semantics,
* promote semantic authority because an optimizer found a faster layout,
* convert derived features into strategy authority,
* turn repeated heuristic success into canonical identity law.

#### E.5 Known watchpoints in the retained family set

The hardened loop should explicitly watch:

* `mark_index_funding_family@1` as the primary future split candidate,
* `market_bar_family@1` submodes as a possible future promotion into stronger explicit subfamilies if revision/operator profiles diverge further,
* `derived_feature_family@1` as the primary IR-boundary pressure zone because wide aligned frames can become either too lossy or too bloated.

---

### F. Derived-feature deontic barrier

The retained draft already said features are not automatic strategy authority. The hardening turns that into explicit constitutional law.

#### F.1 Default force profile

Every `derived_feature_family` artifact should default to this force profile:

```json
{
  "runtime_force": "compiled_surface_only",
  "binding_posture": "advisory_only",
  "authority_source_kind": "descriptive_artifact_only_forbidden",
  "promotion_law_posture": "settled_authority_required_before_execution",
  "amendment_entitlement": "not_authorized_by_this_artifact"
}
```

Meaning:

* a feature artifact is a compiled descriptive/advisory surface,
* it is not execution authority,
* it is not canonical family truth,
* it is not identity authority,
* it does not authorize its own promotion.

#### F.2 Hard laws

**Derived-feature non-truth law**
Derived features are not canonical market-data family truth. Canonical truth remains raw capture plus accepted normalized family records.

**Derived-feature non-identity law**
Derived features may not create, alter, or justify `venue_listing_ref`, canonical instrument binding, market kind, unit binding, or construction basis.

**Derived-feature non-execution law**
No derived-feature artifact or feature projection may directly authorize order submission, position mutation, risk-limit override, or strategy execution.

**Force monotonicity law**
A projection or downstream consumer binding may preserve or strengthen an upstream force profile. It may not weaken it.

**No backflow law**
Feature success, backtest convenience, or optimizer performance may not flow backward and rewrite family law, source-binding contracts, or listing identity semantics.

#### F.3 Projection posture

`market_data_projection_manifest@1` must now declare its authority posture explicitly.

For any projection whose upstream source includes `derived_feature_family`:

* default `binding_posture` is `advisory_only`,
* default `authority_source_kind` is `descriptive_artifact_only_forbidden`,
* default `promotion_law_posture` is `settled_authority_required_before_execution`.

A projection may only become execution-relevant if there is a separate `market_data_downstream_consumer_binding@1` or later external normative artifact that strengthens, not weakens, that posture.

#### F.4 Strategy systems

Later strategy systems may consume feature projections, but only as **external consumers** with their own binding artifacts and authority chain.

The substrate therefore remains:

* a market-data substrate,
* a replay/query/feature materialization substrate,
* a projection/serving substrate,

and **not**:

* a strategy engine,
* an order-generation engine,
* a policy-entitlement source.

One additional hardening rule follows for feature-set definitions:

> released v0 feature sets may contain only descriptive, backward-looking, causal features.
> They may not contain imperative columns (`go_long`, `execute_now`, `position_size`) or future-leaking targets.

---

### G. Patch to the existing v0 substrate spec

This is a patch, not a rewrite.

#### G.1 Sections that stand unchanged

The following retained sections stand substantively unchanged:

* **A. Executive verdict** — storage/runtime choice and v0 cut line remain.
* **B. Why existing general-purpose layers are insufficient** — the recursion from PG -> time-series -> market-data family specialization remains correct.
* **D. Selected v0 family registry** — released/deferred family cut line remains unchanged.
* **E. Semantic IR design** — multiple family-local IRs under a common super-grammar remains correct.
* **F. Physical architecture** — raw capture, replay segments, Postgres catalog, DuckDB runtime, immutable segments, compaction model all remain.
* **H. Native operator algebra** — the retained first-class operator surface remains.
* **Most of I. Correctness / determinism / evidence** — canonical IDs, logical hash vs carrier-bytes hash, replay determinism, provenance, compaction evidence remain.
* **Most of K. Roadmap** — the phase order and bounded implementation shape remain.
* **L. Risks and open decisions** — order-book deferral and future split watchpoints remain.

#### G.2 Sections that are amended

**Existing Section C — Constitutional schema-family grammar**
Amend with:

* explicit doctrinal descent under repo-wide schema-family grammar,
* field ownership split: universal / market-data constitutional / family-local / instance-local,
* explicit `occupancy_law`,
* explicit `admissibility_law`,
* explicit `source_binding_basis`,
* explicit `listing_identity_basis`,
* explicit `normalization_state_algebra`,
* explicit carrier-profile non-constitutionality clause,
* explicit descendant binding-frame reuse.

**Existing Section G — Ingestion and normalization semantics**
Amend with:

* a formal **binding/adjudication membrane** before lowering,
* required first-class binding artifacts,
* `market_data_normalization_resolution_record@1`,
* four-state semantic outcome algebra,
* lowering-admissibility rule.

**Existing Section I — Correctness / determinism / evidence model**
Amend with:

* ambiguity register and lowering readiness,
* feature force monotonicity law,
* explicit no-backflow law from derived features,
* benchmark/evolution artifacts as advisory-only unless separately accepted.

**Existing Section J — Repo-native artifact proposal**
Insert the new artifacts from section C:

* source-binding and listing terms artifacts,
* endpoint field mapping contract,
* publication semantics contract,
* unit/multiplier binding,
* normalization resolution record,
* feature set definition,
* downstream consumer binding,
* IR-boundary review,
* family evolution decision report.

**Existing Section K — Bounded implementation roadmap**
The roadmap shape stays the same, but three concrete insertions are required.

#### G.3 Roadmap deltas

Insert these deltas into the retained roadmap.

**Before Phase 2 raw capture work:**
Add a control-plane binding package or module set for:

* `market_data_source_binding_contract`
* `market_identity_binding`
* `market_venue_listing_terms`
* `market_endpoint_field_mapping_contract`
* `market_publication_semantics_contract`
* `market_unit_multiplier_binding`
* `market_data_descriptive_normative_binding_frame`

**Before Phase 3 family normalizers:**
Add the normalization membrane and `market_data_normalization_resolution_record@1`.

**Before or alongside feature materialization:**
Add `market_data_feature_set_definition@1`, repaired `projection_manifest`, and `market_data_downstream_consumer_binding@1`.

**During benchmark phase:**
Extend benchmark runners to support:

* `candidate_point_kind`
* IR-boundary reviews
* family-evolution decision reports

#### G.4 New mandatory tests

Add these to the retained test plan:

* reject any normalization path that lowers without `source_binding_contract_ref`,
* reject listing identity resolution from raw symbol alone,
* reject missing unit/multiplier binding when the family requires it,
* fixture-test all four normalization outcome states,
* reject projection manifests that weaken upstream feature force profile,
* reject downstream strategy consumer bindings without separate normative authority,
* reject benchmark decision artifacts that claim amendment entitlement.

---

### H. Final hardened v0 position

The hardened v0 position is:

> Build the retained thin-stack crypto market-data substrate exactly as planned, but make it a clearly descended ADEU domain-family cluster rather than a domain constitution floating beside the repo-wide authoring laws.

That means:

* keep the current carrier profile and family cut line,
* make source binding, listing semantics, endpoint mapping, publication semantics, and units first-class artifacts,
* make normalization fail closed under a four-state semantic outcome algebra,
* let empirical work refine family boundaries and IR cuts through explicit advisory decision artifacts,
* and keep derived features permanently behind a monotone descriptive/advisory barrier unless a separate normative authority chain is attached downstream.

In practical build terms, the next cycle should not start by changing storage engines. It should start by adding the missing binding contracts, normalization-resolution artifacts, and feature authority barriers that make the already-good substrate architecture fully native to the newer ADEU schema-family and binding formalization line.
