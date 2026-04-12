### A. Executive verdict

The right bounded v0 is **not** a new general database kernel and **not** a generic time-series schema over a familiar engine.

The right bounded v0 is a **market-data schema-family substrate** with four custom layers over commodity primitives:

1. a **constitutional market-data family grammar**,
2. a **small released family registry** for the first useful crypto families,
3. a **deterministic raw-capture -> normalization -> immutable segment pipeline**,
4. a **family-aware query and replay runtime** over a hybrid carrier stack.

The best v0 stack is:

* **raw source truth:** immutable `jsonl.zst` capture segments,
* **normalized query carrier:** immutable family-local `Parquet` replay segments,
* **metadata and control plane:** `Postgres`,
* **historical query/runtime:** `DuckDB`,
* **custom domain layer:** family registry, instance manifests, normalization law, canonical hashing, replay law, compaction law, feature derivation law, and native operator lowering.

That makes v0 a **dedicated market-data substrate** rather than “use Timescale” or “store Parquet files.”

The released v0 family set should be:

* `trade_event_family@1`
* `market_bar_family@1`
* `mark_index_funding_family@1`
* `open_interest_family@1`
* `derived_feature_family@1` restricted to **bar-aligned causal feature frames**

The following should be **specified now but deferred from released core v0**:

* `orderbook_delta_family@1`
* `orderbook_snapshot_family@1`
* `liquidation_event_family@1`

For those deferred families, v0 still captures raw source packets and keeps future reconstruction admissible, but does not pretend that the first release already has lawful book-reconstruction semantics.

So the substrate is:

```text
market-data family compiler
+ raw capture ledger
+ deterministic normalizer
+ immutable segment store
+ family-aware operator runtime
+ ADEU-style registry / manifest / evidence surfaces
```

It is not:

```text
one universal schema
or one generic SQL table design
or a lakehouse with renamed folders
or a full custom engine before the laws are stable
or a released order-book kernel in v0
```

---

### B. Why existing general-purpose layers are insufficient

Plain relational storage is too general because it treats domain law as application convention. A trade, a bar, a funding interval, and an order book delta all become “rows with timestamps.” That representation is admissible as a carrier, but it does not express the governing laws of those objects.

Time-series systems improve one level. They specialize for time partitioning, range scans, retention, compression, and some window operations. That is the same move Timescale makes relative to plain PostgreSQL: one useful narrowing step. But “time-indexed data” is still too broad for crypto market structure.

Crypto market data is not one family. It contains at least these distinct native object kinds:

* point execution events,
* interval aggregates,
* sampled reference states,
* state-transition logs,
* snapshot states,
* derived aligned feature frames.

Those families differ in all the important ways that drive architecture:

* identity axes,
* admissible replay order,
* mutation profile,
* compaction law,
* lawful rollup law,
* operator algebra,
* error modes,
* provenance burden,
* query shape.

A candle stream is not just “time series.” It has slot identity, closure law, revision law, and a specific rollup algebra. A trade stream is not just “events over time.” It has duplicate policy, semantic keys, aggressor-side semantics, and aggregation operators. Funding is not just a point sample; it often binds an interval of effect. Order book deltas are not just events; they are replay-sensitive state transitions.

So the recursion is:

```text
generic relational grammar
    -> time-index specialization
        -> market-data family grammar
            -> subfamily specialization
```

Examples of the final step matter:

* `market_bar_family` splits into at least:

  * `exchange_published_bar`
  * `trade_compiled_bar`
* `mark_index_funding_family` already contains both:

  * point samples
  * interval-assigned rates
* `derived_feature_family` should split between:

  * bar-aligned causal frames in v0
  * event-aligned microstructure frames later
* `orderbook_delta_family` will likely split by:

  * source diff semantics
  * depth scope
  * checkpoint policy

So the object to build is not “a table design.” It is a **schema-family system** whose laws are stronger than generic storage, but thinner than a speculative full database kernel.

---

### C. Constitutional schema-family grammar

The substrate needs five layers kept separate.

**Universal storage grammar.** This is the domain-agnostic substrate for immutable raw segments, immutable normalized segments, manifests, compaction records, query plans, provenance, and benchmark records. It says nothing about what a trade or bar means.

**Market-data schema-family grammar.** This is the meta-meta-schema every family must satisfy. It defines what fields and laws a lawful family must declare.

**Family instantiation.** This binds a family to a concrete coverage scope such as venue listing, interval, metric kind, or feature set.

**Carrier selection.** This chooses a physical layout profile for an instance. It may be benchmark-driven. It may not rewrite semantic identity.

**Derived operator surface.** This is the named algebra the runtime exposes and compiles. It is not “whatever SQL happens to run.”

#### C.1 Constitutional row for a family definition

```json
{
  "schema": "market_data_family_definition@1",
  "family_name": "string",
  "family_version": "integer",
  "release_status": "draft | released_v0_core | specified_deferred",
  "world_object_kind": "string",

  "coverage_scope_axes": ["..."],
  "identity_axes": ["..."],

  "family_selection_basis": {
    "admissible_binders": ["adapter_endpoint_kind", "identity_binding_ref", "..."],
    "raw_value_only_forbidden": true
  },

  "force_profile": {
    "storage_conformance_force": "mandatory_for_conforming_runtime",
    "operator_conformance_force": "mandatory_for_named_native_operators",
    "semantic_use_force": "descriptive_only_unless_separately_bound",
    "governance_change_force": "separate_lock_required",
    "strategy_use_force": "external_policy_required"
  },

  "temporal_indexing_model": "point_event | interval_slot | point_sample | aligned_grid | checkpoint_delta",
  "replay_model": "canonical_event_order | slot_revision_chain | asof_state_sample | aligned_frame_sequence | snapshot_delta_reconstruction",

  "placement_basis": {
    "partition_axes": ["..."],
    "sort_axes": ["..."],
    "segment_span_policy": "time | rows | hybrid",
    "segment_target_profile": {
      "target_rows": "integer|null",
      "target_duration": "string|null"
    }
  },

  "normalized_carrier": {
    "carrier_class": "append_log_columnar_segment | interval_bucket_columnar_segment | state_sample_columnar_segment | aligned_frame_columnar_segment | checkpoint_delta_segment",
    "backing_profile": "parquet_segments + postgres_catalog + duckdb_runtime",
    "raw_capture_dependency": "required"
  },

  "native_invariants": ["..."],
  "dominant_operator_algebra": ["..."],
  "mutation_profile": "append_only_deduplicated | slot_revision_chain | append_with_conflict_flag | immutable_derived_projection | checkpoint_delta",

  "transition_law": ["..."],
  "compaction_law": ["..."],
  "rollup_resampling_law": ["..."],

  "evidence_requirements": ["..."],
  "descriptive_vs_normative_binding": {
    "descriptive_inputs": ["..."],
    "compiled_outputs": ["..."],
    "normative_promotions_require": ["..."],
    "forbidden_promotions": ["..."]
  },

  "projection_targets": ["..."],
  "failure_modes": ["..."],

  "benchmark_workload_classes": ["..."],
  "family_payload_contract": { "...": "family-local" },
  "subfamily_modes": ["..."]
}
```

#### C.2 Meaning of the constitutional fields

**`world_object_kind`** is the semantic kind, not a storage guess. Examples: `market_trade_execution_event`, `market_interval_aggregate`, `reference_metric_observation`, `open_interest_state_sample`.

**`coverage_scope_axes`** define what dimensions an instance may bind. Examples: venue listing, interval, metric kind, feature set, depth scope.

**`identity_axes`** define lawful uniqueness. These are semantic axes, not file paths.

**`family_selection_basis`** defines admissible binders for assigning source data to the family. This is where the system forbids the category error of inferring semantic family from raw values alone.

**`force_profile`** says what kind of force the family definition has. In v0, family law is operationally mandatory inside the substrate but descriptive facts remain descriptive facts; strategic authority is never smuggled in.

**`placement_basis`** is the physical routing and pruning basis. It is compiled from family law and workload evidence. It is not the family’s semantic identity.

**`normalized_carrier`** is a carrier class, not a database product name. In v0 the concrete backing profile is fixed to Parquet segments plus Postgres metadata plus DuckDB query runtime.

**`dominant_operator_algebra`** says which verbs are first-class and semantically law-bearing for the family.

**`mutation_profile`** says whether the family is append-only, revision-chained, conflict-flagged, or immutable derived output.

**`transition_law`** is the lawful state evolution of records or slots.

**`compaction_law`** states what carrier rewrites preserve semantic equivalence.

**`rollup_resampling_law`** states what higher-level aggregations are lawful and under which completeness conditions.

**`descriptive_vs_normative_binding`** hard-codes the barrier between observed facts, compiled surfaces, and governance authority.

#### C.3 Constitutional laws

1. **Family assignment law.** A record may be assigned to a family only by explicit source binding, instance manifest, or explicit derivation spec. Raw-value-only family inference is forbidden.

2. **Identity law.** Every normalized record must bind a `venue_listing_ref`. Cross-venue canonical instrument identity is optional and separately bound; symbol-string coincidence is never enough.

3. **Carrier separation law.** Carrier choice may change file layout, compression, segment span, and row-group policy. It may not change family identity, semantic keys, or native invariants.

4. **Raw truth law.** Raw capture is immutable and remains replay authority. Normalized segments are query authority but must be reproducible from raw capture plus accepted bindings and compiler version.

5. **Compaction law.** Compaction may only perform transformations named in the family’s `compaction_law` and must emit explicit equivalence evidence.

6. **Derivation law.** Any derived output must bind exact input refs, derivation spec hash, causal boundary, alignment law, and projection target. Hidden feature generation is forbidden.

7. **Promotion law.** Benchmark results, optimizer hints, and anomaly heuristics may inform carrier selection and review. They may not mint semantic identity, canonical instrument equivalence, or strategy authority.

8. **Projection law.** SQL, Arrow frames, and downstream views are projections. They are not the authoritative semantic layer; the authoritative semantic layer is the accepted family law plus the normalized record set and its manifests.

---

### D. Selected v0 family registry

#### D.1 Registry cut line

Released in core v0:

```text
trade_event_family@1
market_bar_family@1
mark_index_funding_family@1
open_interest_family@1
derived_feature_family@1
```

Specified now but deferred from released v0 core:

```text
orderbook_delta_family@1
orderbook_snapshot_family@1
liquidation_event_family@1
```

That cut line is deliberate.

Bars, trades, reference metrics, open interest, and aligned derived features deliver immediate research and operator value with bounded semantics, manageable replay law, and tractable storage profiles.

Order book families do not fail because they are unimportant. They fail the bounded-v0 test because they impose the hardest combination of:

* sequence-sensitive replay,
* snapshot bootstrap law,
* gap reconciliation,
* very high ingest volume,
* venue-specific semantics,
* expensive correctness burden.

Liquidations are simpler than order books, but they are still less foundational than trades/bars/reference/OI for the first release and have highly exchange-specific publication semantics.

#### D.2 `trade_event_family@1`

**What it models.** One observed execution event published by a venue or historical endpoint for one venue listing. It is not order intent, not quote change, and not a synthetic aggregation.

**Native identity axes.** `venue_listing_ref`, `semantic_trade_key`, `event_time_ns`. The `semantic_trade_key` is sourced from explicit exchange identity when present, otherwise from a stable packet-position fallback declared by the adapter contract.

**Native invariants.** Price and quantity must be positive. Side semantics must be explicit as `aggressor_side`, `maker_side`, or `unknown`; they may not be guessed from price motion. Exact duplicates are deduplicable. Divergent duplicates sharing the same semantic key are a conflict anomaly, not silent overwrite.

**Native operators.** Time-range tape retrieval, time-bucket aggregation, VWAP, signed volume, notional flow, trade count, rolling trade imbalance, replay slices.

**Native replay semantics.** `canonical_event_order`, with replay key:
`(event_time_ns, source_sequence_if_any, capture_packet_ref, packet_ordinal)`.

**Appropriate carrier choice.** `append_log_columnar_segment` backed by Parquet. Data shape is narrow, high-volume, append-heavy, range-scanned, and commonly bucketed by time. Compaction is sort-and-dedupe, not aggregation.

**What is explicitly bound vs inferred.** Explicitly bound: venue listing, market kind, source trade-id field mapping, side field semantics, adapter binding, source endpoint. Inferred: segment size, row group size, compression profile. Not inferable: trade identity from price/qty alone, aggressor side from value behavior alone.

**First-class queries.** `trades.range`, `trades.aggregate`, `trades.vwap`, `trades.imbalance`, `replay.slice`.

**Lawful transitions and compactions.** No semantic revisions are normal. Lawful compactions are exact-duplicate collapse, sort stabilization, and segment merge. Aggregating trades into bars is a projection, not canonical trade compaction.

**Downstream projections.** Trade-compiled bars, rolling trade features, research frames, execution-side recent tape views.

#### D.3 `market_bar_family@1`

**What it models.** One interval-bounded aggregate for one venue listing and one interval. This family has two released submodes: `exchange_published_bar` and `trade_compiled_bar`.

**Native identity axes.** `venue_listing_ref`, `interval_ref`, `interval_start_ns`, `construction_basis`, `revision_seq`. The semantic slot identity is the same tuple without `revision_seq`.

**Native invariants.** `interval_end_ns_exclusive = interval_start_ns + interval`. `low <= min(open, close) <= max(open, close) <= high`. Volume fields are nonnegative. `construction_basis` is explicit and cannot be inferred. Official exchange bars and trade-compiled bars are different submodes even when values match.

**Native operators.** Range retrieval by venue listing and interval, integer-multiple rollup, causal rolling windows, returns, ATR-like transforms, gap detection, revision inspection.

**Native replay semantics.** `slot_revision_chain`. Default projection is “latest final revision for each slot”; explicit queries may request provisional or historical revisions.

**Appropriate carrier choice.** `interval_bucket_columnar_segment`. Data shape is moderate volume, highly regular, mostly queried by contiguous ranges and windows, and usually partitioned by listing plus interval plus day.

**What is explicitly bound vs inferred.** Explicitly bound: interval, slot boundaries, construction basis, source priority policy, source endpoint kind, revision law. Inferred: segment span and compaction grouping. Not inferable: whether a bar is official or compiled; whether a late value is a correction or a source conflict.

**First-class queries.** `bars.range`, `bars.rollup`, `bars.window`, `bars.gaps`, `bars.revisions`.

**Lawful transitions and compactions.**

* `forming -> closed`
* `forming -> superseded`
* `closed -> corrected_closed` only under explicit higher-rank source or declared recompilation path
* `corrected_closed -> superseded` only when another correction is explicitly accepted

Canonical compaction preserves the full revision chain. A latest-only serving projection may collapse to one row per slot, but that is a projection target with its own manifest, not the source-of-truth segment rewrite.

**Downstream projections.** Research bar views, feature-input grids, higher-interval rollups, recent-bar execution views.

#### D.4 `mark_index_funding_family@1`

**What it models.** Venue-published reference values used in derivatives and perp markets: `mark_price`, `index_price`, `premium_index`, `funding_rate`, `predicted_funding_rate`. Computed basis belongs in the derived feature family unless the venue explicitly publishes basis as a source metric.

**Native identity axes.**

* Point metrics: `venue_listing_ref`, `metric_kind`, `sample_time_ns`
* Interval-bound rates: `venue_listing_ref`, `metric_kind`, `applies_from_ns`, `applies_until_ns`

**Native invariants.** `metric_kind` is explicit. Units are explicit. Funding interval boundaries are explicit when relevant. A point sample and an interval-assigned rate are not interchangeable. Basis is not silently admitted under this family.

**Native operators.** As-of joins to bar or feature grids, funding-window retrieval, staleness-aware latest lookup, mark-vs-index alignment.

**Native replay semantics.** Mostly `asof_state_sample`, with interval-assigned rows treated as active over a declared time range.

**Appropriate carrier choice.** `state_sample_columnar_segment`. The family is low-to-moderate volume, queried by time range and as-of alignment, and benefits from narrow columnar storage.

**What is explicitly bound vs inferred.** Explicitly bound: metric kind, unit kind, rate semantics, interval semantics, listing ref. Inferred: placement granularity and row-group profile only.

**First-class queries.** `reference.range`, `reference.asof`, `reference.funding_windows`, `reference.join_to_grid`.

**Lawful transitions and compactions.** Exact duplicate collapse and sort stabilization are lawful. Downsampling is a projection, not canonical compaction. Divergent duplicates at the same semantic key are anomaly records.

**Downstream projections.** Funding/mark/index research views, basis and carry feature inputs, recent reference-state execution reads.

#### D.5 `open_interest_family@1`

**What it models.** Sampled open-interest state for one venue listing.

**Native identity axes.** `venue_listing_ref`, `sample_time_ns`, `unit_kind`.

**Native invariants.** Value must be nonnegative. `unit_kind` is explicit: `contracts`, `base_qty`, or `quote_notional`. Contract-size or multiplier binding must exist when interpretation requires it.

**Native operators.** Range retrieval, as-of join to bars or features, delta, rate of change, divergence against price/volume.

**Native replay semantics.** `asof_state_sample`.

**Appropriate carrier choice.** `state_sample_columnar_segment`, for the same reasons as the reference family.

**What is explicitly bound vs inferred.** Explicitly bound: unit kind, multiplier binding, listing ref, source endpoint. Inferred: file layout and compaction profile only.

**First-class queries.** `oi.range`, `oi.asof`, `oi.delta`.

**Lawful transitions and compactions.** Sort stabilization and exact duplicate collapse. Divergent duplicates are preserved with conflict flags.

**Downstream projections.** State views and feature inputs.

#### D.6 `derived_feature_family@1`

**What it models.** Versioned, aligned, causal feature frames built from released source families. In v0 this family is intentionally narrow: one feature frame is aligned to a closed bar grid, and every feature is backward-looking only.

**Native identity axes.** `feature_set_ref`, `venue_listing_ref`, `alignment_interval_ref`, `anchor_time_ns`, `derivation_spec_hash`.

**Native invariants.** Every feature key must be declared in the bound feature spec. Every output row must bind exact input refs or input segment sets, null/warmup policy, and staleness policy for as-of joined inputs. Future-looking labels are not in released v0 core. Feature materialization may not use future data relative to `anchor_time_ns`.

**Native operators.** Materialize, refresh through new derivation refs, range retrieval, frame join on same alignment grid, completeness filtering.

**Native replay semantics.** `aligned_frame_sequence`, with supersession at the derivation level rather than silent overwrite.

**Appropriate carrier choice.** `aligned_frame_columnar_segment`, typically wide rows keyed by anchor time, one feature set per instance.

**What is explicitly bound vs inferred.** Explicitly bound: feature spec, derivation code ref, input family instance refs, alignment basis, causal boundary, as-of staleness thresholds. Inferred: carrier layout only.

**First-class queries.** `features.range`, `features.materialize`, `features.join`, `features.latest`.

**Lawful transitions and compactions.** Outputs are immutable once materialized. Late upstream data creates a new derivation record and a superseding projection, not in-place rewrite. Compaction only merges segments with the same `feature_set_ref` and `derivation_spec_hash`, or builds a latest-only serving projection.

**Downstream projections.** Research/model-input frames and advisory execution read models.

#### D.7 Deferred families

**`orderbook_delta_family@1`.** Models visible-book state transitions. Identity axes include listing ref, depth scope, and source sequence range. Replay model is `snapshot_delta_reconstruction`. Carrier class is `checkpoint_delta_segment`. First-class operators would be `book.at_time`, `depth_ladder`, `spread`, `imbalance`. Deferred because snapshot bootstrap, sequence-gap law, and volume profile are too heavy for v0 core.

**`orderbook_snapshot_family@1`.** Models visible-book snapshots from source or derived reconstruction. Identity axes include listing ref, snapshot time, and depth scope. Deferred because it is downstream of the delta law and cannot be released honestly before the delta/snapshot reconciliation law is frozen.

**`liquidation_event_family@1`.** Models venue-published liquidation events. Deferred because semantics vary across venues and the initial leverage surface is lower than bars/trades/reference/OI. Raw capture still preserves later admission.

---

### E. Semantic IR design

v0 should use **multiple family-local IRs under one common super-grammar**, not one universal record IR.

A single universal row IR would collapse into one of two bad outcomes:

* an optional-field swamp with lost laws,
* or a carrier-driven pseudo-ontology where semantics live outside the IR.

The better object is:

```text
common envelope
+ temporal axes
+ sequence axes
+ lineage bundle
+ quality bundle
+ family-local payload
```

#### E.1 Common super-grammar

```json
{
  "schema": "market_data_record_envelope@1",
  "family_name": "string",
  "family_version": "integer",
  "family_instance_ref": "string",
  "record_id": "string",

  "semantic_key": { "...": "family-local typed object" },
  "temporal_axes": { "...": "point_event | interval_slot | point_sample | aligned_grid" },
  "sequence_axes": { "...": "family-local ordering fields" },

  "lineage": {
    "capture_refs": ["..."],
    "normalization_ref": "string|null",
    "derivation_ref": "string|null",
    "compaction_ref": "string|null"
  },

  "quality_flags": ["..."],
  "payload": { "...": "family-local typed payload" }
}
```

That envelope is **semantic IR**, not a physical table.

Its concrete family-local payload contracts are:

* `trade_event_record@1`
* `market_bar_record@1`
* `mark_index_funding_record@1`
* `open_interest_record@1`
* `derived_feature_frame_row@1`

Deferred:

* `orderbook_delta_record@1`
* `orderbook_snapshot_record@1`
* `liquidation_event_record@1`

#### E.2 Family-local payload shapes

**Trade payload.**

```text
price
quantity
notional(optional, derived deterministically if stored)
aggressor_side_or_unknown
source_trade_id(optional but explicit)
trade_match_semantics
```

**Bar payload.**

```text
interval_ref
interval_start_ns
interval_end_ns_exclusive
construction_basis
revision_seq
bar_status
open high low close
volume_base
volume_quote(optional but explicit if present)
trade_count(optional)
```

**Mark/index/funding payload.**

```text
metric_kind
observation_form(point_sample | interval_assignment)
value
unit_kind
sample_time_ns or applies_from/applies_until
settlement_time_ns(optional)
```

**Open-interest payload.**

```text
value
unit_kind
multiplier_ref(optional but explicit when needed)
sample_time_ns
```

**Derived-feature payload.**

```text
feature_set_ref
feature_values{ declared wide columns }
completeness_flags
warmup_flags
alignment_interval_ref
anchor_time_ns
```

#### E.3 Why this is the least-lossy lawful point

It is least-lossy because:

* raw exchange packets remain preserved separately as immutable source truth,
* family-local semantic structure remains explicit,
* physical carrier details stay below the IR,
* query/runtime operators target family laws directly,
* evidence and lineage are bound into the envelope.

So the IR is not “everything the exchange ever sent.” It is the least-lossy **lawful middle object** between raw source packets and downstream operators, while preserving loss-recovery through raw refs.

---

### F. Physical architecture

#### F.1 Concrete v0 architecture

```text
connector/adapters
    -> raw_capture_segment (.jsonl.zst, immutable)
    -> normalization pipeline
    -> family-local IR rows
    -> replay_segment_writer (.parquet, immutable)
    -> Postgres segment/catalog metadata

query API / operator runtime
    -> planner uses Postgres manifests for pruning
    -> DuckDB scans selected Parquet segments
    -> family-aware operator lowering
    -> result relation / projection manifest

compactor
    -> merges replay segments under family compaction law
    -> emits compaction_record
    -> never mutates raw capture truth

feature materializer
    -> reads bars/trades/reference/OI
    -> materializes derived feature segments
    -> emits derivation_record + projection_manifest
```

#### F.2 Delegated versus custom

**Delegated to existing primitives.**

* Postgres handles transactional metadata, uniqueness constraints, checkpoints, and deployment-friendly control data.
* Parquet handles columnar persistence and compression.
* DuckDB handles local vectorized scans, window execution, joins, and SQL lowering.
* PyArrow handles segment writing.

**Custom in the substrate.**

* Family grammar and registry.
* Family-local IR validators.
* Identity binding law.
* Raw-capture truth model.
* Normalization law.
* Canonical replay keys.
* Logical hashing.
* Compaction equivalence law.
* Feature derivation law.
* Native operator API and lowering.
* Evidence and benchmark artifacts.

That is the correct thin stack for v0.

#### F.3 Durable units

There are three durable units, not one:

**Raw capture segment.** Immutable source packet capture. This is the replay root.

**Replay segment.** Immutable normalized family-local Parquet file. This is the query root.

**Manifest artifact.** Immutable or append-only metadata object in Postgres and optionally exported snapshots. This is the control root.

#### F.4 File and catalog layout

Suggested path layout:

```text
data/raw/<venue>/<source_kind>/<yyyy>/<mm>/<dd>/<hh>/<raw_segment_id>.jsonl.zst
data/replay/<family>/<family_instance_id>/<yyyy>/<mm>/<dd>/<segment_id>.parquet
data/projections/<projection_kind>/<projection_id>/<segment_id>.parquet
```

Suggested Postgres catalog objects:

```text
family_registry_snapshots
family_instances
identity_bindings
raw_capture_segments
replay_segments
compaction_records
derivation_records
projection_manifests
query_plan_records
benchmark_runs
benchmark_decisions
quality_anomalies
```

No canonical market rows live in Postgres tables in v0. Postgres is the control plane, not the data plane.

#### F.5 Write path

1. Adapter receives source data from websocket or REST backfill.
2. Adapter emits raw capture envelopes.
3. Raw envelopes are persisted to immutable raw capture segments.
4. Normalizer reads raw capture envelopes, resolves identity bindings and family instance.
5. Family-local IR rows are produced and validated.
6. Rows are sorted by family replay key, written to immutable Parquet replay segments.
7. Replay segment manifest is committed in Postgres.
8. Optional feature materializers consume replay segments and emit derived segments plus derivation records.

#### F.6 Read path

1. Query API compiles a native operator request.
2. Planner resolves family instance refs and time bounds.
3. Postgres manifest scan prunes candidate segments by partition and min/max time.
4. DuckDB reads the selected Parquet segments.
5. Family-aware SQL/macros/UDFs enforce operator law.
6. Output may remain ephemeral or be materialized as a projection with a projection manifest.

#### F.7 Replay

Replay is always over normalized segments in canonical family order, but replay reproducibility is grounded by raw capture.

* raw capture proves what was observed,
* normalized replay proves how the substrate interpreted it,
* logical hashes prove deterministic equivalence.

#### F.8 Low-latency versus historical

v0 should **unify** low-latency and historical under the same segment model, not split into a second serving database.

The distinction is:

* hot path: smaller, more recent replay segments,
* cold path: compacted larger replay segments,
* optional recent-tail memory cache: later and not semantic.

This keeps the semantic source-of-truth singular.

---

### G. Ingestion and normalization semantics

#### G.1 Pipeline stages

**Stage 1: source capture.** Adapters write raw packets into capture envelopes without semantic promotion.

**Stage 2: capture persistence.** Raw envelopes are durably written before any semantic compaction.

**Stage 3: source binding resolution.** The system resolves adapter endpoint kind, identity binding, and family instance manifest. This is where family assignment occurs.

**Stage 4: canonical normalization.** Raw payloads are mapped into family-local IR rows.

**Stage 5: family-local validation.** Native invariants are checked. Rows may be accepted, accepted-with-flags, or quarantined.

**Stage 6: segment placement.** Accepted rows are routed using family `placement_basis`.

**Stage 7: manifest and evidence emission.** Normalization records, anomaly records, segment manifests, and provenance records are emitted.

#### G.2 Adapters and connectors

v0 should support two adapter classes only:

* `live_stream_connector`
* `historical_backfill_connector`

Both must emit the same raw capture envelope schema so replay and backfill share one ingestion law.

#### G.3 Raw packet capture versus normalized record

The raw packet layer stores:

* exact source bytes or exact source text,
* receive time,
* adapter id and version,
* source stream identity,
* raw payload hash,
* optional decoded envelope hints.

The normalized layer stores:

* family-local semantic payload,
* normalized identity axes,
* replay axes,
* lineage refs,
* quality flags.

The raw layer is not queried as the normal analytics store. The normalized layer is not allowed to erase the raw truth.

#### G.4 Idempotence and replay

Idempotence is handled at two levels.

**Capture idempotence.** Re-ingesting the same raw capture segment must not create a second raw manifest with a different identity.

**Semantic idempotence.** Re-normalizing the same raw capture with the same family definitions and identity bindings must yield the same logical record hashes and segment logical hashes.

#### G.5 Late, duplicate, missing, and out-of-order data

**Duplicates.** Exact semantic duplicates collapse under family law. Divergent duplicates become anomaly records.

**Late arrivals.** Late rows are accepted where the family law allows it and flagged. They do not silently rewrite history.

**Out-of-order packets.** Arrival order is never semantic order. Family replay keys determine canonical order.

**Missing data.** Missingness is family-specific.

* Bars use expected interval grids.
* Reference/OI use declared sampling contracts.
* Trades only have strong gap semantics when source sequence fields exist.

#### G.6 Canonical timestamp policy

All internal times are canonicalized to **UTC int64 nanoseconds**.

Every normalized record binds:

* `capture_time_ns`: local adapter receipt time,
* family-local source time axes:

  * `event_time_ns`,
  * or `sample_time_ns`,
  * or `interval_start_ns` / `interval_end_ns_exclusive`.

There is no single universal timestamp field because that collapses distinct temporal models.

#### G.7 Symbol and venue normalization

v0 must separate:

* `venue_listing_ref`: mandatory, descriptive/compiled from source metadata,
* `canonical_instrument_ref`: optional, separately bound, and not required for core ingest.

This avoids false cross-venue equivalence.

Example:
`BTCUSDT` on a spot market and `BTCUSDT` on a linear perpetual market are different venue listings even when the symbol string matches.

#### G.8 Family selection at ingest time

Family selection must be driven by explicit source bindings such as:

```text
binance.ws.trade          -> trade_event_family
binance.ws.kline.1m       -> market_bar_family (exchange_published_bar, 1m)
binance.rest.klines.1m    -> market_bar_family (exchange_published_bar, 1m)
binance.ws.mark_price     -> mark_index_funding_family (mark_price)
binance.rest.funding      -> mark_index_funding_family (funding_rate)
binance.rest.open_interest -> open_interest_family
```

What is forbidden:

```text
payload has open/high/low/close so assume bar
payload value looks like rate so assume funding
symbol looks like BTCUSDT so assume canonical cross-venue identity
```

#### G.9 Interval and bar closure policy

For `market_bar_family`, the canonical slot key is:

```text
(venue_listing_ref, interval_ref, interval_start_ns, construction_basis)
```

The slot may have multiple revisions.

Rules:

* websocket updates for an open slot emit `forming` revisions,
* final close emits `closed`,
* later accepted correction emits `corrected_closed`,
* superseded revisions are never silently deleted from canonical truth.

Default historical queries return latest final revisions only. Explicit revision queries can surface the full chain.

#### G.10 Order book reconciliation policy

Because order book families are deferred, v0 policy is:

* raw capture of order book streams is mandatory when adapters exist,
* optional experimental reconciliation artifacts may be emitted,
* no released canonical orderbook family rows are admitted in core v0.

The future release gate for order books should require:

* snapshot bootstrap law,
* monotone sequence law,
* explicit gap fail-closed law,
* deterministic reconstruction fixtures,
* storage and replay benchmark evidence.

#### G.11 Schema drift handling

When a source packet shape changes:

* raw capture continues,
* normalization must either adapt through a known adapter version or quarantine the packet,
* unknown field shapes do not silently widen family semantics,
* a `schema_drift_detected` anomaly is emitted.

#### G.12 Evidence emitted during normalization

Every normalization micro-batch should emit:

* one `ingestion_normalization_record`,
* zero or more `quality_anomaly_record`s,
* one or more `replay_segment_manifest`s,
* optional `provenance_record`s for aggregated lineage.

---

### H. Native operator algebra

v0 should expose a **family-aware operator API** that compiles to DuckDB, not “SQL only.”

SQL remains a physical lowering target, not the semantic surface.

#### H.1 First-class operator families

```text
bars.range(instance, t0, t1, state_mode)
bars.rollup(instance, source_interval, target_interval, completeness_mode)
bars.window(instance, kernels, lookback)
bars.gaps(instance, t0, t1)

trades.range(instance, t0, t1)
trades.aggregate(instance, target_interval, kernels)
trades.vwap(instance, lookback)
trades.imbalance(instance, lookback)

reference.range(instance, metric_kind, t0, t1)
reference.asof(instance, metric_kind, anchor_relation, staleness_limit)
reference.funding_windows(instance, t0, t1)

oi.range(instance, t0, t1)
oi.asof(instance, anchor_relation, staleness_limit)
oi.delta(instance, lookback)

join.align_to_bar_grid(bar_instance, right_instances..., join_spec)
join.mark_index_basis(bar_grid, mark_ref, index_ref)
join.funding_carry(bar_grid, funding_ref)
join.oi_price_context(bar_grid, oi_ref)

features.materialize(feature_set, anchor_grid, inputs, t0, t1)
features.range(feature_instance, t0, t1)
features.join(feature_instances...)

replay.slice(family_instance, t0, t1, include_flags)
quality.gaps(family_instance, t0, t1)
```

#### H.2 Primitive kernels in v0

The operator kernel boundary should include:

* range scan,
* exact replay ordering,
* integer-multiple interval rollup,
* causal rolling windows,
* lag, difference, ratio,
* rolling sum, mean, min, max, std,
* EMA,
* VWAP,
* ATR over bars,
* as-of join with staleness policy,
* completeness and gap propagation,
* feature materialization over declared specs.

These primitives are enough to compile the usual starter transforms:
returns, log returns, SMA, EMA, rolling volatility, VWAP, ATR, funding carry, mark-index basis, open-interest delta, trade-imbalance-on-bar-grid.

#### H.3 Rollup law boundary

`bars.rollup` is lawful only when:

* target interval is an integer multiple of source interval,
* source bars share construction basis,
* source bars share venue listing,
* completeness mode is explicit.

Canonical OHLCV rollup:

* `open = first(open)`
* `high = max(high)`
* `low = min(low)`
* `close = last(close)`
* additive fields sum
* completeness flag is the conjunction of source completeness

#### H.4 As-of join law boundary

As-of join requires:

* explicit anchor relation,
* explicit staleness threshold,
* explicit tie-break policy,
* null-or-flag behavior when stale or missing.

This is first-class because mark/index/OI/funding joins are native market-data behavior, not incidental SQL.

#### H.5 What stays outside v0

Not first-class in v0:

* full order book reconstruction,
* queue-position models,
* arbitrary user code inside the runtime,
* full technical-indicator catalog,
* strategy DSL,
* backtesting engine,
* execution simulation,
* label/target generation with future leakage,
* portfolio and PnL semantics.

Those can sit downstream of projections or arrive in later families.

---

### I. Correctness / determinism / evidence model

#### I.1 Canonical ids

Every major object gets a canonical content-derived id:

* `family_registry_id`
* `family_definition_id`
* `family_instance_id`
* `raw_capture_segment_id`
* `replay_segment_id`
* `compaction_record_id`
* `derivation_record_id`
* `projection_manifest_id`
* `benchmark_run_id`
* `benchmark_decision_id`

For normalized records:

* `record_id` is content-derived from family identity plus semantic payload identity,
* bars additionally distinguish `slot_key` and `revision_seq`.

#### I.2 Canonical serialization and hashing

Use two hashes for segments:

**Logical hash.** Authoritative for semantic equivalence.

```text
record_logical_hash = sha256(canonical_json(record_without_nonsemantic_fields))
segment_logical_hash = sha256(concat(record_logical_hashes_in_canonical_replay_order))
```

**Carrier bytes hash.** Authoritative for storage integrity only.

```text
carrier_bytes_hash = sha256(file_bytes)
```

This distinction is important because Parquet byte layout can vary without changing the logical row set.

#### I.3 Replay determinism

The required v0 determinism statement is:

> Given the same raw capture segments, family registry snapshot, identity bindings, family instance manifests, and compiler/runtime version, normalization and segmenting must produce the same ordered logical record hashes and the same segment logical hashes.

Compaction determinism is weaker but still explicit:

> Given the same input segments and compaction profile, compaction must produce either identical output carrier bytes or an output whose logical equivalence is proven under the family compaction law.

#### I.4 Provenance model

Provenance must be explicit at the right granularity.

**Direct row provenance** for point observations:

* capture refs,
* packet ordinal,
* adapter version,
* source binding ref.

**Aggregated provenance** for compiled or derived outputs:

* input segment refs,
* time window,
* derivation or aggregation spec hash,
* compiler entrypoint and version.

That distinction prevents row payloads from exploding when one output row depends on many input rows.

#### I.5 Family instantiation evidence

A family instance is not just declared. It must bind evidence for:

* family definition ref,
* identity binding ref,
* admissible source bindings,
* coverage scope values,
* placement plan,
* carrier profile,
* query/read model targets.

#### I.6 Compaction evidence

Every compaction emits:

* input segment refs,
* output segment refs,
* compaction profile ref,
* equivalence mode,
* counts of deduped rows, preserved conflicts, preserved revisions,
* proof that family compaction law was obeyed.

#### I.7 Derivation evidence

Every feature materialization emits:

* feature spec ref,
* derivation code ref,
* input family instance refs,
* input segment refs,
* time range,
* alignment grid,
* causal boundary assertion,
* output segment refs.

#### I.8 Quality anomaly evidence

Quality anomalies should be first-class evidence, not free text. Examples:

* `duplicate_source_identity`
* `conflicting_duplicate`
* `source_sequence_gap_suspected`
* `timestamp_regression`
* `missing_bar_slots`
* `schema_drift_detected`
* `unit_binding_missing`
* `asof_staleness_exceeded`
* `derivation_input_incomplete`

#### I.9 Verification surfaces

v0 should ship these deterministic verification surfaces:

* raw capture segment validator,
* family-local normalization replay validator,
* segment logical-hash recomputation,
* compaction equivalence validator,
* native operator golden-fixture suite,
* feature derivation reproducibility suite,
* benchmark runner with frozen workloads.

#### I.10 Descriptive versus normative binding

This boundary must be explicit.

**Descriptive.**

* raw captures,
* normalized records,
* source timestamps,
* quality anomalies,
* benchmark measurements.

**Inferred.**

* candidate carrier profiles,
* anomaly heuristics,
* partition tuning suggestions.

**Compiled.**

* family instance manifests,
* query plans,
* projection manifests,
* feature derivation records,
* preferred latest projections.

**Normative / governed.**

* accepting a family definition into released registry,
* accepting cross-venue canonical instrument bindings,
* admitting a feature spec as released,
* accepting a benchmark decision as deployment-default profile.

**Advisory only.**

* optimizer recommendations,
* exploratory benchmarks,
* strategy-facing read models unless separately authorized.

Hard prohibitions:

1. Carrier inference may not become semantic identity.
2. Structural typing may not become canonical cross-venue binding.
3. Derived features may not become execution authority.
4. Benchmark outcomes may not rewrite family law.
5. Raw values alone may not choose family membership.

This is the ADEU barrier translated into market data: storage, structure, semantics, and governance remain distinct layers.

---

### J. Repo-native artifact proposal

The repo should add a bounded market-data artifact family with the same general pattern already used elsewhere: schema exports, deterministic ids, reference fixtures, reject fixtures, and evidence-rich manifests.

#### J.1 Constitutional and family-level artifacts

**`market_data_schema_family_registry@1`**
Class: constitutional. Posture: normative.
Purpose: the released registry of market-data families and their status.
Key fields: registry id, constitutional profile ref, family entries, evidence refs, source set hash.

**`market_data_family_definition@1`**
Class: family-level. Posture: normative for accepted families.
Purpose: one family’s constitutional and family-local law.
Key fields: the full grammar from section C.

**`market_data_family_instance_manifest@1`**
Class: runtime/family binding. Posture: compiled.
Purpose: binds one family to one concrete coverage scope and carrier plan.
Key fields: instance id, family ref, coverage scope values, identity binding refs, source binding refs, placement plan, carrier profile, quality policy, projection targets.

**`market_identity_binding_catalog@1`**
Class: family support / binding. Posture: mixed.
Purpose: maps raw venue symbols and listing metadata to `venue_listing_ref`, and optionally to separately accepted `canonical_instrument_ref`.
Key fields: venue id, raw symbol, market kind, listing ref, contract metadata, optional canonical instrument binding, binding posture.

**`market_data_descriptive_normative_binding_frame@1`**
Class: constitutional support. Posture: normative.
Purpose: states how descriptive market artifacts may and may not be promoted to normative use.
Key fields: binding entries, allowed use summaries, forbidden use summaries, promotion law posture, supporting evidence refs.

#### J.2 Runtime and evidence artifacts

**`market_data_raw_capture_segment_manifest@1`**
Class: runtime/evidence. Posture: descriptive.
Purpose: identifies one immutable raw capture segment.
Key fields: raw segment id, venue, source kind, time bounds, row count, raw bytes hash, adapter version, source stream ref.

**`market_data_ingestion_normalization_record@1`**
Class: runtime/evidence. Posture: descriptive/compiled.
Purpose: records one normalization batch.
Key fields: normalization id, raw segment refs, family instance ref, accepted counts, quarantined counts, anomaly counts, compiler version.

**`market_data_replay_segment_manifest@1`**
Class: runtime/evidence. Posture: compiled.
Purpose: identifies one immutable normalized segment.
Key fields: replay segment id, family instance ref, time bounds, row count, logical hash, carrier bytes hash, segment path, sort key profile, lineage refs.

**`market_data_compaction_record@1`**
Class: evidence/runtime. Posture: compiled.
Purpose: records one compaction rewrite and its equivalence claim.
Key fields: compaction id, input segment refs, output segment refs, compaction profile, equivalence mode, law checks.

**`market_data_provenance_record@1`**
Class: evidence. Posture: descriptive/compiled.
Purpose: externalized lineage for subjects whose provenance is larger than a row payload should carry.
Key fields: subject ref, subject kind, lineage edges, supporting refs, hash refs.

**`market_data_quality_anomaly_record@1`**
Class: evidence. Posture: descriptive.
Purpose: typed anomaly surface.
Key fields: anomaly id, anomaly kind, affected refs, severity, evidence refs, resolution posture.

**`market_data_query_plan_record@1`**
Class: runtime/projection. Posture: compiled.
Purpose: records the compiled native operator plan.
Key fields: plan id, operator name, source instance refs, segment selection hash, lowered SQL or operator DAG, planner version, output equivalence mode.

**`market_data_feature_derivation_record@1`**
Class: runtime/evidence. Posture: compiled.
Purpose: records one feature materialization.
Key fields: derivation id, feature set ref, derivation spec hash, input segment refs, anchor grid, output segment refs, causal policy.

**`market_data_projection_manifest@1`**
Class: projection-level. Posture: compiled.
Purpose: maps semantic sources to downstream views, files, and consumer surfaces.
Key fields: projection id, target kind, source refs, output refs, binding posture, consumer class.

#### J.3 Benchmark artifacts

**`market_data_benchmark_run_record@1`**
Class: evidence. Posture: descriptive/compiled.
Purpose: captures one benchmark execution over one candidate point and one workload set.
Key fields: run id, candidate point kind, candidate ref, corpus refs, host class, metrics, correctness status.

**`market_data_benchmark_decision_report@1`**
Class: evidence/governance support. Posture: advisory unless separately accepted.
Purpose: chooses the currently preferred carrier profile or semantic cut among measured candidates.
Key fields: decision id, candidate comparisons, chosen profile, reasons, rejected tradeoffs, authority posture.

#### J.4 Sample skeletons

`market_data_schema_family_registry@1`

```json
{
  "schema": "market_data_schema_family_registry@1",
  "registry_id": "md_registry_...",
  "constitutional_profile_ref": "docs/ARCHITECTURE_MARKET_DATA_SUBSTRATE_v0.md#constitutional-grammar",
  "family_entries": [
    {
      "family_name": "trade_event_family",
      "family_version": 1,
      "release_status": "released_v0_core",
      "family_definition_ref": "md_family_trade_event_..."
    },
    {
      "family_name": "orderbook_delta_family",
      "family_version": 1,
      "release_status": "specified_deferred",
      "family_definition_ref": "md_family_orderbook_delta_..."
    }
  ],
  "evidence_refs": ["..."],
  "source_set_hash": "..."
}
```

`market_data_family_instance_manifest@1`

```json
{
  "schema": "market_data_family_instance_manifest@1",
  "family_instance_id": "md_inst_...",
  "family_ref": "market_bar_family@1",
  "family_definition_ref": "md_family_market_bar_...",
  "coverage_scope": {
    "venue_id": "binance",
    "venue_listing_ref": "binance.linear_perpetual.BTCUSDT",
    "interval_ref": "1m",
    "construction_basis": "exchange_published_bar"
  },
  "identity_binding_refs": {
    "venue_listing_binding_ref": "listing_bind_...",
    "canonical_instrument_ref": null
  },
  "admissible_source_bindings": [
    "binance.ws.kline.1m",
    "binance.rest.klines.1m"
  ],
  "placement_plan": {
    "partition_axes": ["family_instance_id", "utc_day"],
    "sort_axes": ["interval_start_ns", "revision_seq"],
    "segment_span_policy": "time",
    "segment_target_profile": {
      "target_duration": "1d",
      "target_rows": null
    }
  },
  "carrier_profile_ref": "carrier_profile_bar_daily_zstd_rg64k",
  "quality_policy": {
    "duplicate_policy": "keep_revisions_flag_conflicts",
    "late_arrival_policy": "accept_and_flag"
  },
  "projection_targets": ["duckdb_relation", "feature_input_grid"]
}
```

`market_data_replay_segment_manifest@1`

```json
{
  "schema": "market_data_replay_segment_manifest@1",
  "replay_segment_id": "md_seg_...",
  "family_instance_ref": "md_inst_...",
  "segment_path": "data/replay/market_bar_family/md_inst_.../2026/04/12/md_seg_....parquet",
  "min_time_ns": 1712870400000000000,
  "max_time_ns_exclusive": 1712956800000000000,
  "row_count": 1440,
  "logical_hash": "sha256:...",
  "carrier_bytes_hash": "sha256:...",
  "sort_key_profile": ["interval_start_ns", "revision_seq"],
  "lineage": {
    "raw_capture_segment_refs": ["raw_seg_..."],
    "normalization_ref": "norm_..."
  }
}
```

`market_data_feature_derivation_record@1`

```json
{
  "schema": "market_data_feature_derivation_record@1",
  "derivation_id": "featdrv_...",
  "feature_set_ref": "core_perp_bar_features_v1",
  "family_instance_ref": "feature_inst_...",
  "anchor_grid": {
    "base_family_instance_ref": "bar_inst_...",
    "alignment_interval_ref": "1m",
    "anchor_mode": "closed_bar_end"
  },
  "input_segment_refs": ["seg_a", "seg_b", "seg_c"],
  "derivation_spec_hash": "sha256:...",
  "causal_policy": "backward_only",
  "output_segment_refs": ["feat_seg_1", "feat_seg_2"]
}
```

`market_data_benchmark_decision_report@1`

```json
{
  "schema": "market_data_benchmark_decision_report@1",
  "decision_id": "md_bench_decision_...",
  "decision_scope": "trade_event_family carrier profile on host_class_a",
  "candidate_point_kind": "carrier_profile",
  "candidate_refs": [
    "trade_hourly_rg250k_zstd",
    "trade_daily_rg1m_zstd",
    "trade_hourly_rg250k_snappy"
  ],
  "workload_refs": [
    "trade_range_1d",
    "trade_to_bar_1m_1d",
    "replay_slice_hash_recompute"
  ],
  "chosen_candidate_ref": "trade_hourly_rg250k_zstd",
  "reasons": [
    "best latency/storage frontier under correctness equivalence",
    "deterministic replay preserved"
  ],
  "rejected_tradeoffs": [
    "daily partition improved bytes but harmed one-day aggregation latency"
  ],
  "authority_posture": "advisory_until_deployment_acceptance"
}
```

---

### K. Bounded implementation roadmap

#### K.1 What to build first

**Phase 1: schema contracts and registry.**
Create `packages/adeu_market_data/` with:

* schema exports,
* Pydantic models,
* canonical id/hash helpers,
* family registry,
* family definition validators,
* family instance manifest validators,
* identity binding catalog,
* descriptive/normative binding frame.

This phase is done when reference and reject fixtures validate exactly.

**Phase 2: raw capture and metadata plane.**
Build:

* raw capture envelope model,
* raw capture segment writer,
* Postgres catalog migrations,
* raw segment manifest model,
* normalization batch record model.

This phase is done when raw segments can be written, indexed, and replayed deterministically by manifest.

**Phase 3: trade and bar families.**
Implement:

* adapter binding tables for Binance-like trades and klines,
* trade normalizer,
* bar normalizer with revision-chain law,
* replay segment writer,
* segment manifests,
* deterministic re-normalization tests.

This is the first meaningful end-to-end slice.

**Phase 4: query runtime for bars and trades.**
Implement:

* DuckDB manifest pruning,
* `trades.range`, `trades.aggregate`,
* `bars.range`, `bars.rollup`, `bars.window`, `bars.gaps`,
* query plan records,
* golden query fixtures.

**Phase 5: reference metrics and open interest.**
Add:

* mark/index/funding normalizers,
* open-interest normalizer,
* as-of join operators,
* staleness policy handling.

**Phase 6: derived feature family.**
Add:

* feature spec registry,
* feature derivation records,
* causal aligned feature materializer,
* starter feature set:

  * returns,
  * log returns,
  * rolling volatility,
  * EMA,
  * VWAP,
  * ATR,
  * mark-index basis,
  * funding carry,
  * OI delta,
  * trade imbalance on bar grid.

**Phase 7: compaction and benchmark loop.**
Add:

* compaction engine,
* compaction equivalence validator,
* benchmark corpora,
* workload runner,
* decision report emitter.

#### K.2 Repository and module boundaries

Suggested package split:

```text
packages/adeu_market_data/
  schema/
  src/adeu_market_data/
    models.py
    families.py
    bindings.py
    canonicalize.py
    export_schema.py
  tests/

packages/adeu_market_data_runtime/
  src/adeu_market_data_runtime/
    catalog.py
    capture.py
    normalize.py
    segments.py
    compaction.py
    query.py
    operators.py
    cli.py
  tests/

packages/adeu_market_data_benchmarking/
  schema/
  src/adeu_market_data_benchmarking/
    corpora.py
    workloads.py
    runner.py
    decision.py
  tests/
```

This mirrors the repo’s existing package pattern cleanly.

#### K.3 Language and runtime choices

Use Python for v0 implementation:

* Pydantic for artifact and schema models,
* PyArrow for Parquet writing,
* DuckDB Python API for query lowering,
* psycopg for Postgres catalog,
* pytest for fixtures and replay tests.

Do not add Rust or C++ in v0 core unless one specific hotspot is proven by benchmarks. The semantic layer is still the unstable part; optimize after the laws are exercised.

#### K.4 Mandatory tests

The coding agent should not improvise these. They are required.

**Schema and id tests.**

* exported schemas accept reference fixtures,
* reject fixtures fail for the right reason,
* id hashes recompute deterministically.

**Normalization determinism tests.**

* same raw input -> same logical record hashes,
* same raw input -> same segment logical hashes,
* duplicate and out-of-order fixtures behave exactly as specified.

**Family law tests.**

* bar rollup correctness,
* bar revision-chain correctness,
* trade aggregation correctness,
* reference/OI as-of join correctness,
* feature causal-window correctness.

**Compaction tests.**

* compaction preserves logical equivalence,
* superseded bar revisions remain reconstructible or explicitly preserved through manifests.

**Benchmark tests.**

* workload runner emits benchmark run records,
* decision report selects only candidates that passed correctness equivalence.

#### K.5 Acceptance surfaces

v0 is done only when these surfaces exist and pass:

1. released schema family registry and family definitions,
2. reference fixtures for all released artifacts,
3. raw capture -> normalized replay end-to-end for trades and bars,
4. reference metrics and OI normalization end-to-end,
5. native operator suite over DuckDB,
6. derived feature materialization for starter feature set,
7. deterministic replay and logical hash verification,
8. benchmark run records and one benchmark decision report.

#### K.6 Benchmark corpora and gates

Starter corpora:

* **Corpus A:** 30 days BTCUSDT perp plus BTCUSDT spot, with trades, bars, mark/index/funding, OI.
* **Corpus B:** one burst-volatility week with reconnects and out-of-order fixtures.
* **Corpus C:** ETHUSDT equivalents for cross-instance join coverage.
* **Corpus D:** synthetic anomaly corpus with duplicates, gaps, conflicting duplicates, late arrivals, and schema drift.

Starter workloads:

* one-day trade tape range,
* one-day trades -> one-minute bar aggregation,
* ninety-day one-minute bar range and rolling windows,
* ninety-day mark/index/funding/OI as-of joins to one-minute bar grid,
* ninety-day starter feature materialization,
* replay-slice hash recomputation,
* compaction equivalence verification.

Required gates:

* correctness equivalence must pass,
* replay determinism must pass,
* compaction equivalence must pass,
* benchmark decision report must identify a preferred carrier profile for each released family.

Absolute latency thresholds should be attached to a declared benchmark host class in the implementation docs, not invented ad hoc at review time.

#### K.7 What belongs in v0 core, v0.1, and later

**v0 core**

* trade events,
* bars with revision law,
* mark/index/funding,
* open interest,
* bar-aligned causal features,
* raw capture truth,
* replay segments,
* Postgres catalog,
* DuckDB operator runtime,
* benchmark loop.

**v0.1**

* liquidation family,
* more venues,
* better recent-tail serving path,
* expanded feature registry,
* maybe object-store deployment profile.

**Later research**

* orderbook delta family,
* orderbook snapshot family,
* exact snapshot/delta bootstrap law,
* event-aligned microstructure features,
* concurrent serving projections,
* possible specialized hot path or dedicated engine components.

#### K.8 What “done” means for v0

“Done” is not “we stored some candles.”

“Done” means:

* the substrate has an accepted family grammar,
* five core families are released and test-backed,
* raw capture can be normalized deterministically into immutable segments,
* native operators over those families are correct and reproducible,
* derived features are lawful, causal, and evidenced,
* benchmark evidence exists for currently preferred carrier profiles,
* orderbook and liquidation futures remain admissible through preserved raw capture without being overclaimed as released semantics.

---

### L. Risks and open decisions

**1. Cross-venue canonical instrument policy.**
Using `venue_listing_ref` as the hard identity is correct for v0, but research workflows will eventually pressure the system toward cross-venue canonical instruments. That promotion should remain separately governed. The main open decision is when to release a canonical-instrument binding artifact rather than keep it optional.

**2. Combined `mark_index_funding_family` versus future split.**
The combined family is right for bounded v0 because the operator surface is mostly as-of and interval-alignment. If workloads start diverging strongly between point samples and interval-assigned rates, funding should split into its own family in v0.1 or later.

**3. Full bar revision retention cost.**
Keeping the canonical revision chain is semantically correct, but long-lived markets may make storage overhead noticeable. The key open decision is whether canonical truth always retains all revisions or whether older superseded revisions move to a slower archival tier with preserved manifests.

**4. Order book release threshold.**
The main open edge is not storage technology. It is the law: snapshot bootstrap, gap detection, source-sequence semantics, and exact reconstruction fixtures. Order books should not be promoted until that law is explicit and benchmarked.

**5. When the DuckDB historical path stops being enough.**
For single-node research and deterministic replay, DuckDB is the right v0 runtime. If concurrency, serving latency, or multi-tenant access becomes a hard requirement, add a serving projection layer later. Do not let that pressure rewrite the semantic source-of-truth in v0.
