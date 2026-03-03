## ADEU Semantic Compiler (ASC) — High‑Level Design Spec

This spec defines a **deterministic Semantic Compiler** that treats ADEU’s “semantic code” (locked continuations, slice specs, stop‑gate decisions) as the **primary build input**, compiling it into **typed Commitments IR** plus **deterministic checks** and **generated artifacts**.

---

# A) Design principles and invariants

### A.1 Determinism and replayability (hard invariant)

1. **Same repo state + same compiler version + same config ⇒ identical outputs**

   * Identical: Commitments IR bytes, diagnostics (order + codes), artifact bytes, artifact hashes.
2. **Canonical serialization** for *all hashed payloads*:

   * UTF‑8
   * JSON keys sorted lexicographically
   * `separators=(",", ":")`
   * `ensure_ascii=False`
   * No pretty‑print whitespace in hashed payloads
     (Matches existing canonicalization patterns in `apps/api/src/adeu_api/hashing.py` and `packages/urm_runtime/src/urm_runtime/hashing.py`.)
3. **Deterministic ordering** everywhere:

   * Sources discovered in lexicographic path order.
   * Collections normalized to canonical order (e.g., locks, surfaces, evidence).
4. **No hidden non-determinism**:

   * No wall‑clock dependence; any “time” must be explicit input and treated nonsemantic unless explicitly locked.
   * No randomness or UUID generation unless derived from canonical hash inputs.

### A.2 Stable IDs and stable hashes (hard invariant)

We distinguish:

* **Human IDs** (semantic, stable, readable): e.g. `arc:vnext_plus26`, `slice:vnext_plus26:z3`
* **Stable hashes** (deterministic fingerprints): e.g. `module_hash`, `semantic_source_hash`, `artifact_hash`

**Invariant:**

* A module’s “meaning” is represented by its **semantic hash** over normalized semantic blocks (not prose).

### A.3 Fail‑closed behavior (hard invariant)

Any uncertainty produces a deterministic failure:

* Unknown vocabulary item → ERROR.
* Unparseable semantic block → ERROR.
* Duplicate IDs or ambiguous refs → ERROR.
* Surface extraction mismatch (missing file, wrong schema) → ERROR.
* A lock says “freeze” and a delta exists → ERROR.

### A.4 No semantic drift without explicit surfaced changes (hard invariant)

1. **Semantic meaning lives only in explicit semantic blocks** (see B.2).

   * Changes to narrative prose **must not** alter the compiled semantics hash.
2. **Surfaces are first‑class** and must be:

   * Declared or inferred deterministically
   * Snapshotted deterministically
   * Checked against locks (freeze/additive-only/etc.)

### A.5 “Docs/specs are the primary artifact” (hard invariant)

* The compiler treats docs as **source code**.
* Generated artifacts are **derived** and should be re‑generable from the same sources.
* Code is “last mile”: code changes must satisfy compiled commitments and locks.

### A.6 ODEU typing is explicit (hard invariant)

Each commitment is typed into ODEU-like channels:

* **O**: Surfaces / entities / contracts (what exists)
* **D_norm**: Locks / obligations / prohibitions (what must/must not)
* **E**: Evidence requirements + trust metadata (what is known / acceptable proof)
* **U**: Goals / rationale (why)

This is not philosophical decoration; it determines:

* what is checked deterministically,
* what is merely recorded,
* what must be evidenced for stop‑gates.

### A.7 Trust lanes and evidence quality are explicit (hard invariant)

* Evidence records must declare:

  * **TrustLane** (mapping/solver/proof/tooling)
  * **EvidenceType**
  * **EvidenceQualityLevel**
* No “implicit trust” via prose.

---

# B) Component architecture (module boundaries)

## B.1 Proposed new packages

### 1) `packages/adeu_commitments_ir`

**Responsibility:** Typed IR models + schema export (mirrors `adeu_ir`, `adeu_core_ir` patterns).

* `src/adeu_commitments_ir/models.py` (Pydantic v2, `extra="forbid"`, discriminated unions)
* `src/adeu_commitments_ir/ids.py` (stable id helper; may reuse semantics of `adeu_ir.ids.stable_id`)
* `src/adeu_commitments_ir/reason_codes.py` (stable diagnostic codes)
* `src/adeu_commitments_ir/export_schema.py`

  * writes authoritative schema under `packages/adeu_commitments_ir/schema/…`
  * mirrors schema under `spec/…schema.json` (like `adeu_core_ir/export_schema.py`)

### 2) `packages/adeu_semantic_compiler`

**Responsibility:** Compile semantic sources → Commitments IR + artifacts + diagnostics.

* Purely deterministic; no network; no provider calls; no DB writes.

Suggested internal layout:

* `src/adeu_semantic_compiler/source_discovery.py`
* `src/adeu_semantic_compiler/markdown_block_extractor.py`
* `src/adeu_semantic_compiler/normalize.py`
* `src/adeu_semantic_compiler/stdlib_v0.py` (frozen vocabulary + parameter schemas)
* `src/adeu_semantic_compiler/ir_builder.py`
* `src/adeu_semantic_compiler/pass_manager.py`
* `src/adeu_semantic_compiler/passes/`:

  * `parse.py`
  * `normalize.py`
  * `resolve_refs.py`
  * `typecheck.py`
  * `effect_check.py`
  * `surface_snapshot.py`
  * `surface_delta_check.py`
  * `codegen.py`
* `src/adeu_semantic_compiler/surfaces/`:

  * `schema_surface.py` (JSON schema signature extraction)
  * `manifest_surface.py` (fixture manifest signature extraction)
  * `file_surface.py` (byte hashing)
  * `markdown_json_block_surface.py` (extract fenced JSON blocks by schema id)
* `src/adeu_semantic_compiler/artifacts/`:

  * `pr_splits.py`
  * `evidence_manifest.py`
  * `stop_gate_template.py`
  * `surface_snapshot_writer.py`
* `src/adeu_semantic_compiler/diagnostics.py` (stable formatting + deterministic ordering)
* `src/adeu_semantic_compiler/hashing.py` (canonical json + sha256 wrapper)

## B.2 Semantic source format: “Semantic Markdown blocks”

To avoid brittle NLP-style parsing, the compiler only treats certain blocks as semantic:

**Semantic blocks (MVP):**

1. **YAML frontmatter** at top of doc (optional but recommended)
2. **Fenced code blocks** labeled `adeu` (or `adeu.<kind>`), containing YAML or JSON:

   * Example:

     ````
     ```adeu.arc_lock
     schema: adeu.semantic_source.arc_lock@1
     arc_id: vnext_plus26
     ...
     ```
     ````

**Everything else is nonsemantic** (prose/tables are ignored by semantics hash), unless explicitly embedded into semantic blocks.

This single design choice is how we achieve:

* determinism,
* no semantic drift,
* fail‑closed parsing,
* stable hashes.

## B.3 Responsibility map (who does what)

| Component                | Consumes              | Produces                       | Determinism notes                                      |
| ------------------------ | --------------------- | ------------------------------ | ------------------------------------------------------ |
| Source discovery         | repo root, glob rules | ordered `SourceFile[]`         | lexicographic ordering; forbid absolute paths          |
| Markdown block extractor | file bytes            | `RawSemanticBlock[]` + spans   | strict fence parsing (no markdown renderer dependence) |
| Normalizer               | raw blocks            | canonical semantic records     | normalizes IDs, sorting, de-dup                        |
| Stdlib v0                | —                     | vocab + lock parameter schemas | frozen list; unknown = error                           |
| IR builder               | normalized records    | `CommitmentsIR`                | Pydantic validation; `extra="forbid"`                  |
| Pass manager             | IR + repo state       | pass outputs + diagnostics     | ordered passes; pass versioning                        |
| Surface extractors       | repo files            | `SurfaceSnapshot`              | canonical hashing; stable path normalization           |
| Artifact generator       | IR + snapshots        | PR plan, templates, manifests  | deterministic templates + canonical json               |
| Fixture harness          | fixture dirs          | golden equality checks         | like `packages/adeu_kernel/tests/test_fixtures.py`     |

---

# C) Commitments IR (data model)

## C.1 ID conventions

### Canonical “human IDs”

* Arc: `arc:<slug>`
  Example: `arc:vnext_plus26`
* Slice: `slice:<arc_slug>:<slice_slug>`
  Example: `slice:vnext_plus26:z3`
* Stop‑gate: `stop_gate:<arc_slug>`
  Example: `stop_gate:vnext_plus26`
* Surface: `surface:<namespace>.<name>` or reuse existing `surface_id` patterns
  Example: `surface:adeu.tooling.transfer_report_builder_parity`

### Stable hash fields (always sha256 hex)

* `semantic_source_hash`: hash over **only semantic blocks**
* `module_hash`: hash over normalized module payload, excluding nonsemantic fields
* `artifact_hash`: hash over canonical JSON or bytes for artifacts

## C.2 Minimal IR types (MVP)

### Root

`CommitmentsIR` (schema: `adeu.commitments.v0`)

* `schema_version`: `"adeu.commitments.v0"`
* `compiler`: `{ name, version, pass_versions, config_hash }`
* `source_set`: `{ repo_root_rel, files: [ {path, semantic_source_hash, file_hash} ], source_set_hash }`
* `modules`: `Module[]` (discriminated union)
* `surface_decls`: optional global surface declarations (often attached to modules)
* `diagnostics`: optional (or emitted separately as CompileReport)

### Module union

Discriminator: `module_kind`

* `ArcLockModule`
* `SliceSpecModule`
* `StopGateModule`

### Common module fields

* `module_id` (canonical id)
* `module_kind`
* `title`
* `status`: `draft | frozen | superseded`
* `source`: `{ path, span? }`
* `depends_on`: list of `module_id` refs
* `odeu`: `{ O?, D_norm?, E?, U? }` minimal typed summary
* `effects_declared`: `EffectTag[]`
* `locks`: `Lock[]`
* `surfaces`: `SurfaceRef[]`
* `assertions`: `Assertion[]`
* `evidence_requirements`: `EvidenceRequirement[]`
* `module_hash`

### Lock

* `lock_id`
* `kind: LockKind`
* `severity: ERROR|WARN`
* `odeu_channel: "D_norm"`
* `target`: selector (module/surface/effect/path)
* `params`: kind-specific struct (typed)
* `source`: span ref
* `lock_hash`

### SurfaceRef

* `surface_id`
* `kind: SurfaceKind`
* `selector`: (path, symbol, endpoint signature key, schema id, etc.)
* `baseline_ref?` (previous snapshot artifact ref)
* `source`: span ref

### Assertion

* `assertion_id`
* `type: AssertionType`
* `target` (surface/effect/metric/etc.)
* `expected` (value / comparator)
* `required_evidence_types`: `EvidenceType[]`
* `odeu_channel: "E"` (assertion is epistemic: must be proven)

### EvidenceRequirement

* `evidence_id`
* `evidence_type`
* `trust_lane`
* `quality_level`
* `required: bool`
* `satisfy_by`: refs (artifact path, event stream, CI run id, etc.)
* `source`

### Diagnostic record

* `code`
* `severity`
* `message`
* `module_id?`
* `source`: `{ path, span?, block_id? }`
* `details`: structured dict
* `fingerprint`: stable hash of `(code + normalized target + source path + stable selector)`
  (Used for “same error stays same” behavior.)

## C.3 Example snippets (JSON‑ish)

### C.3.1 ArcLock module (sketch)

```json
{
  "module_kind": "arc_lock",
  "module_id": "arc:vnext_plus26",
  "title": "Locked Continuation vNext+26",
  "status": "draft",
  "source": { "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md" },
  "depends_on": ["arc:vnext_plus25", "stop_gate:vnext_plus25"],
  "effects_declared": ["docs_only", "tooling_refactor", "artifact_schema"],
  "locks": [
    {
      "lock_id": "lock:arc:vnext_plus26:forbid_runtime_semantics",
      "kind": "forbid_effect",
      "severity": "ERROR",
      "odeu_channel": "D_norm",
      "target": { "effect": "solver_runtime_semantics" },
      "params": { "rationale": "No solver semantic contract changes in this arc." }
    },
    {
      "lock_id": "lock:arc:vnext_plus26:freeze_hash_profile",
      "kind": "freeze_hash_profile",
      "severity": "ERROR",
      "target": { "profile_id": "canonical_json_sha256.v1" },
      "params": {
        "json": { "sort_keys": true, "separators": [",", ":"], "ensure_ascii": false },
        "hash": "sha256"
      }
    }
  ],
  "surfaces": [
    {
      "surface_id": "surface:apps.api.fixtures.stop_gate.vnext_plus26_manifest",
      "kind": "manifest",
      "selector": { "path": "apps/api/fixtures/stop_gate/vnext_plus26_manifest.json" }
    }
  ],
  "module_hash": "…sha256…"
}
```

### C.3.2 SliceSpec module (sketch)

```json
{
  "module_kind": "slice_spec",
  "module_id": "slice:vnext_plus26:z3",
  "title": "Z3 Stop-Gate Tooling Parity Metrics (v26)",
  "status": "draft",
  "source": { "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md", "span": {"start": 3200, "end": 5200} },
  "depends_on": ["arc:vnext_plus26"],
  "effects_declared": ["artifact_schema", "fixture_surface"],
  "locks": [
    {
      "lock_id": "lock:slice:vnext_plus26:z3:freeze_surface_id_set",
      "kind": "freeze_surface_set",
      "severity": "ERROR",
      "target": { "surface_kind": "stop_gate_surface_id" },
      "params": {
        "allowed": [
          "adeu.tooling.stop_gate_input_model_parity",
          "adeu.tooling.transfer_report_builder_parity"
        ]
      }
    }
  ],
  "assertions": [
    {
      "assertion_id": "assert:slice:vnext_plus26:z3:metrics_thresholds",
      "type": "metric_threshold",
      "target": { "artifact_path": "artifacts/stop_gate/metrics_v26_closeout.json" },
      "expected": {
        "metrics.artifact_stop_gate_input_model_parity_pct": 100.0,
        "metrics.artifact_transfer_report_builder_parity_pct": 100.0
      },
      "required_evidence_types": ["artifact", "fixture_manifest"],
      "odeu_channel": "E"
    }
  ],
  "module_hash": "…sha256…"
}
```

### C.3.3 StopGate module (sketch)

```json
{
  "module_kind": "stop_gate",
  "module_id": "stop_gate:vnext_plus25",
  "title": "Draft Stop-Gate Decision (Post vNext+25)",
  "status": "draft",
  "source": { "path": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS25.md" },
  "depends_on": ["arc:vnext_plus25"],
  "assertions": [
    {
      "assertion_id": "assert:stop_gate:vnext_plus25:all_passed",
      "type": "stop_gate_closeout",
      "target": { "artifact_path": "artifacts/stop_gate/metrics_v25_closeout.json" },
      "expected": { "all_passed": true, "schema": "stop_gate_metrics@1" },
      "required_evidence_types": ["artifact", "ci_run", "git_commit"],
      "odeu_channel": "E"
    }
  ],
  "evidence_requirements": [
    {
      "evidence_id": "evidence:stop_gate:vnext_plus25:ci_run",
      "evidence_type": "ci_run",
      "trust_lane": "tooling_trust",
      "quality_level": "captured",
      "required": true,
      "satisfy_by": { "github_actions_run_id": "22467143669" }
    }
  ],
  "module_hash": "…sha256…"
}
```

### C.3.4 SurfaceSnapshot artifact (sketch)

```json
{
  "schema": "adeu.surface_snapshot@1",
  "snapshot_id": "surface_snapshot:arc:vnext_plus26",
  "source_set_hash": "…sha256…",
  "projection": "surface.signature.v1",
  "surfaces": [
    {
      "surface_id": "surface:apps.api.fixtures.stop_gate.vnext_plus26_manifest",
      "kind": "manifest",
      "selector": { "path": "apps/api/fixtures/stop_gate/vnext_plus26_manifest.json" },
      "signature_hash": "…sha256…",
      "details": { "schema": "stop_gate.vnext_plus26_manifest@1", "manifest_hash": "b842…" }
    }
  ],
  "snapshot_hash": "…sha256…"
}
```

### C.3.5 Diagnostic record (sketch)

```json
{
  "code": "SEMCOMP_SURFACE_SET_VIOLATION",
  "severity": "ERROR",
  "message": "Manifest declares surface_id not permitted by freeze_surface_set lock.",
  "module_id": "slice:vnext_plus26:z3",
  "source": { "path": "apps/api/fixtures/stop_gate/vnext_plus26_manifest.json" },
  "details": {
    "unexpected_surface_ids": ["adeu.tooling.new_surface_x"],
    "allowed_surface_ids": [
      "adeu.tooling.stop_gate_input_model_parity",
      "adeu.tooling.transfer_report_builder_parity"
    ]
  },
  "fingerprint": "…sha256…"
}
```

---

# D) “Stdlib v0” vocabulary (frozen MVP set)

The stdlib is the **only** accepted vocabulary unless the compiler itself is updated. Unknown tokens fail closed.

## D.1 EffectTag (declared effects)

| EffectTag                  | Meaning                                                 | Typical owners                |
| -------------------------- | ------------------------------------------------------- | ----------------------------- |
| `docs_only`                | doc-only change; no code or artifact semantics          | docs/                         |
| `tooling_refactor`         | refactor of tooling paths; behavior must remain stable  | apps/api/scripts, urm_runtime |
| `fixture_surface`          | changes to fixture manifests/payloads                   | apps/api/fixtures             |
| `artifact_schema`          | introduces/changes a versioned artifact contract/schema | spec/, packages/*/schema      |
| `code_public_api`          | changes public API surfaces (endpoints/exports)         | apps/api, packages/*          |
| `solver_runtime_semantics` | changes solver/runtime semantics                        | adeu_kernel, runtime          |
| `policy_enforcement`       | adds/changes enforcement semantics                      | urm_runtime policy            |
| `provider_boundary`        | affects provider clients or provider matrix             | providers, parity fixtures    |
| `data_migration`           | persistent storage/schema changes                       | apps/api/storage              |

## D.2 SurfaceKind

| SurfaceKind           | What is snapshotted                                                    | MVP extraction approach                     |
| --------------------- | ---------------------------------------------------------------------- | ------------------------------------------- |
| `schema`              | JSON schema contracts under `spec/` and `packages/*/schema`            | parse JSON → canonical hash                 |
| `manifest`            | stop‑gate manifests, provider matrices, catalogs                       | parse JSON → canonical hash                 |
| `markdown_json_block` | fenced JSON blocks keyed by `schema` field                             | extract block → parse JSON → canonical hash |
| `api_openapi`         | OpenAPI signature for API endpoints                                    | canonicalize OpenAPI JSON                   |
| `file`                | raw file bytes for “freeze file” locks                                 | sha256(bytes)                               |
| `enum`                | enum label sets (from schema or code)                                  | from schema (MVP)                           |
| `contract`            | arbitrary named signature (hash profile ids, parity projections, etc.) | explicit canonical payload                  |

## D.3 LockKind (frozen MVP set)

Locks are **D_norm** commitments.

| LockKind                      | Semantics                                                     | Target            | Typical violation               |
| ----------------------------- | ------------------------------------------------------------- | ----------------- | ------------------------------- |
| `forbid_effect`               | prohibited effect tag                                         | `EffectTag`       | slice declares forbidden effect |
| `require_effect`              | required effect tag present                                   | `EffectTag`       | slice missing required effect   |
| `freeze_surface_signature`    | surface hash must equal baseline                              | `SurfaceRef`      | surface hash changed            |
| `allow_surface_additive_only` | surface may change only additively (structural rules by kind) | `SurfaceRef`      | breaking schema change          |
| `freeze_surface_set`          | declared set must match exactly                               | list of IDs       | new/removed surface id          |
| `freeze_hash_profile`         | canonicalization/hash profile locked                          | profile id        | hash rules drift                |
| `forbid_io`                   | prohibit specific non-deterministic IO                        | `io_kind`         | wall-clock usage                |
| `require_deterministic_env`   | require env constraints (TZ/LC_ALL)                           | env vars          | missing enforcement             |
| `allowed_write_paths`         | restrict writes during deterministic tooling                  | path list         | writes outside allowlist        |
| `require_evidence`            | evidence must exist with quality/trust                        | evidence selector | missing closeout artifact       |

## D.4 AssertionType + required evidence mapping

Assertions are **E** commitments: something must be provable.

| AssertionType        | Meaning                                  | Required EvidenceType (min)        |
| -------------------- | ---------------------------------------- | ---------------------------------- |
| `metric_threshold`   | metric path meets comparator             | `artifact` + `fixture_manifest`    |
| `hash_parity`        | baseline/candidate hashes equal          | `artifact`                         |
| `schema_valid`       | artifact validates against schema        | `schema` + `artifact`              |
| `surface_unchanged`  | surface signature equals baseline        | `surface_snapshot`                 |
| `no_provider_calls`  | guarded execution did not call providers | `test_log` (or replay attestation) |
| `stop_gate_closeout` | stop‑gate closeout all_passed + valid    | `artifact` + `ci_run`              |

## D.5 EvidenceType, TrustLane, EvidenceQualityLevel

### EvidenceType (minimal, non‑toy)

* `artifact` (repo file, canonical JSON or bytes)
* `schema` (JSON schema)
* `fixture_manifest`
* `fixture_payload`
* `surface_snapshot`
* `ci_run`
* `git_commit`
* `test_log` (deterministic test output captured)

### TrustLane (aligns with existing ADEU language + adds tooling lane)

* `mapping_trust`
* `solver_trust`
* `proof_trust`
* `tooling_trust`

### EvidenceQualityLevel (frozen)

* `claimed` (declared but not verified)
* `captured` (persisted artifact exists and hashes)
* `replayed` (recomputed deterministically in CI and matches)
* `certified` (explicitly approved or signed-off per governance policy)

---

# E) Compiler pipeline (passes)

## E.1 Stage overview

`Discover → Parse → Normalize → ResolveRefs → TypecheckLocks → EffectCheck → SurfaceSnapshot → SurfaceDeltaCheck → Codegen`

Each pass has:

* `pass_id` (stable string)
* `pass_version` (semantic version)
* `input_hash` / `output_hash` (sha256 canonical json)
* Deterministic diagnostics emitted in lexicographic order.

## E.2 Pass contract table

| Pass                  | Inputs               | Outputs                     | Failure conditions (fail‑closed)                            | Hashing strategy                                   |
| --------------------- | -------------------- | --------------------------- | ----------------------------------------------------------- | -------------------------------------------------- |
| `DiscoverSources`     | repo root            | ordered file list           | missing required source roots; absolute paths               | hash of normalized path list + file content hashes |
| `ParseSemanticBlocks` | file bytes           | raw semantic blocks + spans | malformed fenced blocks; unknown block schema               | hash only semantic blocks (not prose)              |
| `Normalize`           | raw blocks           | canonical records           | invalid ids; duplicates; unsorted lists                     | canonical json of normalized records               |
| `BuildIR`             | canonical records    | CommitmentsIR               | Pydantic validation error; extra fields                     | hash of IR excluding nonsemantic fields            |
| `ResolveRefs`         | IR                   | IR + resolved DAG           | missing refs; cycles; invalid dependency ordering           | hash of DAG adjacency list                         |
| `TypecheckLocks`      | IR + stdlib          | IR + typed lock params      | unknown lock kind; wrong params; invalid target kind        | hash of normalized typed locks                     |
| `EffectCheck`         | IR                   | diagnostics                 | declared effects violate locks                              | hash of normalized effect sets                     |
| `SurfaceSnapshot`     | IR + repo files      | SurfaceSnapshot             | missing surface file; schema mismatch; extraction ambiguity | hash of surface signatures                         |
| `SurfaceDeltaCheck`   | snapshot + baselines | diagnostics                 | freeze violated; additive-only violated                     | hash of delta summary                              |
| `Codegen`             | IR + snapshot        | artifacts                   | cannot write; non-deterministic templates detected          | artifact bytes hashed individually                 |

## E.3 Deterministic hashing strategy (explicit)

* Use `sha256(canonical_json(payload))` for JSON artifacts.
* For Markdown artifacts: either

  * hash raw bytes, **or**
  * treat markdown as nonsemantic wrapper around a fenced JSON block and hash that JSON block (preferred for anything used as evidence).
* Each output artifact embeds:

  * `schema` (if JSON)
  * `source_set_hash`
  * `artifact_hash` (self hash with `artifact_hash` field excluded, same pattern as stop‑gate manifests do with `manifest_hash`)

---

# F) Outputs and generated artifacts

## F.1 Canonical output locations (conceptual)

Use a single deterministic root for compiler outputs:

* `artifacts/semantic_compiler/<arc_slug>/…` (machine evidence)
* `docs/generated/semantic_compiler/<arc_slug>/…` (human convenience, non-authoritative unless explicitly locked)

### Generated files (per arc)

1. **Commitments IR**

   * `artifacts/semantic_compiler/<arc_slug>/commitments_ir.json`
2. **Compile report**

   * `artifacts/semantic_compiler/<arc_slug>/compile_report.json`
     (pass hashes, source_set_hash, diagnostics summary)
3. **Diagnostics**

   * `artifacts/semantic_compiler/<arc_slug>/diagnostics.json`
4. **Evidence manifest**

   * `artifacts/semantic_compiler/<arc_slug>/evidence_manifest.json`
5. **Surface snapshot**

   * `artifacts/semantic_compiler/<arc_slug>/surface_snapshot.json`
6. **Surface diff (optional, if baseline exists)**

   * `artifacts/semantic_compiler/<arc_slug>/surface_diff.json`
7. **Stop‑gate template (for next arc closeout)**

   * `artifacts/semantic_compiler/<arc_slug>/stop_gate_template.json`
8. **PR splits (human-readable)**

   * `docs/generated/semantic_compiler/<arc_slug>/PR_SPLITS.md`

## F.2 How artifacts become stop‑gate evidence

* `evidence_manifest.json` enumerates required evidence objects for the arc and slices.
* Stop‑gate tooling can:

  1. Validate that all required evidence exists and hashes match.
  2. Optionally include `semantic_compiler_artifact_hashes` in `stop_gate_metrics@1` as additive keys.
* Stop‑gate decision docs can reference these artifacts explicitly as closeout evidence:

  * analogous to how `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS25.md` references `artifacts/stop_gate/metrics_v25_closeout.json`.

---

# G) Integration with existing ADEU patterns (grounded to repo conventions)

## G.1 Where it lives

* **IR**: `packages/adeu_commitments_ir`
* **Compiler**: `packages/adeu_semantic_compiler`

Rationale:

* Mirrors ADEU’s strong existing separation of “typed IR” vs “deterministic checker/tooling”:

  * `packages/adeu_ir` (IR) + `packages/adeu_kernel` (checker)
  * `packages/adeu_core_ir` (IR) + `packages/urm_runtime` (runtime tooling)
  * This new module parallels that pattern.

## G.2 Align with schema export discipline

Follow `adeu_core_ir/export_schema.py`:

* Authoritative schema in `packages/adeu_commitments_ir/schema/*.json`
* Mirror schema in `spec/adeu_commitments_ir.schema.json`

Add a schema regression test like existing semantic-depth schema tests:

* “schema accepts normalized payload”
* “stdlib mapping in schema matches runtime constants” (optional `x_*` fields)

## G.3 Deterministic, fixture-based tests

Mirror `packages/adeu_kernel/tests/test_fixtures.py`:

* `examples/fixtures/semantic_compiler/<case>/sources/...`
  (small markdown docs with semantic blocks)
* `examples/fixtures/semantic_compiler/<case>/expected/...`

  * `commitments_ir.json`
  * `diagnostics.json`
  * `surface_snapshot.json`
  * `evidence_manifest.json`

Golden test invariant:

* exact JSON equality (`sort_keys=True` canonical output).

## G.4 Optional integration with URM stop‑gate tooling

The compiler can:

* Generate **stop‑gate templates** (thresholds + evidence expectations) that become input for:

  * `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (eventually)
* Provide a shared **surface registry** for Z4‑style “mutable surface snapshot” enforcement.

  * Today Z4 guard hardcodes surface file sets in `apps/api/tests/test_tooling_z4_guards.py`.
  * ASC can generate that list deterministically from the arc locks and surfaces, so the test loads it instead of re‑encoding it.

(Implementation glue is intentionally omitted; this is the conceptual integration point.)

---

# H) MVP → v1 roadmap (thin slices with stop‑gates)

## H.0 v0 — Parse + IR + basic lock checks + basic surface snapshots

**Scope**

* Semantic block extraction (frontmatter + ` ```adeu.* ` blocks).
* Commitments IR models + schema export.
* Passes through `TypecheckLocks` + basic `SurfaceSnapshot` for:

  * `schema`, `manifest`, `file`, `markdown_json_block`

**Done means**

* Deterministic compile of at least one real arc doc (e.g., vNext+26) after minimal semantic blocks are added.
* Golden fixtures passing.
* Fail‑closed on unknown lock/effect/surface kinds.

**Stop‑gate**

* `SEMCOMP_V0_SCHEMA_EXPORT_PARITY`: exported schema matches checked-in `spec/*.json`
* `SEMCOMP_V0_DETERMINISM`: same compile run repeated 3× yields identical hashes.

## H.1 v0.1 — PR split plan generation

**Scope**

* Codegen `PR_SPLITS.md` from slice modules:

  * stable ordering
  * includes declared effects, locked surfaces, required evidence

**Done means**

* PR plan deterministic and stable under no semantic changes.
* PR plan changes only when semantic blocks change.

**Stop‑gate**

* `SEMCOMP_PR_SPLITS_HASH_STABLE` on a frozen fixture case.

## H.2 v0.2 — Stronger surface delta analysis + (bounded) effect inference

**Scope**

* Surface delta checks for:

  * schema: additive-only vs breaking rules (minimal structural heuristics)
  * manifests: allowed set checks, required keys checks
* Optional deterministic effect inference:

  * infer effect tags from changed paths (e.g., touching `apps/api/src` implies `code_public_api` *only if* endpoints changed per OpenAPI snapshot)

**Done means**

* Compiler can deterministically detect:

  * new endpoint added when forbidden
  * schema breaking change under additive-only lock

**Stop‑gate**

* `SEMCOMP_SURFACE_DELTA_BREAKING_DETECTED` fixture where a breaking change is correctly rejected.

## H.3 v1 — Deeper integration (CI + evidence + URM hooks)

**Scope**

* CI job that runs ASC in fail-closed mode on “participating” docs.
* Evidence manifest integrated into stop‑gate tooling as an additive check.
* Optional API endpoint (read-only) returning compiled Commitments IR for a given arc (no UI design here).

**Done means**

* “Locked continuation” docs become **machine-checkable governance contracts**:

  * changes that violate locks are blocked in CI
  * stop‑gate decision evidence can be validated against compiled requirements

**Stop‑gate**

* `SEMCOMP_V1_GOVERNANCE_CONSISTENCY`: arc lock ↔ stop‑gate decision ↔ artifacts are consistent and hashed.

---

# I) Concrete worked example (grounded to repo: `LOCKED_CONTINUATION_vNEXT_PLUS26.md`)

### I.1 Source fragments (assumed minimal semantic blocks)

We *do not* try to compile the prose directly. We embed explicit semantic blocks into the existing doc.

At the top of `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`:

```yaml
---
adeu_semantic: true
schema: adeu.semantic_source.arc_lock@1
module_id: arc:vnext_plus26
title: "Locked Continuation vNext+26"
status: draft
depends_on:
  - arc:vnext_plus25
  - stop_gate:vnext_plus25
effects_declared:
  - docs_only
  - tooling_refactor
  - fixture_surface
  - artifact_schema
global_locks:
  - kind: forbid_effect
    effect: solver_runtime_semantics
    severity: ERROR
  - kind: freeze_hash_profile
    profile_id: canonical_json_sha256.v1
    severity: ERROR
surfaces:
  - surface_id: surface:apps.api.fixtures.stop_gate.vnext_plus26_manifest
    kind: manifest
    selector:
      path: apps/api/fixtures/stop_gate/vnext_plus26_manifest.json
---
```

Under the Z3 section (Stop‑Gate Tooling Parity Metrics), embed a slice block:

````yaml
```adeu.slice_spec
schema: adeu.semantic_source.slice_spec@1
module_id: slice:vnext_plus26:z3
title: "Z3 Stop-Gate Tooling Parity Metrics (v26)"
effects_declared: [fixture_surface, artifact_schema]
locks:
  - kind: freeze_surface_set
    target:
      surface_kind: stop_gate_surface_id
    params:
      allowed:
        - adeu.tooling.stop_gate_input_model_parity
        - adeu.tooling.transfer_report_builder_parity
assertions:
  - type: metric_threshold
    target:
      artifact_path: artifacts/stop_gate/metrics_v26_closeout.json
    expected:
      metrics.artifact_stop_gate_input_model_parity_pct: 100.0
      metrics.artifact_transfer_report_builder_parity_pct: 100.0
evidence_requirements:
  - evidence_type: artifact
    trust_lane: tooling_trust
    quality_level: captured
    required: true
    satisfy_by:
      path: artifacts/stop_gate/metrics_v26_closeout.json
````

````

This is intentionally minimal:
- It encodes the enforceable semantics from the prose locks,
- without requiring the compiler to interpret freeform text.

### I.2 Compiled IR result (sketch)
The compiler emits:
- `artifacts/semantic_compiler/vnext_plus26/commitments_ir.json`
containing `arc:vnext_plus26` and `slice:vnext_plus26:z3` modules, typed and hashed.

Key outputs:
- `module_hash` for `slice:vnext_plus26:z3`
- `surface_snapshot.json` including canonical hash of `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`

### I.3 Example violation and diagnostics

**Violation scenario:** someone edits  
`apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`  
and adds a new `surface_id`:
- `adeu.tooling.new_surface_x`

But `freeze_surface_set` lock allows only:
- `adeu.tooling.stop_gate_input_model_parity`
- `adeu.tooling.transfer_report_builder_parity`

**Compiler behavior (fail‑closed):**
- `SurfaceSnapshot` pass succeeds (it can hash the manifest).
- `SurfaceDeltaCheck` (or manifest semantic validation) fails with:

```json
{
  "code": "SEMCOMP_SURFACE_SET_VIOLATION",
  "severity": "ERROR",
  "message": "Manifest declares surface_id not permitted by freeze_surface_set lock.",
  "module_id": "slice:vnext_plus26:z3",
  "source": { "path": "apps/api/fixtures/stop_gate/vnext_plus26_manifest.json" },
  "details": {
    "unexpected_surface_ids": ["adeu.tooling.new_surface_x"],
    "allowed_surface_ids": [
      "adeu.tooling.stop_gate_input_model_parity",
      "adeu.tooling.transfer_report_builder_parity"
    ]
  },
  "fingerprint": "…stable sha256…"
}
````

**Why this matches ADEU philosophy**

* Deterministic: same edit yields same diagnostic fingerprint.
* Fail‑closed: new surface id is rejected unless the lock is explicitly updated.
* No semantic drift: prose edits elsewhere do not affect the compiled lock.

---

## Closing note: what this achieves

With ASC + Commitments IR:

* ADEU’s “locked continuation” docs become **first-class compile targets**.
* Locks become **typed, checkable deontics** rather than narrative-only contracts.
* Stop‑gates gain explicit **evidence manifests** and surface snapshots that are reproducible and hash‑stable.
* The repo’s existing determinism discipline (canonical hashing, fixtures, stop‑gates) becomes **compiler-enforced**, not merely convention.
