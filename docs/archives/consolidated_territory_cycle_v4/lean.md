A) Repo-grounded inventory

### Key existing artifacts/schemas relevant to ODEU (file paths)

**Authoritative locks + semantics contracts**

* **Latest continuation lock (current arc):** `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`

  * Explicitly locks **SEMANTICS_v3** as authoritative and fixes the **canonical JSON + sha256** profile (`json.dumps(sort_keys=True, separators=(",", ":"), ensure_ascii=False)`), plus the “trust lanes” separation (mapping_trust / solver_trust / proof_trust). (See “A1) Semantics boundary lock”, “A2) Canonical serialization profile & hash lock”, “A4) Trust lanes remain separate”.) `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
* **SEMANTICS v3 contract:** `docs/SEMANTICS_v3.md`

  * Defines the IR-only predicate language (`defined`, `refers_to_doc`, `not`, `and`, `or`), closed-world defaulting, and how exceptions defeat norms/policies in the SMT integration contract. `docs/SEMANTICS_v3.md`
* **Core IR contract freeze (ODEU graph):** `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md`

  * Freezes `adeu_core_ir@0.1` as a **projection artifact**, including the **ODEU layers**, **edge typing matrix**, **canonical node/edge ordering**, and **no-duplicates** constraints. (See sections “A1) Core IR contract freeze”, “A2) Edge typing matrix lock (frozen)”, “A3) Canonical ordering lock”.) `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md`

**ODEU core schema family (contracts in `packages/adeu_core_ir/schema/`)**

* **Core ODEU graph schema:** `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`

  * Defines `CoreONode`, `CoreENode`, `CoreDNode`, `CoreUNode` and `CoreEdge` (edge types include `about`, `defines`, `supports`, `refutes`, `depends_on`, `justifies`, `gates`, `serves_goal`, `prioritizes`, `excepts`). `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`
* **Integrity diagnostics schemas (derived from core IR):**

  * Dangling references: `packages/adeu_core_ir/schema/adeu_integrity_dangling_reference.v0_1.json` `packages/adeu_core_ir/schema/adeu_integrity_dangling_reference.v0_1.json`
  * Cycle policy: `packages/adeu_core_ir/schema/adeu_integrity_cycle_policy.v0_1.json` and extended: `..._extended.v0_1.json` `packages/adeu_core_ir/schema/adeu_integrity_cycle_policy.v0_1.json` `packages/adeu_core_ir/schema/adeu_integrity_cycle_policy_extended.v0_1.json`
  * Deontic conflict: `packages/adeu_core_ir/schema/adeu_integrity_deontic_conflict.v0_1.json` and extended: `..._extended.v0_1.json` `packages/adeu_core_ir/schema/adeu_integrity_deontic_conflict.v0_1.json` `packages/adeu_core_ir/schema/adeu_integrity_deontic_conflict_extended.v0_1.json`
  * Reference-integrity extended: `packages/adeu_core_ir/schema/adeu_integrity_reference_integrity_extended.v0_1.json` `packages/adeu_core_ir/schema/adeu_integrity_reference_integrity_extended.v0_1.json`
* **Lane-level artifacts:** lane report `packages/adeu_core_ir/schema/adeu_lane_report.v0_1.json` and read-surface bundle `packages/adeu_core_ir/schema/adeu_read_surface_payload.v0_1.json` `packages/adeu_core_ir/schema/adeu_lane_report.v0_1.json` `packages/adeu_core_ir/schema/adeu_read_surface_payload.v0_1.json`
* **Newer “evidence / trust / candidate” packet families (explicitly requested):**

  * Normative advice packet: `packages/adeu_core_ir/schema/adeu_normative_advice_packet.v0_1.json` `packages/adeu_core_ir/schema/adeu_normative_advice_packet.v0_1.json`
  * Trust invariant packet: `packages/adeu_core_ir/schema/adeu_trust_invariant_packet.v0_1.json` `packages/adeu_core_ir/schema/adeu_trust_invariant_packet.v0_1.json`
  * Semantics-v4 candidate packet: `packages/adeu_core_ir/schema/adeu_semantics_v4_candidate_packet.v0_1.json` `packages/adeu_core_ir/schema/adeu_semantics_v4_candidate_packet.v0_1.json`

**Cross-IR artifacts requested (“cross_ir”)**

* **NOT FOUND** as JSON schemas under `packages/adeu_core_ir/schema/` (directory listing contains no `cross_ir` schema files). `packages/adeu_core_ir/schema/`
* However, the **contracted schema strings and validators exist in the API layer**:

  * Cross-IR bridge manifest schema/version string: `apps/api/src/adeu_api/cross_ir_bridge_vnext_plus20.py` (e.g., `CROSS_IR_BRIDGE_MANIFEST_SCHEMA = "adeu_cross_ir_bridge_manifest@0.1"`). `apps/api/src/adeu_api/cross_ir_bridge_vnext_plus20.py`
  * Cross-IR coherence diagnostics schema/version string: `apps/api/src/adeu_api/cross_ir_coherence_vnext_plus20.py` (e.g., `CROSS_IR_COHERENCE_DIAGNOSTICS_SCHEMA = "adeu_cross_ir_coherence_diagnostics@0.1"`). `apps/api/src/adeu_api/cross_ir_coherence_vnext_plus20.py`
  * Stop-gate knows these schema names and treats them as frozen surfaces: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (constants `CROSS_IR_BRIDGE_MANIFEST_SCHEMA`, `CROSS_IR_COHERENCE_DIAGNOSTICS_SCHEMA`). `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`

**Concrete ODEU fixture examples**

* A canonical core IR example with sorted nodes/edges and O/E/D/U usage: `apps/api/fixtures/stop_gate/vnext_plus19/core_ir_read_surface_case_a_1.json` (shows `nodes` with layers `O/E/D/U` and edges like `about`, `depends_on`, `justifies`, `serves_goal`, etc.). `apps/api/fixtures/stop_gate/vnext_plus19/core_ir_read_surface_case_a_1.json`

---

### Current Lean footprint and what it already formalizes (file paths)

**Lean library entry + build**

* `packages/adeu_lean/AdeuCore.lean` imports only `AdeuCore.Semantics` and `AdeuCore.Theorems`. `packages/adeu_lean/AdeuCore.lean`
* `packages/adeu_lean/lakefile.lean` defines `lean_lib AdeuCore` and includes `std4` only (no mathlib). `packages/adeu_lean/lakefile.lean`

**Semantics formalization (currently predicate + conflict microkernel)**

* `packages/adeu_lean/AdeuCore/Semantics.lean`

  * Defines `Pred` (`defined`, `refersToDoc`, boolean connectives), evaluation `evalPred`, exception defeat `exceptionDefeatsNorm`, and conflict candidate/soundness predicates (`conflictCandidate`, `conflictSound`). `packages/adeu_lean/AdeuCore/Semantics.lean`
* `packages/adeu_lean/AdeuCore/Theorems.lean`

  * Proves: closed-world missing def is false (`pred_closed_world_missing_false`), exception gating (`exception_gating_false_not_defeat`), and conflict soundness (`conflict_soundness`). `packages/adeu_lean/AdeuCore/Theorems.lean`

**Lean proof runner plumbing (Python)**

* `packages/adeu_lean/src/adeu_lean/runner.py`

  * Builds wrapper theorems that bind `adeuSemanticsVersion_*` and `adeuInputsHash_*`, and proves the selected theorem (e.g., `AdeuCore.Theorems.pred_closed_world_missing_false`). `packages/adeu_lean/src/adeu_lean/runner.py`
* `packages/adeu_lean/src/adeu_lean/models.py`

  * Defines the obligation kinds (`pred_closed_world`, `exception_gating`, `conflict_soundness`) and default semantics version `"adeu.lean.core.v1"`. `packages/adeu_lean/src/adeu_lean/models.py`

**Kernel-side matching implementation of SEMANTICS_v3 predicate semantics**

* Predicate parsing/eval: `packages/adeu_kernel/src/adeu_kernel/predicate.py` (functions `parse_predicate`, `evaluate_predicate`, `PredDefined`, `PredRefersToDoc`, etc.). `packages/adeu_kernel/src/adeu_kernel/predicate.py`
* Assertion naming per SEMANTICS_v3: `packages/adeu_kernel/src/adeu_kernel/checker.py` (`_json_path_hash`, `assertion_name_format = "a:<object_id>:<json_path_hash>"`). `packages/adeu_kernel/src/adeu_kernel/checker.py`
* This is the runtime alignment point with `docs/SEMANTICS_v3.md`. `docs/SEMANTICS_v3.md`

---

### “Canonical IR” boundary: what is already frozen as contracts

**(1) ODEU Core Graph contract (projection)**

* Schema boundary: `adeu_core_ir@0.1` is defined in `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` and re-validated/normalized by Pydantic models in `packages/adeu_core_ir/src/adeu_core_ir/models.py` (`class AdeuCoreIR`, `CoreONode/CoreENode/CoreDNode/CoreUNode`, `CoreEdge`). `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Contract enforcements beyond JSON-schema:

  * Node canonical sort key `(layerOrder, kind, id)` and edge canonical sort key `(type, from_ref, to_ref)` enforced in `AdeuCoreIR._validate_contract`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
  * No duplicate node IDs (`node_ids` set), no duplicate edge identities (`(type, from, to)`), and no dangling edge endpoints (from/to must exist) enforced in the same validator. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
  * Layer/edge discipline is enforced by `_EDGE_TYPING_MATRIX` + `_node_signature` checks (e.g., `"about": from {"E.Claim","E.Assumption","E.Question","D.Norm","D.Policy","U.Goal"} to {"O.Entity","O.Concept","O.RelationType"}`, etc.). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Lock doc explicitly states this is a **projection artifact** and “does not replace `adeu.ir.v0` authority”; it is frozen and non-breaking. `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md`

**(2) SEMANTICS boundary for runtime/solver integration**

* The authoritative semantic contract for predicate evaluation and exception/conflict reasoning is `docs/SEMANTICS_v3.md`, and the newest lock reiterates that SEMANTICS_v3 remains authoritative (no drift) in this arc. `docs/SEMANTICS_v3.md` `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
* Runtime kernel implementation that must not be semantically altered is in `packages/adeu_kernel/src/adeu_kernel/checker.py` + `predicate.py` (assertion naming, predicate parsing/eval). `packages/adeu_kernel/src/adeu_kernel/checker.py` `packages/adeu_kernel/src/adeu_kernel/predicate.py`

**(3) Canonical hashing/serialization profile**

* Lock: canonical serialization + sha256 profile is fixed in `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` (A2). `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
* Implementations:

  * API hashing helper: `apps/api/src/adeu_api/hashing.py` (`canonical_json`, `sha256_text`, `sha256_canonical_json`). `apps/api/src/adeu_api/hashing.py`
  * Runtime hashing helper: `packages/urm_runtime/src/urm_runtime/hashing.py` mirrors the same canonical_json config. `packages/urm_runtime/src/urm_runtime/hashing.py`

---

B) Proposed formalization target (“ODEU Formal Template v0”)

The template goal: **add an independent Lean formal layer** that (1) faithfully models the frozen ODEU contracts, and (2) proves the invariants the repo already enforces—**without requiring any runtime behavior changes** (SEMANTICS_v3 remains authoritative per lock). `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` `docs/SEMANTICS_v3.md`

### Core typed objects to formalize in Lean (repo-aligned)

I recommend a **two-level** modeling approach:

1. **Raw artifact model (“Artifacts layer”)** — a faithful Lean mirror of the JSON contracts
2. **Validated/typed model (“Typed layer”)** — constructed only when the raw model satisfies the frozen contract (so well-typedness holds “by construction”)

This matches how the repo uses Pydantic models as a contract boundary today. `packages/adeu_core_ir/src/adeu_core_ir/models.py`

#### O layer (Ontology) — entities, concepts, relation types

* **Raw node shape** should match:

  * `$defs.CoreONode` with `layer: "O"`, `kind ∈ {"Entity","Concept","RelationType"}`, and fields `id`, `label`, optional `aliases`. `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` `packages/adeu_core_ir/src/adeu_core_ir/models.py` (see `OKind`, `CoreONode`)
* Lean object set (Artifacts):

  * `structure CoreONode := (id : String) (kind : OKind) (label : String) (aliases : List String)` mirroring `CoreONode` fields. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Typed layer:

  * `ORef` as a typed reference to an O-node ID, only constructible if the ID exists in the validated graph (avoids dangling refs). This directly targets the runtime contract “edge references must resolve to nodes” in `AdeuCoreIR._validate_contract`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`

#### D layer (Deontics) — norms/policies/exceptions, modality typing

* **Raw node shape** should match:

  * `$defs.CoreDNode` with `layer: "D"`, `kind ∈ {"PhysicalConstraint","Norm","Policy","Exception"}`, optional `modality ∈ {"obligatory","forbidden","permitted"}`, optional `condition`, `target`, `priority`, etc. `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` `packages/adeu_core_ir/src/adeu_core_ir/models.py` (see `DKind`, `CoreDNode`)
* Deontic semantics lock (predicate/exception/conflict) remains SEMANTICS_v3 and is already formalized in Lean as `AdeuCore.Semantics` (Pred / exceptionDefeatsNorm / conflictCandidate). `docs/SEMANTICS_v3.md` `packages/adeu_lean/AdeuCore/Semantics.lean`
* Typed layer recommendations:

  * Keep `CoreDNode.condition : Option String` as-is (because core IR’s integrity conflict logic currently treats it as normalizable text, not a parsed predicate). `packages/adeu_core_ir/src/adeu_core_ir/integrity_deontic_conflict.py` (see `_normalize_condition`)
  * Add an **optional interpreted view**:

    * `inductive DCondition | text (s:String) | pred (p: AdeuCore.Pred)`
      This allows future evidence-only parsing while not changing the raw contract. Predicate language and parser exist in runtime already (`parse_predicate`), and Lean already has `Pred`. `packages/adeu_kernel/src/adeu_kernel/predicate.py` `packages/adeu_lean/AdeuCore/Semantics.lean`

#### E layer (Epistemics) — claims/assumptions/evidence/question + evidence ledger

* **Raw node shape** should match:

  * `$defs.CoreENode` with `kind ∈ {"Claim","Assumption","Question","Evidence"}`, `text`, `spans : list[SourceSpan]`, optional `confidence`, and **SBR ledger fields** (`ledger_version`, `S_milli`, `B_milli`, `R_milli`, and display `S/B/R`). `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` `packages/adeu_core_ir/src/adeu_core_ir/models.py` (see `EKind`, `CoreENode._validate_ledger_fields`)
* SBR scoring algorithm is explicit in code:

  * `packages/adeu_core_ir/src/adeu_core_ir/ledger.py` (`apply_claim_ledger_scores`, `clamp_milli`, etc.) `packages/adeu_core_ir/src/adeu_core_ir/ledger.py`
* Typed layer:

  * `SourceSpan` as `{start : Nat, end_ : Nat}` plus invariant `start < end` (matches `adeu_ir.models.SourceSpan` constraints `start>=0`, `end>0`, and validator requiring `start < end`). `packages/adeu_ir/src/adeu_ir/models.py` (class `SourceSpan`)
  * `SBR` record ensuring bounds (`0 ≤ *_milli ≤ 1000`) consistent with `clamp_milli` usage. `packages/adeu_core_ir/src/adeu_core_ir/ledger.py`

#### U layer (Utility) — goals/metrics/preferences

* **Raw node shape** should match:

  * `$defs.CoreUNode` with `kind ∈ {"Goal","Metric","Preference"}`, `label`, optional `weight`. `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` `packages/adeu_core_ir/src/adeu_core_ir/models.py` (see `UKind`, `CoreUNode`)
* Typed layer:

  * `URef` typed node ID reference for well-formed edges like `serves_goal` and `prioritizes`. Edge-typing matrix already encodes allowed endpoints (e.g., `serves_goal` from `D.*` to `U.Goal`; `prioritizes` from `U.Preference` to `U.Goal|U.Metric|U.Preference`). `packages/adeu_core_ir/src/adeu_core_ir/models.py` (`_EDGE_TYPING_MATRIX`)

---

### Layer discipline invariants to formalize (worth proving first)

These are “high-value / low-risk” because they directly mirror already-locked behavior (schema + validators):

1. **Canonical ordering invariants**

* Nodes sorted by `(layerOrder, kind, id)` and edges sorted by `(type, from_ref, to_ref)` (required by `AdeuCoreIR._validate_contract`). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Example fixture demonstrates this ordering in practice. `apps/api/fixtures/stop_gate/vnext_plus19/core_ir_read_surface_case_a_1.json`

2. **Reference integrity invariants**

* Every edge endpoint must be a node ID (no dangling). Enforced in `AdeuCoreIR._validate_contract` and also diagnosable via integrity artifacts. `packages/adeu_core_ir/src/adeu_core_ir/models.py` `packages/adeu_core_ir/src/adeu_core_ir/integrity_dangling_reference.py`

3. **Edge typing matrix invariants (ODEU separation)**

* Each edge’s `(fromSig, toSig)` must be allowed for that edge type per `_EDGE_TYPING_MATRIX`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* This is explicitly locked in the earlier continuation doc (frozen matrix). `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md`

4. **Uniqueness invariants**

* Node IDs unique; edge identities `(type, from, to)` unique. Enforced in `AdeuCoreIR._validate_contract`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`

5. **SBR ledger shape invariants (epistemic bookkeeping)**

* Ledger field coherence in `CoreENode._validate_ledger_fields` (e.g., if any milli score present then `ledger_version` must be present; `ledger_version == "adeu.sbr.v0_1"`). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Deterministic recompute/match behavior uses `ledger.py`. `packages/adeu_core_ir/src/adeu_core_ir/ledger.py`

---

C) Lean module plan (repo-integrated)

Below is an additive-first module plan that **does not change** existing `AdeuCore.*` semantics; it adds a parallel library to formalize ODEU core artifacts and invariants.

### Proposed new Lean files + namespaces

> All new files live under `packages/adeu_lean/` alongside the existing `AdeuCore.*` library (`packages/adeu_lean/AdeuCore.lean`, `packages/adeu_lean/AdeuCore/Semantics.lean`, `packages/adeu_lean/AdeuCore/Theorems.lean`). `packages/adeu_lean/AdeuCore.lean`

#### 0) Repo wiring (minimal glue)

* **Change:** add a new Lean library stanza in `packages/adeu_lean/lakefile.lean`:

  * add: `lean_lib AdeuODEU where globs := #[.submodules \`AdeuODEU]` 
    This is additive and does not modify`AdeuCore`. `packages/adeu_lean/lakefile.lean`

---

### 1) `packages/adeu_lean/AdeuODEU.lean`

**Purpose**

* Root import file for the new library, analogous to `AdeuCore.lean`. `packages/adeu_lean/AdeuCore.lean`

**Key definitions**

* Just imports:

  * `AdeuODEU.Artifacts`
  * `AdeuODEU.Ontology`
  * `AdeuODEU.Deontics`
  * `AdeuODEU.Epistemics`
  * `AdeuODEU.Utility`
  * `AdeuODEU.Invariants`
  * `AdeuODEU.ProofPackets`

**Theorem targets (2–3)**

* Mostly “integration theorems” ensuring the library composes:

  * `theorem AdeuODEU.compiles : True := trivial` (sanity target)
  * `theorem AdeuODEU.importsAdeuCoreNoSemanticChange : True := trivial` (documentary; the *actual* guarantee is procedural: no edits to `AdeuCore` files). `packages/adeu_lean/AdeuCore/Semantics.lean`

---

### 2) `packages/adeu_lean/AdeuODEU/Artifacts.lean`

**Purpose**

* Faithful Lean mirror of **`adeu_core_ir@0.1`** raw artifact structures.

**Grounding targets**

* Must match the schema and Pydantic models:

  * `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` (`$defs.CoreONode/CoreENode/CoreDNode/CoreUNode/CoreEdge`)
  * `packages/adeu_core_ir/src/adeu_core_ir/models.py` (`CoreONode/CoreENode/CoreDNode/CoreUNode`, `CoreEdge`, `Layer`, `OKind/EKind/DKind/UKind`, `EdgeType`) `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` `packages/adeu_core_ir/src/adeu_core_ir/models.py`

**Key definitions**

* Enumerations:

  * `Layer := O | E | D | U` (matches `Layer = Literal["O","E","D","U"]`). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
  * `OKind/EKind/DKind/UKind` mirroring the Literal unions. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
  * `EdgeType` mirroring the `EdgeType` literal union. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Structures:

  * `CoreONode`, `CoreENode`, `CoreDNode`, `CoreUNode` matching model fields (id/layer/kind + per-layer fields). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
  * `CoreNode := Sum CoreONode (Sum CoreENode (Sum CoreDNode CoreUNode))` (or an inductive), matching `CoreNode = Union[CoreONode, CoreENode, CoreDNode, CoreUNode]`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
  * `CoreEdge` with `type/from_ref/to_ref` matching `CoreEdge`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
  * `AdeuCoreIR` record matching schema fields `schema`, `source_text_hash`, optional `source_text`, optional `metadata`, plus lists of nodes/edges. `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`

**Concrete lemma targets (2–5)**

* `lemma nodeSignature_def (n : CoreNode) : nodeSignature n = s!"{layer}.{kind}"`
  (mirrors `_node_signature` in Python). `packages/adeu_core_ir/src/adeu_core_ir/models.py` (`def _node_signature`)
* `lemma canonicalNodeKey_matches_python (n : CoreNode) : ...`
  capturing the structure of `canonical_node_sort_key` (`(_LAYER_ORDER[layer], kind, id)`). `packages/adeu_core_ir/src/adeu_core_ir/models.py` (`def canonical_node_sort_key`)
* `lemma canonicalEdgeKey_matches_python (e : CoreEdge) : ...`
  capturing `canonical_edge_sort_key = (type, from_ref, to_ref)`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* `theorem edgeIdentity_injective : edgeIdentity e1 = edgeIdentity e2 → ...`
  (supports “no duplicate edges” invariant). `packages/adeu_core_ir/src/adeu_core_ir/models.py` (duplicate check uses `(edge.type, edge.from_ref, edge.to_ref)`)

---

### 3) `packages/adeu_lean/AdeuODEU/Ontology.lean`

**Purpose**

* Ontology-layer conveniences + invariants, still grounded in the raw schema.

**Grounding targets**

* O-kind enum and O node fields: `OKind` and `CoreONode` in `packages/adeu_core_ir/src/adeu_core_ir/models.py`, schema `$defs.CoreONode` in `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`. `packages/adeu_core_ir/src/adeu_core_ir/models.py` `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`

**Key definitions**

* `def isEntity/isConcept/isRelationType : CoreNode → Bool/Prop`
* Optional: `def canonicalAliases : List String → List String` (if you want a *non-gating* normalization view; raw artifacts need not be normalized per schema). Schema only says `aliases` exists, not normalized. `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`

**Theorem targets**

* `theorem aboutEdge_targets_O (h : Contract ir) (e ∈ ir.edges) : e.type = about → toLayer(e)=O`
  grounded by `_EDGE_TYPING_MATRIX["about"]` allowed targets. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* `theorem definesEdge_only_Evidence_to_O`
  grounded by `_EDGE_TYPING_MATRIX["defines"] : from {"E.Evidence"} → to {"O.Entity","O.Concept","O.RelationType"}`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`

---

### 4) `packages/adeu_lean/AdeuODEU/Deontics.lean`

**Purpose**

* Deontic-layer definitions and invariants, plus a *non-invasive* bridge to SEMANTICS_v3 predicate semantics already formalized in `AdeuCore.Semantics`.

**Grounding targets**

* Deontic node kinds + modalities: `CoreDNode` fields and `DKind` / modality literals in `packages/adeu_core_ir/src/adeu_core_ir/models.py`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Exception defeat/conflict semantics already formalized: `AdeuCore.Semantics.exceptionDefeatsNorm` and `conflictCandidate`. `packages/adeu_lean/AdeuCore/Semantics.lean`
* Deontic conflict diagnostic heuristic: `packages/adeu_core_ir/src/adeu_core_ir/integrity_deontic_conflict.py` (`_is_conflict_modality_pair`, normalization of target/condition). `packages/adeu_core_ir/src/adeu_core_ir/integrity_deontic_conflict.py`

**Key definitions**

* `inductive Modality | obligatory | forbidden | permitted` (mirror `CoreDNode.modality`). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* `def isNorm/isPolicy/isException/isPhys : CoreNode → Prop`
* Optional interpreted condition:

  * `inductive DCondition | text (s:String) | pred (p: AdeuCore.Pred)`
    (bridges to Lean predicate semantics without changing raw artifact). `packages/adeu_lean/AdeuCore/Semantics.lean`

**Theorem targets**

* **Edge discipline**

  * `theorem exceptsEdge_fromException (h : Contract ir) : e.type = excepts → fromSig(e) = "D.Exception"`
    grounded by `_EDGE_TYPING_MATRIX["excepts"] : from {"D.Exception"} ...`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
  * `theorem gatesEdge_fromPolicy (h : Contract ir) : e.type = gates → fromSig(e) = "D.Policy"`
    grounded by `_EDGE_TYPING_MATRIX["gates"] : from {"D.Policy"} → to {"E.Claim","E.Assumption","E.Question","D.Norm","D.Policy"}`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* **Conflict heuristic properties (evidence-only)**

  * `theorem conflictModalityPair_symm : isConflictPair a b ↔ isConflictPair b a`
    grounded by `_is_conflict_modality_pair` using set equality `{a,b} == {"obligatory","forbidden"}`. `packages/adeu_core_ir/src/adeu_core_ir/integrity_deontic_conflict.py`
* **SEMANTICS_v3 bridge (do not change semantics; just reuse)**

  * `theorem leanConflictSoundness_reexport := AdeuCore.Theorems.conflict_soundness`
    (makes it usable from AdeuODEU proofs). `packages/adeu_lean/AdeuCore/Theorems.lean`

---

### 5) `packages/adeu_lean/AdeuODEU/Epistemics.lean`

**Purpose**

* Epistemic layer + ledger formalization.

**Grounding targets**

* E node kinds + ledger fields: `CoreENode` in `packages/adeu_core_ir/src/adeu_core_ir/models.py` and schema `$defs.CoreENode`. `packages/adeu_core_ir/src/adeu_core_ir/models.py` `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`
* Ledger scoring algorithm: `packages/adeu_core_ir/src/adeu_core_ir/ledger.py` (`apply_claim_ledger_scores`, `clamp_milli`). `packages/adeu_core_ir/src/adeu_core_ir/ledger.py`
* Source spans contract: `packages/adeu_ir/src/adeu_ir/models.py` (`class SourceSpan` with validator `start < end`). `packages/adeu_ir/src/adeu_ir/models.py`

**Key definitions**

* `structure SourceSpan where start : Nat; end_ : Nat; h : start < end_`
* `structure SBR where S_milli B_milli R_milli : Nat; bounds proofs`
* `def recomputeSBR : ...` mirroring `apply_claim_ledger_scores` (Slice 2 implements faithfully). `packages/adeu_core_ir/src/adeu_core_ir/ledger.py`

**Theorem targets**

* `theorem clamp_milli_bounds : 0 ≤ clamp_milli x ∧ clamp_milli x ≤ 1000`
  mirrors `clamp_milli` behavior. `packages/adeu_core_ir/src/adeu_core_ir/ledger.py`
* `theorem recompute_in_range : recomputeSBR ... → 0 ≤ S,B,R ≤ 1000`
  grounded by ledger’s clamp usage. `packages/adeu_core_ir/src/adeu_core_ir/ledger.py`
* `theorem ledger_version_required : (E node has any *_milli) → ledger_version = "adeu.sbr.v0_1"`
  matches `CoreENode._validate_ledger_fields`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`

---

### 6) `packages/adeu_lean/AdeuODEU/Utility.lean`

**Purpose**

* Utility layer + the canonical edge discipline around goals/metrics/preferences.

**Grounding targets**

* U node kinds and fields: `CoreUNode` / `UKind` in `packages/adeu_core_ir/src/adeu_core_ir/models.py`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Edge discipline: `_EDGE_TYPING_MATRIX["serves_goal"]` and `["prioritizes"]`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`

**Key definitions**

* `def isGoal/isMetric/isPreference : CoreNode → Prop`
* Optional: `def weight : CoreUNode → Option Int`

**Theorem targets**

* `theorem servesGoalEdge_targets_Goal (h : Contract ir) : e.type = serves_goal → toSig(e)="U.Goal"`
  grounded by `_EDGE_TYPING_MATRIX["serves_goal"] : from D.* → to U.Goal`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* `theorem prioritizesEdge_fromPreference (h : Contract ir)`
  grounded by `_EDGE_TYPING_MATRIX["prioritizes"] : from {"U.Preference"} → to {"U.Goal","U.Metric","U.Preference"}`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`

---

### 7) `packages/adeu_lean/AdeuODEU/Invariants.lean`

**Purpose**

* Encode the **frozen contract** from `AdeuCoreIR._validate_contract` as a Lean predicate + decidable checker, enabling:

  * “static” theorems (prove the checker is sound)
  * “artifact-level” proofs (embed an artifact value and prove `check ir = true`)

**Grounding targets**

* Validation contract: `packages/adeu_core_ir/src/adeu_core_ir/models.py` (`AdeuCoreIR._validate_contract`, `_EDGE_TYPING_MATRIX`, `_LAYER_ORDER`, sorting and uniqueness checks). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Lock doc that this matrix/order is frozen: `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md`. `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md`

**Key definitions**

* `def Contract (ir : AdeuCoreIR) : Prop := ...`
  with clauses:

  * `nodesSorted`, `edgesSorted`
  * `Nodup nodeIds`, `Nodup edgeIdentities`
  * `edgeEndpointsExist`
  * `edgeTypingMatrixRespected`
* `def checkContract (ir) : Bool := ...` (decidable computation)
* `theorem checkContract_sound : checkContract ir = true → Contract ir`
* Optional: `def canonicalize (ir) : AdeuCoreIR` mirroring `canonicalize_core_ir_payload` (dedup edges, sort, etc.). `packages/adeu_core_ir/src/adeu_core_ir/models.py` (`def canonicalize_core_ir_payload`)

**Theorem targets**

* `theorem contract_implies_no_dangling : Contract ir → ∀ e ∈ ir.edges, e.from_ref ∈ nodeIds ∧ e.to_ref ∈ nodeIds`
  mirrors `AdeuCoreIR._validate_contract` “edge references unknown node”. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* `theorem contract_implies_edge_typing : Contract ir → ∀ e, AllowedEdge e`
  grounded by `_EDGE_TYPING_MATRIX` checks. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* `theorem canonicalize_preserves_contract : Contract ir → Contract (canonicalize ir)`
  grounded by `canonicalize_core_ir_payload` behavior (sort + dedup). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* `theorem checkContract_complete : Contract ir → checkContract ir = true`
  (enables `by decide` proofs on concrete artifacts)

---

### 8) `packages/adeu_lean/AdeuODEU/ProofPackets.lean`

**Purpose**

* Align Lean proofs with **existing evidence packet families** (trust packets, semantics-v4 candidate packets, proof_evidence@1), without altering runtime semantics.

**Grounding targets**

* Trust invariant packet schema + deterministic `proof_id`:
  `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py` (`build_trust_invariant_proof_id`, `TrustInvariantProofItem._validate_contract`). `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py`
* Semantics-v4 candidate packet deterministic `comparison_id`:
  `packages/adeu_core_ir/src/adeu_core_ir/semantics_v4_candidate_packet.py` (`build_semantics_v4_candidate_comparison_id`, sorting + required patterns). `packages/adeu_core_ir/src/adeu_core_ir/semantics_v4_candidate_packet.py`
* Proof evidence contract (deterministic hashing, excluded fields):
  `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py` (`build_proof_evidence_packet`, `proof_evidence_hash`, `PROOF_EVIDENCE_HASH_EXCLUDED_FIELDS`). `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`
* ProofArtifact envelope schema for kernel:
  `packages/adeu_ir/schema/adeu.proof_artifact.v0.json` and the model in `packages/adeu_ir/src/adeu_ir/models.py` (`class ProofArtifact`). `packages/adeu_ir/schema/adeu.proof_artifact.v0.json` `packages/adeu_ir/src/adeu_ir/models.py`

**Key definitions**

* Lean-side “evidence view” types:

  * `structure ProofResult := (theoremId : String) (status : Bool) (details : Json)` (or a Lean record)
    which can be exported by Python into `proof_evidence@1` using `build_proof_evidence_packet`. `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`
* **Spec stubs** for canonical JSON + sha256 matching the lock profile
  (full implementation can land in Slice 2; spec is grounded by the lock + hashing helpers). `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` `apps/api/src/adeu_api/hashing.py`

**Theorem targets**

* `theorem proofEvidence_hash_excludes_nonsemantic_fields`
  mirrors the semantics of `strip_nonsemantic_proof_fields` + `PROOF_EVIDENCE_HASH_EXCLUDED_FIELDS` (a Lean formal spec of that transformation). `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`
* `theorem trustInvariant_proofId_deterministic`
  spec-level: if canonical payload equal then proof_id equal (eventually backed by Lean sha256 implementation or FFI). Grounded by `build_trust_invariant_proof_id`. `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py`
* `theorem semanticsV4Candidate_comparisonId_deterministic`
  grounded by `build_semantics_v4_candidate_comparison_id`. `packages/adeu_core_ir/src/adeu_core_ir/semantics_v4_candidate_packet.py`

---

D) “Proof packets” alignment with existing artifact families

### How Lean proofs can feed/validate existing packets (no runtime semantics changes)

**Existing evidence pipeline we should reuse**

* The repo already has a deterministic proof evidence contract builder:
  `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py` (`build_proof_evidence_packet`, canonical JSON, excluded hash fields). `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`
* Proof artifacts are represented as `ProofArtifact` (schema in `packages/adeu_ir/schema/adeu.proof_artifact.v0.json`, model in `packages/adeu_ir/src/adeu_ir/models.py`). `packages/adeu_ir/schema/adeu.proof_artifact.v0.json` `packages/adeu_ir/src/adeu_ir/models.py`
* The API already materializes proof evidence packets from stored proof rows via `build_proof_evidence_packet`: `apps/api/src/adeu_api/main.py` (`_proof_evidence_packet_from_row`). `apps/api/src/adeu_api/main.py`

**Proposed alignment (additive)**

1. **Artifact-level ODEU proof obligations** (new theorem IDs; same backend = Lean)

   * For a given `adeu_core_ir@0.1` artifact payload, generate a wrapper theorem that proves `checkContract(ir)=true` using your Lean contract checker (in `AdeuODEU.Invariants`). The contract itself is grounded in the existing Pydantic validator (`AdeuCoreIR._validate_contract`) and the frozen matrix. `packages/adeu_core_ir/src/adeu_core_ir/models.py` `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md`
2. **Record results as proof_evidence@1** (not as new schema)

   * The Python side (kernel or stop-gate tooling) uses `build_proof_evidence_packet` to emit deterministic packets with `proof_evidence_hash`. This is already compatible with stop-gate tooling (`PROOF_EVIDENCE_SCHEMA = "proof_evidence@1"`). `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py` `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
3. **Linking to trust/candidate packets without changing them**

   * We do **not** mutate the locked trust packet schema (`TrustInvariantCode` is a fixed Literal set). `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py`
   * Instead, we reference the trust/candidate artifacts in the proof inputs:

     * `ProofInput.object_id` can carry the artifact’s identifier (e.g., the packet’s `core_ir_artifact_id`), and `json_path` can point to subfields (aligned with SEMANTICS_v3’s json_path usage in assertions). `packages/adeu_ir/src/adeu_ir/models.py` (`class ProofInput`) `packages/adeu_kernel/src/adeu_kernel/checker.py` (`_json_path_hash`)
   * This gives an additive “proof_trust” lane that can be reviewed alongside mapping_trust outputs, exactly as the lock doc intends (trust lanes separate). `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`

### Minimal deterministic “proof evidence export contract”

Use the existing one:

* **Export type:** `proof_evidence@1` packet created by `build_proof_evidence_packet`, which:

  * normalizes/lex-sorts inputs (`_normalize_inputs`),
  * canonicalizes details (`_normalize_details` via `_canonical_json`),
  * excludes nonsemantic fields from the hash (`PROOF_EVIDENCE_HASH_EXCLUDED_FIELDS`),
  * emits `hash_excluded_fields` and a deterministic `proof_evidence_hash`.
    `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`

This satisfies your determinism constraint and avoids introducing a new serialized artifact schema (consistent with the general lock posture in `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`). `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`

---

E) Minimum viable theorem set (first slice)

Below are **12 prioritized invariants** that are (a) already encoded in repo contracts, and (b) feasible to prove in Lean incrementally.

> For each: (1) artifact/schema scope, (2) Lean mapping, (3) evidence output strategy.

1. **Core IR edge typing matrix respected**

* Applies to: `adeu_core_ir@0.1` validator (`_EDGE_TYPING_MATRIX`). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Lean mapping: `AllowedEdge : EdgeType → NodeSig → NodeSig → Prop` + `Contract.edgeTyping`. `packages/adeu_core_ir/src/adeu_core_ir/models.py` (matrix + `_node_signature`)
* Evidence output: `proof_evidence@1` with `details = { invariant: "EDGE_TYPING_MATRIX", status: pass/fail }`. `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`

2. **No dangling edge endpoints**

* Applies to: `AdeuCoreIR._validate_contract` (“edge references unknown node”). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Lean mapping: `Contract.noDangling : Prop`, derived lemma `contract_implies_no_dangling`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Evidence output: proof_evidence item referencing the artifact’s id + `"$.edges[*].from/to"`. `packages/adeu_ir/src/adeu_ir/models.py` (`ProofInput.json_path`)

3. **Canonical node ordering**

* Applies to: `canonical_node_sort_key` and `AdeuCoreIR._validate_contract` check “nodes must be sorted”. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Lean mapping: `nodesSorted : List CoreNode → Prop` using `layerOrder` + `kind` + `id`.
* Evidence output: proof_evidence pass/fail with `details = {expected_order: "...", observed: "..."} (bounded excerpt)`. `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py` (details canonicalization)

4. **Canonical edge ordering**

* Applies to: `canonical_edge_sort_key` and `_validate_contract` “edges must be sorted”. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Lean mapping: `edgesSorted : List CoreEdge → Prop`.
* Evidence output: as above.

5. **No duplicate node IDs**

* Applies to: `_validate_contract` “duplicate node id”. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Lean mapping: `List.Nodup (ir.nodes.map nodeId)`.
* Evidence output: proof_evidence with failing duplicate set excerpt if violated.

6. **No duplicate edge identities**

* Applies to: `_validate_contract` “duplicate edge identity” using `(type, from_ref, to_ref)`. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Lean mapping: `List.Nodup (ir.edges.map edgeIdentity)`.
* Evidence output: same.

7. **SBR ledger field coherence**

* Applies to: `CoreENode._validate_ledger_fields` (ledger_version required, must be `"adeu.sbr.v0_1"`, score field mutual constraints). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* Lean mapping: `EWellFormed : CoreENode → Prop` and `Contract.allENodesWellFormed`.
* Evidence output: proof_evidence with failing node ids in `details`.

8. **SBR recompute/match**

* Applies to: stop-gate metric name suggests this invariant is used: `VNEXT_PLUS13_DEFAULT_METRICS["adeu_claim_ledger_recompute_match_pct"]`. `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
* Ground truth computation: `packages/adeu_core_ir/src/adeu_core_ir/ledger.py` (`apply_claim_ledger_scores`). `packages/adeu_core_ir/src/adeu_core_ir/ledger.py`
* Lean mapping: implement `recomputeSBR` and prove: if stored SBR equals recomputed then invariant holds.
* Evidence output: proof_evidence per claim node, or one aggregate proof with count.

9. **Lane report contract**

* Applies to: `AdeuLaneReport._validate_contract` enforces canonical lane key order `("O","E","D","U")`, lex-sorted unique node lists, non-negative edge counts. `packages/adeu_core_ir/src/adeu_core_ir/lane_report.py`
* Lean mapping: `LaneReportContract` and a checker for `lane_nodes`/`lane_edge_counts`.
* Evidence output: proof_evidence keyed to lane report artifact id.

10. **Cycle policy diagnostics contract**

* Applies to: `AdeuIntegrityCyclePolicyCycle._validate_contract` (canonical rotation, signature matches node_ids, kind matches length), and summary counts. `packages/adeu_core_ir/src/adeu_core_ir/integrity_cycle_policy.py`
* Lean mapping: define `canonicalCycleRotation` and prove `rotation_minimal` properties; prove summary correctness.
* Evidence output: proof_evidence; on failure include offending `cycle_signature`.

11. **Deontic conflict diagnostics soundness (evidence-only)**

* Applies to: `build_integrity_deontic_conflict_diagnostics` defines conflict iff same normalized `(target, condition)` and modality pair is `{obligatory, forbidden}`. `packages/adeu_core_ir/src/adeu_core_ir/integrity_deontic_conflict.py`
* Lean mapping: formalize `_normalize_text/_normalize_condition` behavior (at least the key “normalize whitespace + NFC + lowercase ASCII” shape; full NFC in Lean may be deferred) and prove: every emitted conflict satisfies predicate.
* Evidence output: proof_evidence; classify as evidence-only (doesn’t block core IR validity unless repo says so). The schema itself is separate from core IR validity. `packages/adeu_core_ir/schema/adeu_integrity_deontic_conflict.v0_1.json`

12. **Trust invariant packet internal contract**

* Applies to: deterministic proof_id generation, sorted proof_items, “exactly one per invariant_code”, summary count matches, justification_refs schema order. `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py`
* Lean mapping: encode `TrustInvariantCode` enum and `trustProofId` spec (Slice 2 implements sha256 + canonical JSON), plus contract checker.
* Evidence output: proof_evidence validating the packet (proof_trust lane validating mapping_trust artifact). Trust lanes separation is explicitly intended. `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`

---

F) Implementation roadmap (3 slices)

### Slice 1: Compile-clean Lean skeleton + a couple “easy” theorems + repo wiring

**Deliverables**

* Add new Lean library `AdeuODEU` without touching existing `AdeuCore.*` files. `packages/adeu_lean/AdeuCore.lean`
* Update `packages/adeu_lean/lakefile.lean` add `lean_lib AdeuODEU` globs. `packages/adeu_lean/lakefile.lean`
* Implement:

  * `AdeuODEU/Artifacts.lean`: enums + raw structures mirroring `adeu_core_ir@0.1`. `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` `packages/adeu_core_ir/src/adeu_core_ir/models.py`
  * `AdeuODEU/Invariants.lean`: `Contract` Prop + `checkContract : Bool` (start with **edge-typing** + **no dangling** first). `packages/adeu_core_ir/src/adeu_core_ir/models.py`
* “Easy theorems” to land first:

  * `checkContract_sound` (if it says true then Contract holds).
  * `Contract.implies_no_dangling`.
  * `Contract.implies_edge_typing`.
    (All grounded by `_validate_contract` and `_EDGE_TYPING_MATRIX`.) `packages/adeu_core_ir/src/adeu_core_ir/models.py`

**Why this doesn’t break semantics**

* SEMANTICS_v3 code and Lean theorems remain unchanged; we are adding a new library. `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` `packages/adeu_lean/AdeuCore/Semantics.lean`

---

### Slice 2: JSON→Lean decoding strategy + property tests + deterministic replay

**Goal**

* Make Lean checks run on **real artifacts**, not just abstract theorems.

**Strategy options (both repo-compatible)**

1. **Embed artifacts as Lean values generated by Python**

   * Python loads JSON → normalizes via existing canonicalization (`canonicalize_core_ir_payload`) → emits Lean code defining `def ir : AdeuODEU.AdeuCoreIR := ...` and a theorem `by native_decide` that `checkContract ir = true`.
     Grounding: `canonicalize_core_ir_payload` exists. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
2. **Lean-side JSON parsing from canonical JSON string**

   * Implement `FromJson` instances for the ODEU structures in `AdeuODEU/Artifacts.lean`, and have the wrapper theorem embed a canonical JSON string.
     Grounding: canonical JSON profile is locked and implemented in python (`canonical_json`). `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` `apps/api/src/adeu_api/hashing.py`

**Property tests (deterministic)**

* Use existing fixtures for replay comparisons, e.g.:

  * `apps/api/fixtures/stop_gate/vnext_plus19/core_ir_read_surface_case_a_1.json` for core IR invariants. `apps/api/fixtures/stop_gate/vnext_plus19/core_ir_read_surface_case_a_1.json`
* Cross-check Lean vs Python:

  * Python: `AdeuCoreIR.model_validate(...)` enforces the same contract. `packages/adeu_core_ir/src/adeu_core_ir/models.py`
  * Lean: `checkContract` should agree on pass/fail for the same canonicalized payload.

**Hashing**

* Implement Lean `canonical_json` serializer and `sha256` only if/when needed (trust packet proof_id and hash recompute invariants). Ground truth for the profile is the lock + existing implementations. `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` `packages/urm_runtime/src/urm_runtime/hashing.py`

---

### Slice 3: Integrate into stop-gate / evidence reporting (additive, non-semantic)

**Goal**

* Emit Lean proof results as **proof_evidence@1** packets alongside existing tooling, without modifying runtime semantics.

**Integration points (existing)**

* Stop gate already recognizes `PROOF_EVIDENCE_SCHEMA = "proof_evidence@1"` and replays determinism for multiple arcs. `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
* Proof evidence packets are deterministic and hashed via `build_proof_evidence_packet`. `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`

**Minimal additive plan**

* Add a new optional runner (do not change existing obligation kinds):

  * Keep current runner stable (`pred_closed_world`, `exception_gating`, `conflict_soundness`). `packages/adeu_lean/src/adeu_lean/models.py` `packages/adeu_lean/src/adeu_lean/runner.py`
  * Add `packages/adeu_lean/src/adeu_lean/odeu_runner.py` (new) that builds wrapper theorems for:

    * core IR contract pass (`AdeuODEU.Invariants.checkContract`)
    * lane report contract
    * trust packet contract (once sha256 is implemented in Lean or via a verified shim)
* Kernel/API uses existing `build_proof_evidence_packet` to export results. `apps/api/src/adeu_api/main.py` `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`
* Stop-gate can treat this as additional **proof_trust** evidence (not replacing mapping_trust packets like trust_invariant_packet). Trust lanes separation is explicitly locked. `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`

---

If you want, I can also draft the exact Lean signatures for `Contract`, `checkContract`, and the `AllowedEdge` matrix encoding so it is *mechanically isomorphic* to `_EDGE_TYPING_MATRIX` (and therefore auditable against `packages/adeu_core_ir/src/adeu_core_ir/models.py`).
