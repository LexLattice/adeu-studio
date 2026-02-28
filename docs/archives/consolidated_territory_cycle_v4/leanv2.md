1. Repo Grounding Map (table)

| ODEU layer         | Authoritative schema(s)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Python model(s)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Validators / enforcement hooks (today)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     | Existing Lean files (today)                                                                                                                                                                                                                                                                                                                                                                                 | Contract facts explicitly enforced today                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| ------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **O — Ontology**   | **(Full IR)** `packages/adeu_ir/schema/adeu.ir.v0.json` defines top-level `"O"` referencing `$defs/OChannel` (entities + definitions).<br><br>**(Core projection)** `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` `$defs/CoreONode` enumerates kind ∈ {Entity, Concept, RelationType}. (Example excerpt: `"$defs": { "CoreONode": { ... "kind": { "enum": ["Entity","Concept","RelationType"] }}}`.)<br><br>**(Concept IR, used by cross-IR)** `packages/adeu_concepts/schema/adeu.concepts.v0.json` (terms/senses/links).                                                                                                                                                                                                   | **(Full IR)** `packages/adeu_ir/src/adeu_ir/models.py:class OChannel` (fields `entities`, `definitions`).<br><br>**(Core projection)** `packages/adeu_core_ir/src/adeu_core_ir/models.py:class CoreONode` + `OKind = Literal["Entity","Concept","RelationType"]`.<br><br>**(Concept IR)** `packages/adeu_concepts/src/adeu_concepts/models.py:class ConceptIR`, `class Term`, `class TermSense`, etc.                                                                                                                                                                                                                                    | **Core IR contract validator:** `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract` enforces global invariants over nodes+edges (sorting, no duplicates, edge typing matrix, no dangling refs). This affects O nodes because O nodes can be edge targets in `_EDGE_TYPING_MATRIX` for `"about"` and `"defines"`.<br><br>**Stop-gate mirror validator (structural):** `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_validated_adeu_core_ir_payload` (calls `_validate_core_ir_nodes`, `_validate_core_ir_edges` using `_ADEU_CORE_ALLOWED_KINDS` / `_ADEU_CORE_EDGE_TYPING_MATRIX`).                                                                                                                                                                                                               | **NOT FOUND**: no Lean module that models OChannel/CoreONode/ConceptIR directly (Lean currently only defines small kernel-style semantics objects). Existing Lean library is `packages/adeu_lean/AdeuCore/*.lean`.                                                                                                                                                                                          | **Core O node kinds are fixed** (`OKind = Literal[...]`) in `packages/adeu_core_ir/src/adeu_core_ir/models.py` and in schema `$defs/CoreONode` in `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`.<br><br>**CoreIR node ordering is frozen** (`nodes must be sorted by (layer, kind, id)`) in `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract` and mirrored in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_validate_core_ir_nodes`.                                                                                         |
| **D — Deontics**   | **(Full IR)** `packages/adeu_ir/schema/adeu.ir.v0.json` includes `"D_phys"` and `"D_norm"` channels (`$defs/DPhysChannel`, `$defs/DNormChannel`, `$defs/NormStatement`, `$defs/ExceptionClause`, etc.).<br><br>**(Core projection)** `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` `$defs/CoreDNode` and global edge types list `$defs/CoreEdge` (type/from/to).<br><br>**(Diagnostics artifacts)** `packages/adeu_core_ir/schema/adeu_integrity_deontic_conflict.v0_1.json` (and `_extended`).                                                                                                                                                                                                                              | **(Full IR)** `packages/adeu_ir/src/adeu_ir/models.py:class NormStatement`, `class ExceptionClause`, `class DPhysConstraint`, `class DNormChannel`.<br><br>**(Core projection)** `packages/adeu_core_ir/src/adeu_core_ir/models.py:class CoreDNode` with fields like `modality`, `condition`, `target`, `priority`, and `DKind = Literal["PhysicalConstraint","Norm","Policy","Exception"]`.<br><br>**(Diagnostics builder)** `packages/adeu_core_ir/src/adeu_core_ir/integrity_deontic_conflict.py:build_integrity_deontic_conflict_diagnostics` (normalizes target/condition text via `_normalize_text`, `_normalize_condition`).      | **Core IR contract:** `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract` enforces D-related edge typing via `_EDGE_TYPING_MATRIX` (e.g., `"justifies": {"E.Claim","E.Evidence"} → {"D.Norm","D.Policy"}`, `"gates": {"D.Policy"} → {"E.Claim","E.Assumption","E.Question"}`, `"excepts": {"D.Exception"} → {"D.PhysicalConstraint","D.Norm","D.Policy"}`).<br><br>**Diagnostics contract:** `packages/adeu_core_ir/src/adeu_core_ir/integrity_deontic_conflict.py:AdeuIntegrityDeonticConflict._validate_contract` enforces sorted conflicts + exact summary counts.<br><br>**Stop-gate:** `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_validated_adeu_integrity_deontic_conflict_payload` validates schema + sorting + summary counts (and enforces deterministic “extended” schema variants). | `packages/adeu_lean/AdeuCore/Semantics.lean` defines abstract deontic gating & conflict concepts: `def exceptionDefeatsNorm` and `def conflictCandidate` / `def conflict` (see `packages/adeu_lean/AdeuCore/Semantics.lean`).<br><br>`packages/adeu_lean/AdeuCore/Theorems.lean` proves small properties like `theorem exception_gating_false_not_defeat` and `theorem conflict_soundness` over those defs. | **Text-normalized deontic conflict detection** (NFC normalization + whitespace collapse + `casefold()`) is explicitly implemented in `packages/adeu_core_ir/src/adeu_core_ir/integrity_deontic_conflict.py:_normalize_text` and used in `build_integrity_deontic_conflict_diagnostics`.<br><br>**Diagnostics output must be sorted** (by kind, primary_id, related_id) in `.../integrity_deontic_conflict.py:AdeuIntegrityDeonticConflict._validate_contract`.                                                                                                                  |
| **E — Epistemics** | **(Full IR)** `packages/adeu_ir/schema/adeu.ir.v0.json` `"E"` references `$defs/EChannel` with `$defs/EvidenceClaim` etc.<br><br>**(Core projection)** `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` `$defs/CoreENode` includes `kind ∈ {"Claim","Assumption","Question","Evidence"}` and optional ledger fields. Notably, `ledger_version` is optional (`anyOf const "adeu.sbr.v0_1" or null`). (See `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` around `"ledger_version": {"anyOf":[{"const":"adeu.sbr.v0_1"}, {"type":"null"}]}`.)<br><br>**(Diagnostics artifacts)** `packages/adeu_core_ir/schema/adeu_integrity_cycle_policy.v0_1.json` (+ `_extended`), `adeu_integrity_dangling_reference.v0_1.json`, etc. | **(Full IR)** `packages/adeu_ir/src/adeu_ir/models.py:class EvidenceClaim` (+ EChannel).<br><br>**(Core projection)** `packages/adeu_core_ir/src/adeu_core_ir/models.py:class CoreENode` (fields: `text`, `spans`, optional `confidence`, optional ledger fields `S_milli`/`B_milli`/`R_milli` via aliases).<br><br>**(Ledger)** `packages/adeu_core_ir/src/adeu_core_ir/ledger.py:_compute_claim_ledger_scores`, `apply_claim_ledger_scores`, `assert_claim_ledger_recompute_match`.<br><br>**(Cycle policy diagnostics)** `packages/adeu_core_ir/src/adeu_core_ir/integrity_cycle_policy.py:build_integrity_cycle_policy_diagnostics`. | **CoreENode ledger field validator:** `packages/adeu_core_ir/src/adeu_core_ir/models.py:CoreENode._validate_ledger_fields` enforces: if `ledger_version` present then exactly `"adeu.sbr.v0_1"`, and each of `S_milli/B_milli/R_milli` is in 0..1000 (also via Pydantic `ge=0, le=1000`).<br><br>**Ledger recompute check:** `packages/adeu_core_ir/src/adeu_core_ir/ledger.py:assert_claim_ledger_recompute_match` raises `URM_ADEU_CORE_LEDGER_RECOMPUTE_MISMATCH` when stored ledger doesn’t match recompute.<br><br>**Stop-gate metric:** `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:VNEXT_PLUS13_DEFAULT_METRICS` includes `adeu_claim_ledger_recompute_match_pct`; enforcement is via `_assert_adeu_claim_ledger_recompute_match` (and related fixture runner) in the same file.                                       | Existing Lean does **not** model the E-layer graph/ledger; it only provides abstract predicates (`Pred`) and evaluation (`evalPred`) in `packages/adeu_lean/AdeuCore/Semantics.lean`, with small theorems in `.../Theorems.lean`. There’s no Lean encoding of `CoreENode` or ledger scoring.                                                                                                                | **Ledger bounds (0..1000) are enforced** in `packages/adeu_core_ir/src/adeu_core_ir/models.py:CoreENode._validate_ledger_fields` and by schema constraints in `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` (`S_milli/B_milli/R_milli` are integer+range via schema/Pydantic).<br><br>**Cycle-policy diagnostics are canonicalized**: cycles must be sorted and signature-consistent in `packages/adeu_core_ir/src/adeu_core_ir/integrity_cycle_policy.py:AdeuIntegrityCyclePolicy._validate_contract` (and rotation canonicalization via `_canonical_cycle_rotation`). |
| **U — Utility**    | **(Full IR)** `packages/adeu_ir/schema/adeu.ir.v0.json` `"U"` references `$defs/UChannel` with `$defs/Goal` etc.<br><br>**(Core projection)** `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` `$defs/CoreUNode` has kind ∈ {Goal, Metric, Preference} (see schema excerpt under `"CoreUNode": { "kind": { "enum": ["Goal","Metric","Preference"] }}`).                                                                                                                                                                                                                                                                                                                                                                         | **(Full IR)** `packages/adeu_ir/src/adeu_ir/models.py:class Goal`, `class UChannel`.<br><br>**(Core projection)** `packages/adeu_core_ir/src/adeu_core_ir/models.py:class CoreUNode` with fields `label`, `weight` (optional).                                                                                                                                                                                                                                                                                                                                                                                                           | **Core IR contract:** edge typing for utility routing is enforced in `_EDGE_TYPING_MATRIX` in `packages/adeu_core_ir/src/adeu_core_ir/models.py` (e.g., `"serves_goal" → {"U.Goal","U.Metric"}`, `"prioritizes"` edges originate from `U.Preference`).<br><br>**Stop-gate mirror:** `_validate_core_ir_edges` in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` uses `_ADEU_CORE_EDGE_TYPING_MATRIX` including the same `"serves_goal"` / `"prioritizes"` target sets.                                                                                                                                                                                                                                                                                                                                                          | **NOT FOUND**: no Lean code for U nodes/goals/preferences.                                                                                                                                                                                                                                                                                                                                                  | **Utility node kinds are fixed** in core IR schema and models (`UKind = Literal["Goal","Metric","Preference"]` in `packages/adeu_core_ir/src/adeu_core_ir/models.py`).<br><br>**Utility-related edge typing is enforced** by `_EDGE_TYPING_MATRIX` in `packages/adeu_core_ir/src/adeu_core_ir/models.py` and mirrored in `_ADEU_CORE_EDGE_TYPING_MATRIX` in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`.                                                                                                                                                          |

**Canonical IR boundary / “what is frozen as contracts” (repo evidence only)**

* **Runtime/semantic authority is the full IR + SEMANTICS v3 lock, not the core-IR projection.**

  * Full IR contract shape: `packages/adeu_ir/src/adeu_ir/models.py:class AdeuIR` (`schema_version: "adeu.ir.v0"`, channels `O/D_phys/D_norm/E/U`).
  * Semantics lock: `docs/SEMANTICS_v3.md` fixes deterministic assertion naming (`a:<object_id>:<json_path_hash>` where `json_path_hash = sha256(json_path).hexdigest()[:12]`), and the “effective norms → conflict checks → SMT” pipeline.
  * The corresponding code is in `packages/adeu_kernel/src/adeu_kernel/checker.py:_json_path_hash` and `docs/SEMANTICS_v3.md` (same hash truncation rule).

* **Core IR is a frozen *projection artifact* with its own contract.**

  * Frozen contract enforcement lives in `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract`.
  * Lock framing (“projection authority lock”) is explicitly stated in `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md` (Core IR v0.1 is a read-only projection; it does not supersede adeu.ir.v0 authority).

* **Deterministic canonical JSON + sha256 locks are global.**

  * Lock text: `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` explicitly freezes canonical serialization profile: “`ensure_ascii=False`, `separators=(',', ':')`, `sort_keys=True`, UTF-8 bytes; do not insert missing fields, do not mutate list order.”
  * Canonical JSON implementations that match this profile exist in:

    * `apps/api/src/adeu_api/hashing.py:canonical_json`
    * `packages/urm_runtime/src/urm_runtime/hashing.py:canonical_json` and `sha256_canonical_json`
    * `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py:_canonical_json`

---

2. “ODEU Formal Template v0.2” (design doc)

A) Goals & non-goals

**Goals (v0.2)**

* **Add an additive Lean “spec & proof” layer for ODEU artifact invariants** without changing runtime semantics (SEMANTICS v3 remains authoritative).

  * SEMANTICS authority is fixed by `docs/SEMANTICS_v3.md` (effective norms, conflict checks, deterministic assertion naming) and implemented in `packages/adeu_kernel/src/adeu_kernel/checker.py` (e.g., `_json_path_hash`).
  * This template targets *artifact contracts* already enforced in Python/stop-gate (e.g., `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract`) and proves those properties in Lean as a parallel layer.

* **Prove high-leverage, deterministic structural invariants** about:

  * Core IR well-formedness (`AdeuCoreIR` contract)
  * Lane report contract (`packages/adeu_core_ir/src/adeu_core_ir/lane_report.py:AdeuLaneReport._validate_contract`)
  * Ledger recompute match (`packages/adeu_core_ir/src/adeu_core_ir/ledger.py:assert_claim_ledger_recompute_match`)
  * Trust invariant packet determinism (`packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py`)
  * Proof evidence hash stability / exclusion semantics (`packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`)

* **Respect deterministic hashing + canonical JSON locks** by treating canonical JSON generation as either:

  * A *shared oracle boundary* (Lean does not implement sha256/canonicalization), or
  * A “replayed” constant provided by deterministic Python code that already implements the frozen profile (e.g., `packages/urm_runtime/src/urm_runtime/hashing.py:canonical_json`).
    The lock text that constrains this is in `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`.

**Non-goals (explicitly out of scope for v0.2)**

* **Not proving solver correctness or theorem-prover integration beyond existing infrastructure.**
  This matches the explicit scope constraint in `docs/LOCKED_CONTINUATION_vNEXT_PLUS23.md` (it calls out that theorem-prover integration beyond existing infrastructure is not in that arc).

* **Not changing the SEMANTICS v3 execution model** (no changes to kernel’s definition of effective norms, exception gating, conflict checks, assertion naming). Authority is locked in `docs/SEMANTICS_v3.md` and implemented in `packages/adeu_kernel/src/adeu_kernel/*`.

* **Not implementing a fully verified JSON parser or SHA-256 inside Lean in v0.2.**
  Canonical JSON + sha256 are locked operationally in `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` and implemented in Python in `apps/api/src/adeu_api/hashing.py` / `packages/urm_runtime/src/urm_runtime/hashing.py`. v0.2 will treat these as oracle boundaries when necessary.

* **Not enforcing “non-enforcing” artifacts as policies.**
  Trust invariant generation is explicitly wrapped in a “non-enforcement context” (`apps/api/src/adeu_api/trust_invariant_vnext_plus22.py:trust_invariant_non_enforcement_context`) and the lock doc `docs/LOCKED_CONTINUATION_vNEXT_PLUS22.md` frames this family as read-only and non-enforcing.

B) Artifact-level model vs typed-level model

**Artifact-level model (what exists today, enforced in Python)**

* The artifact boundary is: **JSON payload → schema shape → contract validator**.

  * Example (Core IR): schema is `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`, model is `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR`, and the contract is enforced in `AdeuCoreIR._validate_contract`:

    ```py
    # packages/adeu_core_ir/src/adeu_core_ir/models.py
    sorted_nodes = sorted(self.nodes, key=canonical_node_sort_key)
    if self.nodes != sorted_nodes:
        raise ValueError("nodes must be sorted by (layer, kind, id)")
    ...
    if from_node is None or to_node is None:
        raise ValueError(f"dangling edge reference: from={edge.from_ref} to={edge.to_ref}")
    ...
    if from_sig not in allowed_from or to_sig not in allowed_to:
        raise ValueError(f"edge typing violation ...")
    ```
  * Stop-gate duplicates this enforcement (structural mirror) in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_validated_adeu_core_ir_payload`, with frozen kind sets and the `_ADEU_CORE_EDGE_TYPING_MATRIX`.

* Canonicalization is already a first-class operation (and it is deterministic under locks):

  * `packages/adeu_core_ir/src/adeu_core_ir/models.py:canonicalize_core_ir_payload`:

    * parses nodes/edges
    * deduplicates edges by identity
    * sorts nodes by `canonical_node_sort_key`
    * outputs JSON with `exclude_none=True` and aliasing.

**Typed-level model (what Lean should add, without changing runtime)**

* In Lean we define *typed equivalents* of the artifact structures that capture:

  * enumerated kinds (Layer, OKind/EKind/DKind/UKind, EdgeType) mirroring `packages/adeu_core_ir/src/adeu_core_ir/models.py` literals
  * node and edge records with minimal required fields for contract checks (id/layer/kind; and for ledger invariants: E node’s SBR fields)
  * a `CoreIRContract` predicate that matches `AdeuCoreIR._validate_contract` and/or stop-gate `_validate_core_ir_nodes/_validate_core_ir_edges` semantics.

* Crucially: **typed-level proofs do not replace runtime validators**; instead they:

  * prove that contract predicates imply useful corollaries (no dangling refs, edge typing discipline, etc.)
  * optionally “re-check” concrete artifacts by importing a Lean constant generated from canonicalized JSON (see bridging strategy below).

C) Canonical invariants to formalize FIRST (8–12 max, highest leverage)

Below are **10** invariants that (a) are already enforced today, (b) are deterministic under the canonical JSON locks, and (c) map cleanly to Lean “hard proofs” (structural) vs “evidence-only” (hashing/oracle).

---

**Invariant 1 — CoreIR.NodesSorted**

* **Informal statement:** `nodes` must be sorted by `(layer, kind, id)` with layer order O < E < D < U.
* **Repo enforcement hook:**

  * Validator: `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract` checks `self.nodes == sorted(self.nodes, key=canonical_node_sort_key)`.
  * Sort key definition: `packages/adeu_core_ir/src/adeu_core_ir/models.py:canonical_node_sort_key` uses `_LAYER_ORDER = {"O":0,"E":1,"D":2,"U":3}`.
  * Stop-gate usage: validation is mirrored by `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_validate_core_ir_nodes` called from `_validated_adeu_core_ir_payload`; violations surface in the vNEXT+13 metric run for `adeu_core_ir_replay_determinism_pct` (metric name frozen in `VNEXT_PLUS13_DEFAULT_METRICS`).
* **Lean theorem (rough):**

  * `theorem coreIR_nodes_sorted : CoreIRContract ir → SortedBy canonicalNodeKey ir.nodes`
* **Hard vs evidence-only:** **hard proof** (pure structural).

---

**Invariant 2 — CoreIR.EdgesSorted**

* **Informal statement:** `edges` must be sorted by `(type, from, to)`.
* **Repo enforcement hook:**

  * Validator: `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract` checks `self.edges == sorted(self.edges, key=canonical_edge_sort_key)`.
  * Sort key: `packages/adeu_core_ir/src/adeu_core_ir/models.py:canonical_edge_sort_key`.
  * Stop-gate usage: mirrored by `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_validate_core_ir_edges` (called by `_validated_adeu_core_ir_payload`).
* **Lean theorem (rough):**

  * `theorem coreIR_edges_sorted : CoreIRContract ir → SortedBy canonicalEdgeKey ir.edges`
* **Hard vs evidence-only:** **hard proof**.

---

**Invariant 3 — CoreIR.UniqueNodeIds**

* **Informal statement:** node IDs are globally unique.
* **Repo enforcement hook:**

  * Validator: `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract` builds `node_index` and rejects duplicates (`raise ValueError(f"duplicate node id: {node.id}")`).
  * Stop-gate usage: mirrored by `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_validate_core_ir_nodes` (checks duplicates).
* **Lean theorem (rough):**

  * `theorem coreIR_unique_node_ids : CoreIRContract ir → Nodup (ir.nodes.map CoreNode.id)`
* **Hard vs evidence-only:** **hard proof**.

---

**Invariant 4 — CoreIR.UniqueEdgeIdentities**

* **Informal statement:** edge identity `(type, from, to)` has no duplicates.
* **Repo enforcement hook:**

  * Validator: `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract` uses `seen_edges: set[tuple[EdgeType,str,str]]` and rejects duplicates (`duplicate edge identity`).
  * Stop-gate usage: mirrored by `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_validate_core_ir_edges` (duplicate identity check).
* **Lean theorem (rough):**

  * `theorem coreIR_unique_edge_ids : CoreIRContract ir → Nodup (ir.edges.map CoreEdge.identity)`
* **Hard vs evidence-only:** **hard proof**.

---

**Invariant 5 — CoreIR.NoDanglingEdges**

* **Informal statement:** every edge endpoint (`from`, `to`) references an existing node ID.
* **Repo enforcement hook:**

  * Validator: `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract` rejects missing endpoints (`dangling edge reference`).
  * Diagnostics artifact: `packages/adeu_core_ir/src/adeu_core_ir/integrity_dangling_reference.py:build_dangling_reference_report` emits structured diagnostics (and has its own output schema/contract).
  * Stop-gate usage: validated structurally in `_validate_core_ir_edges`; plus determinism of the dangling-reference report is tracked in stop-gate metrics (e.g., `VNEXT_PLUS16_DEFAULT_METRICS["artifact_dangling_reference_determinism_pct"]`).
* **Lean theorem (rough):**

  * `theorem coreIR_no_dangling : CoreIRContract ir → ∀ e ∈ ir.edges, e.from ∈ ids ∧ e.to ∈ ids`
* **Hard vs evidence-only:** **hard proof**.

---

**Invariant 6 — CoreIR.EdgeTypingMatrix**

* **Informal statement:** each edge type has a frozen allowed `(fromSig, toSig)` signature pair, where `sig = "<layer>.<kind>"`.
* **Repo enforcement hook:**

  * Matrix: `packages/adeu_core_ir/src/adeu_core_ir/models.py:_EDGE_TYPING_MATRIX`.
  * Validator: `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract` computes `from_sig = _node_signature(from_node)`, checks membership in `_EDGE_TYPING_MATRIX[edge.type]`.
  * Stop-gate mirror: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_ADEU_CORE_EDGE_TYPING_MATRIX` used by `_validate_core_ir_edges`.
* **Lean theorem (rough):**

  * `theorem coreIR_edge_typed : CoreIRContract ir → ∀ e ∈ ir.edges, AllowedEdge ir e`
* **Hard vs evidence-only:** **hard proof**.

---

**Invariant 7 — LaneReport.CanonicalKeysAndSortedNodeIds**

* **Informal statement:** lane report must include lane keys exactly in canonical order `["O","E","D","U"]`, and each lane’s node id list is sorted and duplicate-free.
* **Repo enforcement hook:**

  * Canonical key order is defined in `packages/adeu_core_ir/src/adeu_core_ir/lane_report.py:CANONICAL_LANE_ORDER = ("O","E","D","U")` and `_validate_lane_keys` checks key order exactly.
  * `AdeuLaneReport._validate_contract` enforces: non-empty ids, no duplicates, lexicographic sort, edge_count >= 0.
  * Stop-gate usage: lane report determinism is tracked in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:VNEXT_PLUS15_DEFAULT_METRICS["adeu_lane_report_replay_determinism_pct"]`, and fixtures are validated via corresponding payload validators in the same file.
* **Lean theorem (rough):**

  * `theorem laneReport_contract : LaneReportContract r → ...` (keys canonical ∧ per-lane sorted ∧ nodup ∧ edge_count≥0)
* **Hard vs evidence-only:** **hard proof**.

---

**Invariant 8 — ClaimLedger.RecomputeMatch**

* **Informal statement:** for each `E.Claim` node, stored SBR ledger fields match recomputation under the frozen scoring algorithm.
* **Repo enforcement hook:**

  * Algorithm: `packages/adeu_core_ir/src/adeu_core_ir/ledger.py:_compute_claim_ledger_scores` (counts supports/refutes/depends_on; computes ratios; builds `s_milli`, `b_milli`, `r_milli` and display strings).
  * Enforcement: `packages/adeu_core_ir/src/adeu_core_ir/ledger.py:assert_claim_ledger_recompute_match` raises on mismatch.
  * Stop-gate usage: metric name frozen in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:VNEXT_PLUS13_DEFAULT_METRICS["adeu_claim_ledger_recompute_match_pct"]`; enforcement via `_assert_adeu_claim_ledger_recompute_match` (same file).
* **Lean theorem (rough):**

  * `theorem claimLedger_matches : LedgerContract ir → ∀ claim, recompute claim = stored claim`
* **Hard vs evidence-only:** **hard proof** if we also formalize the scoring algorithm in Lean; **evidence-only** if we treat the algorithm as an oracle. (v0.2 recommendation: keep it evidence-only unless we commit to port `_compute_claim_ledger_scores` exactly.)

---

**Invariant 9 — TrustInvariantPacket.ProofIdAndOrdering**

* **Informal statement:** trust invariant packet includes exactly one proof item per invariant code; proof items are sorted by `(invariant_code, proof_id)`; each proof_id is a deterministic truncated sha256 of canonical JSON of the proof-id payload.
* **Repo enforcement hook:**

  * Proof-id function: `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py:build_trust_invariant_proof_id` uses `json.dumps(sort_keys=True, separators=(",", ":"), ensure_ascii=False)` then `sha256(...).hexdigest()[:16]`.
  * Contract: `.../trust_invariant_packet.py:TrustInvariantProofItem._validate_contract` recomputes and checks `proof_id`; `AdeuTrustInvariantPacket._validate_contract` enforces sorted `proof_items` and summary count consistency.
  * Stop-gate usage: validated in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_validated_trust_invariant_packet_payload`; determinism metrics names are frozen in `VNEXT_PLUS22_DEFAULT_METRICS`.
* **Lean theorem (rough):**

  * `theorem trustPacket_sorted_unique : TrustPacketContract p → SortedBy key p.proofItems ∧ ExactlyOnePerCode p.proofItems`
  * `theorem trustPacket_proofId_oracle : TrustPacketContract p → proofId = Sha16(canonicalJson(proofIdPayload))` (oracle boundary for sha256/canonical-json)
* **Hard vs evidence-only:** ordering/cardinality = **hard proof**; proof_id hash equality = **evidence-only** (hash/canonical-json oracle).

---

**Invariant 10 — ProofEvidence.HashExclusionStability**

* **Informal statement:** `proof_evidence_hash` is computed over the payload with “nonsemantic fields” stripped (timestamps, paths, operator messages, etc.). Modifying only excluded fields must not change the hash.
* **Repo enforcement hook:**

  * Exclusion set: `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py:PROOF_EVIDENCE_HASH_EXCLUDED_FIELDS` and `strip_nonsemantic_proof_fields`.
  * Hash definition: `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py:proof_evidence_hash(payload)`.
  * Stop-gate usage: proof fixtures are validated in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_proof_fixture_hash` which checks `proof_evidence_hash` equals `_proof_packet_hash` (which calls `sha256_canonical_json(strip_nonsemantic_proof_fields(payload))`).
* **Lean theorem (rough):**

  * `theorem proofHash_ignores_excluded : stripNonsemantic p1 = stripNonsemantic p2 → proofHash p1 = proofHash p2`
* **Hard vs evidence-only:** structure of strip function = **hard proof**; sha256 itself = **evidence-only**.

D) Minimal Lean module layout proposal (files + responsibilities)

**Constraint:** stay additive-only; do not modify runtime semantics. The Lean library currently is `lean_lib AdeuCore` in `packages/adeu_lean/lakefile.lean` (globs include all submodules under `AdeuCore`), and today’s modules are `packages/adeu_lean/AdeuCore/Semantics.lean` + `.../Theorems.lean` (imported by `packages/adeu_lean/AdeuCore.lean`).

**Proposal: put the new template under the existing `AdeuCore` library as `AdeuCore.ODEU.*`** (so we don’t need to touch `lakefile.lean` at all; adding new submodules is already supported by `.submodules 'AdeuCore'` in `packages/adeu_lean/lakefile.lean`).

New Lean files (additive):

1. `packages/adeu_lean/AdeuCore/ODEU/Types.lean`

   * Purpose: mirror core IR enum surfaces as Lean inductives.
   * Grounding target: match the frozen literal sets in `packages/adeu_core_ir/src/adeu_core_ir/models.py` (`Layer`, `OKind/EKind/DKind/UKind`, `EdgeType`).
   * Expose:

     * `inductive Layer | O | E | D | U`
     * `inductive EdgeType | about | defines | supports | ... | excepts`
     * `nodeSignature : Layer → Kind → String` (or typed equivalent).

2. `packages/adeu_lean/AdeuCore/ODEU/Artifacts/CoreIR.lean`

   * Purpose: Lean record types for core IR artifacts, but minimal enough to match what contract checks use.
   * Grounding target: `packages/adeu_core_ir/src/adeu_core_ir/models.py:CoreONode/CoreENode/CoreDNode/CoreUNode/CoreEdge` and schema `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`.
   * Recommendation (v0.2 minimal): include only fields used by contract checks + ledger invariants:

     * Node: `id`, `layer`, `kind`; plus for E.Claims ledger fields optionally (S/B/R milli + ledger_version + spans if needed).
     * Edge: `type`, `from`, `to`.

3. `packages/adeu_lean/AdeuCore/ODEU/Contracts/CoreIR.lean`

   * Purpose: define `CoreIRContract : CoreIR → Prop` matching `AdeuCoreIR._validate_contract` / stop-gate validators.
   * Grounding target: `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract` and `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_validate_core_ir_nodes/_validate_core_ir_edges`.
   * Theorem stubs aligned to invariants 1–6 (sortedness, uniqueness, no dangling edges, edge typing matrix).

4. `packages/adeu_lean/AdeuCore/ODEU/Artifacts/LaneReport.lean`

   * Purpose: Lean representation + contract predicate for `AdeuLaneReport`.
   * Grounding target: `packages/adeu_core_ir/src/adeu_core_ir/lane_report.py` (`CANONICAL_LANE_ORDER`, `_validate_lane_keys`, `AdeuLaneReport._validate_contract`).

5. `packages/adeu_lean/AdeuCore/ODEU/Artifacts/TrustInvariantPacket.lean`

   * Purpose: Lean representation + contract predicate for ordering/cardinality properties of trust invariant packets.
   * Grounding target: `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py` (`build_trust_invariant_proof_id`, `TrustInvariantProofItem._validate_contract`, `AdeuTrustInvariantPacket._validate_contract`).
   * Keep sha256/canonical-json as an oracle boundary (see §2E).

6. `packages/adeu_lean/AdeuCore/ODEU/Artifacts/ProofEvidence.lean`

   * Purpose: mirror `proof_evidence@1` hash-exclusion stability semantics as a Lean proof target.
   * Grounding target: `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py:strip_nonsemantic_proof_fields` + `PROOF_EVIDENCE_HASH_EXCLUDED_FIELDS`, and stop-gate mirror in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_proof_packet_hash`.

E) JSON→Lean bridging strategy

You asked for **one primary strategy and one fallback**, with determinism and oracle boundaries explicit.

### Primary strategy (v0.2): deterministic Python → Lean *typed constant codegen* (no Lean JSON parser)

**What we do:**

1. **Validate + canonicalize in Python using the repo’s frozen implementations.**

* Core IR: run `packages/adeu_core_ir/src/adeu_core_ir/models.py:canonicalize_core_ir_payload` then `AdeuCoreIR.model_validate(...)`.
  This ensures ordering and dedup are consistent with the contract and the lock that forbids “inserting missing fields” (canonicalization uses `exclude_none=True`, and only sorts/dedups; it does not invent nulls).
* Canonical JSON profile (when we need it): use `packages/urm_runtime/src/urm_runtime/hashing.py:canonical_json` / `sha256_canonical_json` (matches lock text in `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`).

2. **Emit a Lean file that defines a `CoreIR` constant and proves `CoreIRContract coreIR`.**

* We already have a precedent for deterministic Lean wrapper generation:
  `packages/adeu_lean/src/adeu_lean/runner.py:build_wrapper_theorem_source` generates Lean code from Python inputs (imports `AdeuCore` and builds a wrapper theorem).
* v0.2 extends this pattern with a new codegen function (additive) like:

  * `build_core_ir_contract_theorem_source(core_ir_payload) -> Lean source`
  * embed the minimal `CoreIR` record (ids/layer/kind, edges) as a Lean literal
  * prove the contract via `by decide` (if we make the contract decidable) or via explicit lemmas.

**Determinism commitments:**

* **List order**: we must preserve list order exactly because the lock forbids mutating list order (`docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`). That’s why we canonicalize first (e.g., `canonicalize_core_ir_payload`) and then serialize to Lean in that canonical order.
* **Unicode normalization**:

  * For invariants that depend on normalization (deontic conflict grouping), the repo uses `unicodedata.normalize("NFC", ...)` + whitespace collapse + `.casefold()` in `packages/adeu_core_ir/src/adeu_core_ir/integrity_deontic_conflict.py:_normalize_text`.
  * v0.2 recommendation: treat normalization as an oracle boundary unless/until we port that exact normalization semantics to Lean (Lean’s Unicode normalization story is not defined in this repo; so implementing it would be “inventing” behavior).

**Hashing / sha256 oracle boundary:**

* Anything that depends on sha256 (e.g., trust invariant `proof_id`, proof_evidence_hash, SEMANTICS_v3 json_path_hash) is *defined* in Python using the frozen profile:

  * `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py:build_trust_invariant_proof_id`
  * `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py:proof_evidence_hash`
  * `packages/adeu_kernel/src/adeu_kernel/checker.py:_json_path_hash`
* In Lean v0.2, we model sha256 as an opaque function and prove only *structural* facts (e.g., exclusion stability reduces to equality of stripped payloads), while treating the final sha256 equality as “evidence-only” unless we commit to a verified hash implementation.

### Fallback strategy: “skeleton import” (prove contract over a minimal projection, not full JSON)

If full JSON→Lean encoding is too heavy, we can still prove the highest-leverage invariants by importing only the fields that the Python validator actually uses.

* Evidence that this is sufficient: `packages/adeu_core_ir/src/adeu_core_ir/models.py:AdeuCoreIR._validate_contract` checks:

  * node sorting via `canonical_node_sort_key` which uses only `(layer, kind, id)`
  * edge sorting via `(type, from, to)`
  * edge typing via `_node_signature(layer,kind)` and `_EDGE_TYPING_MATRIX`
  * dangling endpoints via id lookup
    It does **not** use O label text, E text, spans, etc for these structural checks.
* So fallback import defines only:

  * `nodes : List (layer, kind, id)`
  * `edges : List (type, from, to)`
  * and optionally E claim ledger fields when testing ledger invariants.

This keeps bridging deterministic and small, while staying faithful to what’s enforced today.

---

3. Implementation Plan (3 slices, repo-ready)

Slice 1: compile-clean skeleton + 2–3 “easy invariants” proved

**Goal:** land the Lean scaffolding under `AdeuCore.ODEU.*` and prove a couple of structural lemmas, without touching runtime semantics.

**New files (Lean):**

* `packages/adeu_lean/AdeuCore/ODEU/Types.lean` (mirror enums from `packages/adeu_core_ir/src/adeu_core_ir/models.py`).
* `packages/adeu_lean/AdeuCore/ODEU/Artifacts/CoreIR.lean` (minimal records).
* `packages/adeu_lean/AdeuCore/ODEU/Contracts/CoreIR.lean` (contract predicate + decidability).

**“Easy invariants” to prove first:**

* Nodes sorted ⇒ `SortedBy` property (Invariant 1).
* Edges sorted ⇒ `SortedBy` property (Invariant 2).
* Contract ⇒ no dangling edges (Invariant 5), since it’s directly encoded in the predicate mirroring `AdeuCoreIR._validate_contract`.

**Minimal acceptance test:**

* Add a new Python test mirroring the existing runner tests style:

  * Existing pattern: `packages/adeu_lean/tests/test_runner.py` calls `build_wrapper_theorem_source` and checks determinism.
  * New test: generate a tiny in-memory CoreIR skeleton, codegen a Lean file, and assert `lake build` succeeds (skip if Lean toolchain missing, like current tests do).

Slice 2: fixture-backed property checks (connect to existing fixtures / stop-gate artifacts)

**Goal:** validate that Lean contract checks agree with existing frozen fixtures.

**Repo fixtures to use (grounded):**

* `apps/api/fixtures/stop_gate/vnext_plus19/core_ir_read_surface_case_a_1.json` (contains embedded `"core_ir": { "schema":"adeu_core_ir@0.1", "nodes":[...], "edges":[...] }`).

  * This is discoverable by the literal `"schema":"adeu_core_ir@0.1"` inside the fixture file (same file path).
* Additional fixtures exist for later arcs (e.g., proposer packets under `apps/api/fixtures/stop_gate/vnext_plus25/*core_ir_proposer*`).

**New files (Python tooling, additive):**

* `packages/adeu_lean/src/adeu_lean/odeu_codegen.py` (new)

  * Load fixture JSON.
  * Extract `core_ir` payload (or other artifact payloads).
  * Canonicalize with `packages/adeu_core_ir/src/adeu_core_ir/models.py:canonicalize_core_ir_payload`.
  * Emit Lean constants + contract theorems.

**Property checks:**

* For each fixture: `CoreIRContract` should be provable for the canonicalized payload.
* Add cross-check that Python validator accepts the same payload (`AdeuCoreIR.model_validate`), confirming alignment.

**Minimal acceptance tests:**

* `packages/adeu_lean/tests/test_odeu_fixtures.py`:

  * iterate a small fixed fixture list (start with 1–2)
  * run codegen + Lean check
  * assert proof passes.

Slice 3: expansion to cross-artifact families (integrity, trust-invariant packets, etc.)

**Goal:** produce Lean-backed evidence artifacts **without altering runtime semantics**.

**Scope additions:**

* Trust invariant packets:

  * Schema/model: `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py`
  * Stop-gate determinism metrics: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:VNEXT_PLUS22_DEFAULT_METRICS`
* Proof evidence packets:

  * Schema/model: `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py` (`PROOF_EVIDENCE_SCHEMA = "proof_evidence@1"`, `build_proof_evidence_packet`)
  * Stop-gate fixture hashing/validation: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_proof_fixture_hash`

**Additive integration path (no runtime semantics change):**

* When Lean proves `CoreIRContract` (or other artifact contracts), emit a **`proof_evidence@1` packet** using `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py:build_proof_evidence_packet`.

  * This reuses an existing, already stop-gate-recognized evidence family.
  * It also aligns with the lock that canonical JSON/hashing must be deterministic (`docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`) because proof_evidence_hash uses `_canonical_json(ensure_ascii=False, separators=(",", ":"), sort_keys=True)`.

**Minimal acceptance tests:**

* Add one proof-evidence fixture and ensure stop-gate hashing validates it via `_proof_fixture_hash` in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`.
* Add a determinism test that modifying only excluded fields (e.g., `created_at`) does not change `proof_evidence_hash` (grounded by `PROOF_EVIDENCE_HASH_EXCLUDED_FIELDS` in `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`).

---

4. “Red Flags / Gaps in v1 output” 

Below are concrete issues where **lean.md (v1)** makes claims that do **not** match the repo. Each item includes the repo-grounded correction.

**RF-1 — Incorrect edge typing claims for `defines`**

* **What v1 claims:** `defines` edges are only from `E.Evidence` → `O.Concept|O.RelationType`. 
* **Repo reality (core IR contract):**

  * `_EDGE_TYPING_MATRIX["defines"]` explicitly allows **both** `"E.Claim"` and `"E.Evidence"` as sources:

    ```py
    # packages/adeu_core_ir/src/adeu_core_ir/models.py
    "defines": ({"E.Claim", "E.Evidence"}, {"O.Concept", "O.RelationType"})
    ```
  * Stop-gate mirror matches this in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_ADEU_CORE_EDGE_TYPING_MATRIX["defines"]`.
* **Why it matters:** Any Lean formalization that “locks” defines to Evidence-only would reject valid artifacts and violate “repo-grounded” constraints.

**RF-2 — Incorrect edge typing claims for `gates`**

* **What v1 claims:** `gates` targets include `D.Norm` and `D.Policy`. 
* **Repo reality:**

  * `_EDGE_TYPING_MATRIX["gates"]` is **from `D.Policy` to E-layer only**:

    ```py
    # packages/adeu_core_ir/src/adeu_core_ir/models.py
    "gates": ({"D.Policy"}, {"E.Claim", "E.Assumption", "E.Question"})
    ```
* **Why it matters:** This is a layer-discipline invariant; getting it wrong breaks “ODEU separation” proofs.

**RF-3 — Incorrect edge typing claims for `serves_goal`**

* **What v1 claims:** only from D.* to `U.Goal` (excluding E claims, excluding U.Metric). 
* **Repo reality:**

  * Source set includes `E.Claim`, and target set includes both `U.Goal` and `U.Metric`:

    ```py
    # packages/adeu_core_ir/src/adeu_core_ir/models.py
    "serves_goal": (
        {"D.PhysicalConstraint", "D.Norm", "D.Policy", "E.Claim"},
        {"U.Goal", "U.Metric"},
    )
    ```

**RF-4 — Incorrect edge typing claims for `prioritizes`**

* **What v1 claims:** targets include `U.Preference`; misses `D.Exception`. 
* **Repo reality:**

  * `prioritizes` originates from `U.Preference` and targets `{U.Goal,U.Metric,D.PhysicalConstraint,D.Norm,D.Policy,D.Exception}` — **not** `U.Preference`:

    ```py
    # packages/adeu_core_ir/src/adeu_core_ir/models.py
    "prioritizes": (
        {"U.Preference"},
        {"U.Goal", "U.Metric", "D.PhysicalConstraint", "D.Norm", "D.Policy", "D.Exception"},
    )
    ```

**RF-5 — “ledger_version required when *_milli present” is NOT enforced**

* **What v1 claims:** if an E node has any `*_milli` field, it must have `ledger_version = "adeu.sbr.v0_1"`. 
* **Repo reality:**

  * `CoreENode._validate_ledger_fields` only checks: **if** `ledger_version` is present, it must equal `"adeu.sbr.v0_1"`. It does **not** require ledger_version when milli fields are present:

    ```py
    # packages/adeu_core_ir/src/adeu_core_ir/models.py
    if self.ledger_version is not None and self.ledger_version != "adeu.sbr.v0_1":
        raise ValueError(...)
    ```
  * The schema also permits `ledger_version: null` independently (`packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json` shows `ledger_version` as `anyOf const "adeu.sbr.v0_1" or null`).
* **Why it matters:** A Lean “must-have-ledger_version” invariant would be stronger than the repo’s contract and would violate the “do not invent/enforce new semantics” lock.

**RF-6 — Risk of proposing new schema families / new trust invariant codes**

* **Potential v1 drift:** v1 discusses new proof packets / expanded invariants beyond frozen ones (depending on interpretation). 
* **Repo constraint:** trust invariant codes are frozen in `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py:TrustInvariantCode` (exactly four: `CANONICAL_JSON_CONFORMANCE`, `HASH_RECOMPUTE_MATCH`, `REPLAY_HASH_STABILITY`, `MANIFEST_CHAIN_STABILITY`). Adding new codes would violate both the model and the lock framing in `docs/LOCKED_CONTINUATION_vNEXT_PLUS22.md`.
* **v0.2 correction:** use existing `proof_evidence@1` (`packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`) as the export contract for Lean proofs instead of inventing new trust packet families/codes.

---

If you want, I can also produce a **concrete v0.2 “skeleton Lean API”** (names + signatures) that *exactly* mirrors `AdeuCoreIR._validate_contract` and stop-gate `_validate_core_ir_*` semantics, but the above already pins every proposed invariant and integration step to a specific repo file + symbol, while correcting v1’s unsupported assumptions.
