Here’s the **high-level guidance to hand Codex** so it can write the first consolidated draft plan (without you having to pre-decide everything).

---

## 1) Tell Codex what the “consolidated plan” must contain (and must not)

**Deliverable shape (single doc, house style):**

1. **Repo-grounded baseline snapshot**

   * State the latest locked arc reality (“latest locked is vNext+26; next vNext number unknown → use vNext+27+ placeholders”). 
   * List the *actual* hotspots / mismatches discovered in repo (not just abstract advice).

2. **Three workstreams, kept distinct but cross-linked**

   * **Tooling/Determinism hardening & refactors** (from reviewv2).
   * **Product/UX evidence browsing ladder** (from next-arc v2).
   * **Formal verification / Lean ODEU template** (from lean v2).

3. **An interleaving roadmap**

   * Provide **2–3 candidate sequences** + **one recommended sequence**, explicitly calling out prerequisites, stop-gate impact, and risk.
   * Enforce “single-arc lock docs” style (no multi-version bundles). 

4. **Do NOT write a mega “final spec”**

   * The consolidated plan should be a **draft lock-chain proposal** + **diff-oriented PR slices**, not a rewritten SEMANTICS or a big redesign.

---

## 2) Hard constraints Codex must preserve while consolidating

These are the “don’t accidentally break the project” constraints that appear across lanes:

* **Stop-gate metrics discipline:** only add metric keys when introducing a new evidence family; UI-only arcs should have *no stop-gate impact*. 
* **No silent drift vs locks:** e.g., the v26 path normalization allowlist mismatch is explicitly called out as a real repo risk—must be addressed in a behavior-preserving way + tests. 
* **Fixture-first reality:** cross-IR pairing/coherence is currently “catalog authority,” not free-form “session” work; product plans must respect that until explicitly released. 
* **Formal lane is additive & oracle-bounded:** Lean should prove structural invariants that mirror existing contract validators; sha256/canonical-json remain “oracle boundary” (evidence-only).  

---

## 3) What Codex should “merge” from each lane (the essence)

### A) From `reviewv2.md` (implementation assessment → actionable refactor arcs)

Codex should extract **(i)** the top verified issues, **(ii)** the minimal diffs, **(iii)** the thin-slice arcs.

Key repo facts to surface:

* “God modules” + mixed responsibilities: `stop_gate_tools.py` (~15k LOC) and `apps/api/.../main.py` (~7.4k LOC). 
* Canonical JSON/hashing duplication across multiple layers. 
* Concrete high-ROI diffs: deterministic tooling env helper, stop-gate manifest registry single-source, v26 parity allowlist normalization, policy packaged-vs-repo sync tests, Lean runner deterministic temp filename.  

**How to represent in the consolidated plan:**

* Put these as **“Immediate reliability arcs”** (vNext+27..vNext+29 placeholders) with *no metric churn* where possible. 

### B) From `next arcv2.md` (territory roadmap → product ladder + constraints)

Codex should extract:

* The critique points (“don’t assume cross-IR sessions are ‘easy’; it’s fixture-first; don’t add stop-gate keys freely; keep arcs single-version”). 
* The product ladder recommendation (read-only evidence explorer first, then progressively richer panels/safe-write later). 

**How to represent in the consolidated plan:**

* A “**Product UX track**” that explicitly reuses existing safe-write patterns and stays read-only until a later lock release. 

### C) From `leanv2.md` (formal template → Lean module plan + proof targets)

Codex should extract:

* The **Lean layout** under `AdeuCore.ODEU.*` (additive, no lakefile surgery required). 
* The split between **hard proofs** (ordering/cardinality/contract invariants) and **evidence-only** (sha256/canonical-json). 
* The **3-slice implementation plan**: skeleton + easy invariants → fixture-backed agreement checks → expand to more artifact families. 

**How to represent in the consolidated plan:**

* A “**Formal lane track**” that is *explicitly orthogonal* to product UX and refactors, but depends on shared canonical-json/hashing definitions staying stable. 

---

## 4) The consolidation “join points” Codex must explicitly call out

This is where the lanes overlap and Codex must pick a single coherent rule:

1. **One shared helper for deterministic “created_at stripping”**

   * It appears across later evidence families; v22 already pushes toward a shared deterministic helper. Codex should treat this as a platform primitive, not re-implemented ad hoc. 

2. **One canonical-json conformance test suite across layers**

   * Review lane wants a conformance test spanning API/runtime/kernel implementations. 
   * Lean lane treats canonical-json/sha256 as oracle—so conformance tests become the “oracle integrity fence.” 

3. **Stop-gate tooling modularization is a prerequisite for scaling more arcs**

   * Central manifest registry + smaller modules reduces future drift cost. 

4. **Product evidence explorer should *not* invent new evidence**

   * It should browse what exists (fixture-first), and only later do “session” expansions. 

---

## 5) What to ask Codex to output (very specific)

Give Codex this checklist:

* Produce a **“Consolidated Territory Plan v0”** doc with:

  * **Section 1:** Current repo truth + risk register (top 10 issues w/ file paths).
  * **Section 2:** Three workstreams (Tooling / Product / Formal) each with:

    * purpose
    * constraints/locks it must obey
    * thin-slice arc proposals (vNext+27+ placeholders)
    * stop-gate impact (explicitly “none” when applicable)
  * **Section 3:** 2–3 roadmap sequences + one recommended merge ordering.
  * **Section 4:** Cross-stream shared primitives (canonical-json conformance, deterministic env enforcement, created_at stripping).
  * **Section 5:** Immediate “small-green” PR slicing for the first 1–2 arcs.

* The plan must quote **repo paths** and **match house lock tone**, and keep arcs single-version, step-block style.


