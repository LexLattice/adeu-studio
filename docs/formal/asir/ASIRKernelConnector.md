# ASIR Kernel — Adjudication-to-Projection Connector Layer

Fourth bounded Lean 4 formalization task for the ASIR module.
Bridges Kernel 2 (hybrid checkpoint adjudication) and Kernel 3
(blocking ambiguity / projection readiness) via an exact finite connector law:
**how checkpoint adjudication changes ambiguity status for projection gating**.

All definitions use finite vocabularies. All 16 theorems are proof-complete
(zero `sorry`). Only standard axioms (`propext`, `Quot.sound`).

The compilable source is `RequestProject/ASIRKernelConnector.lean`.

---

## Section A — Definitions

```lean
/-
  ASIR Kernel — Adjudication-to-Projection Connector Layer
  Fourth bounded formalization: how checkpoint adjudication changes
  ambiguity status for projection gating.

  Bridges Kernel 2 (hybrid checkpoint adjudication) and Kernel 3
  (blocking ambiguity / projection readiness).

  Finite vocabularies, exact connector law, theorem-oriented.
-/

import RequestProject.ASIRKernel
import RequestProject.ASIRKernelGating

/-! ## Section A — Definitions -/

-- Reused from Kernel 1: FinalAdjudication (.resolvedPass, .resolvedFail, .escalatedHuman)
-- Reused from Kernel 3: AmbiguitySeverity, AmbiguityStatus, ProjectionReadiness,
--   AmbiguityRecord, IsBlockingAmbiguity, ComputeProjectionReadiness

-- Apply an adjudication outcome to an ambiguity status.
-- Law: resolved stays resolved; unresolved is resolved by resolvedPass/resolvedFail,
-- but remains unresolved under escalatedHuman.
def ApplyAdjudicationToStatus : AmbiguityStatus → FinalAdjudication → AmbiguityStatus
  | .resolved,   _                        => .resolved
  | .unresolved, .resolvedPass             => .resolved
  | .unresolved, .resolvedFail             => .resolved
  | .unresolved, .escalatedHuman           => .unresolved

-- Apply adjudication to an ambiguity record: same severity, updated status.
def ApplyAdjudicationToAmbiguity (a : AmbiguityRecord) (f : FinalAdjudication) : AmbiguityRecord :=
  { severity := a.severity, status := ApplyAdjudicationToStatus a.status f }

-- Apply adjudication uniformly over a list of ambiguity records.
def ApplyAdjudicationToList (xs : List AmbiguityRecord) (f : FinalAdjudication) : List AmbiguityRecord :=
  xs.map (fun a => ApplyAdjudicationToAmbiguity a f)
```

---

## Section B — Required Theorems (B.1–B.12)

```lean
/-! ## Section B — Required Theorems -/

-- B.1: resolvedPass on unresolved high → non-blocking
theorem adjudication_resolvedPass_high_nonblocking :
    ¬ IsBlockingAmbiguity (ApplyAdjudicationToAmbiguity ⟨.high, .unresolved⟩ .resolvedPass) := by
  simp [ApplyAdjudicationToAmbiguity, ApplyAdjudicationToStatus, IsBlockingAmbiguity]

-- B.2: resolvedFail on unresolved high → non-blocking
theorem adjudication_resolvedFail_high_nonblocking :
    ¬ IsBlockingAmbiguity (ApplyAdjudicationToAmbiguity ⟨.high, .unresolved⟩ .resolvedFail) := by
  simp [ApplyAdjudicationToAmbiguity, ApplyAdjudicationToStatus, IsBlockingAmbiguity]

-- B.3: resolvedPass on unresolved critical → non-blocking
theorem adjudication_resolvedPass_critical_nonblocking :
    ¬ IsBlockingAmbiguity (ApplyAdjudicationToAmbiguity ⟨.critical, .unresolved⟩ .resolvedPass) := by
  simp [ApplyAdjudicationToAmbiguity, ApplyAdjudicationToStatus, IsBlockingAmbiguity]

-- B.4: resolvedFail on unresolved critical → non-blocking
theorem adjudication_resolvedFail_critical_nonblocking :
    ¬ IsBlockingAmbiguity (ApplyAdjudicationToAmbiguity ⟨.critical, .unresolved⟩ .resolvedFail) := by
  simp [ApplyAdjudicationToAmbiguity, ApplyAdjudicationToStatus, IsBlockingAmbiguity]

-- B.5: escalatedHuman on unresolved high → still blocking
theorem adjudication_escalatedHuman_high_blocking :
    IsBlockingAmbiguity (ApplyAdjudicationToAmbiguity ⟨.high, .unresolved⟩ .escalatedHuman) := by
  simp [ApplyAdjudicationToAmbiguity, ApplyAdjudicationToStatus, IsBlockingAmbiguity]

-- B.6: escalatedHuman on unresolved critical → still blocking
theorem adjudication_escalatedHuman_critical_blocking :
    IsBlockingAmbiguity (ApplyAdjudicationToAmbiguity ⟨.critical, .unresolved⟩ .escalatedHuman) := by
  simp [ApplyAdjudicationToAmbiguity, ApplyAdjudicationToStatus, IsBlockingAmbiguity]

-- B.7: any adjudication on an already-resolved ambiguity keeps it non-blocking
theorem adjudication_resolved_stays_nonblocking (s : AmbiguitySeverity) (f : FinalAdjudication) :
    ¬ IsBlockingAmbiguity (ApplyAdjudicationToAmbiguity ⟨s, .resolved⟩ f) := by
  cases s <;> cases f <;> simp [ApplyAdjudicationToAmbiguity, ApplyAdjudicationToStatus, IsBlockingAmbiguity]

-- Helper: after resolvedPass or resolvedFail, status is always resolved
private lemma apply_status_resolvedPass_unresolved :
    ApplyAdjudicationToStatus .unresolved .resolvedPass = .resolved := rfl

private lemma apply_status_resolvedFail_unresolved :
    ApplyAdjudicationToStatus .unresolved .resolvedFail = .resolved := rfl

private lemma apply_status_resolved (f : FinalAdjudication) :
    ApplyAdjudicationToStatus .resolved f = .resolved := by cases f <;> rfl

private lemma apply_status_always_resolved_pass (s : AmbiguityStatus) :
    ApplyAdjudicationToStatus s .resolvedPass = .resolved := by cases s <;> rfl

private lemma apply_status_always_resolved_fail (s : AmbiguityStatus) :
    ApplyAdjudicationToStatus s .resolvedFail = .resolved := by cases s <;> rfl

-- B.8: if every blocking ambiguity in a list receives resolvedPass, then the result is ready
theorem adjudication_resolvedPass_clears_all (xs : List AmbiguityRecord) :
    ComputeProjectionReadiness (ApplyAdjudicationToList xs .resolvedPass) = ProjectionReadiness.ready := by
  rw [ready_iff_no_unresolved_serious]
  intro ⟨a, ha_mem, ha_block⟩
  simp [ApplyAdjudicationToList] at ha_mem
  obtain ⟨b, _, rfl⟩ := ha_mem
  simp [IsBlockingAmbiguity, ApplyAdjudicationToAmbiguity, apply_status_always_resolved_pass] at ha_block

-- B.9: if every blocking ambiguity in a list receives resolvedFail, then the result is ready
theorem adjudication_resolvedFail_clears_all (xs : List AmbiguityRecord) :
    ComputeProjectionReadiness (ApplyAdjudicationToList xs .resolvedFail) = ProjectionReadiness.ready := by
  rw [ready_iff_no_unresolved_serious]
  intro ⟨a, ha_mem, ha_block⟩
  simp [ApplyAdjudicationToList] at ha_mem
  obtain ⟨b, _, rfl⟩ := ha_mem
  simp [IsBlockingAmbiguity, ApplyAdjudicationToAmbiguity, apply_status_always_resolved_fail] at ha_block

-- B.10: if a list contains a blocking ambiguity and receives escalatedHuman, the result remains blocked
theorem adjudication_escalatedHuman_preserves_blocked (xs : List AmbiguityRecord)
    (h : AnyBlockingAmbiguity xs) :
    ComputeProjectionReadiness (ApplyAdjudicationToList xs .escalatedHuman) = ProjectionReadiness.blocked := by
  rw [blocked_iff_unresolved_serious]
  obtain ⟨a, ha_mem, ha_block⟩ := h
  refine ⟨ApplyAdjudicationToAmbiguity a .escalatedHuman, ?_, ?_⟩
  · simp [ApplyAdjudicationToList]
    exact ⟨a, ha_mem, rfl⟩
  · obtain ⟨hs, hsev⟩ := ha_block
    simp [ApplyAdjudicationToAmbiguity, ApplyAdjudicationToStatus, IsBlockingAmbiguity, hs, hsev]

-- B.11: resolvedPass and resolvedFail both discharge semantic blockage
theorem resolvedPass_discharges_blockage (a : AmbiguityRecord) (h : IsBlockingAmbiguity a) :
    ¬ IsBlockingAmbiguity (ApplyAdjudicationToAmbiguity a .resolvedPass) := by
  obtain ⟨hs, _⟩ := h
  simp [ApplyAdjudicationToAmbiguity, IsBlockingAmbiguity, hs, apply_status_always_resolved_pass]

theorem resolvedFail_discharges_blockage (a : AmbiguityRecord) (h : IsBlockingAmbiguity a) :
    ¬ IsBlockingAmbiguity (ApplyAdjudicationToAmbiguity a .resolvedFail) := by
  obtain ⟨hs, _⟩ := h
  simp [ApplyAdjudicationToAmbiguity, IsBlockingAmbiguity, hs, apply_status_always_resolved_fail]

-- B.12: escalatedHuman does not discharge semantic blockage
theorem escalatedHuman_preserves_blockage (a : AmbiguityRecord) (h : IsBlockingAmbiguity a) :
    IsBlockingAmbiguity (ApplyAdjudicationToAmbiguity a .escalatedHuman) := by
  obtain ⟨hs, hsev⟩ := h
  simp [ApplyAdjudicationToAmbiguity, ApplyAdjudicationToStatus, IsBlockingAmbiguity, hs, hsev]
```

---

## Section C — Strengthening Lemmas (C.13–C.16)

```lean
/-! ## Section C — Strengthening Lemmas -/

-- C.13: severity is invariant under adjudication
theorem severity_invariant_under_adjudication (a : AmbiguityRecord) (f : FinalAdjudication) :
    (ApplyAdjudicationToAmbiguity a f).severity = a.severity := by
  simp [ApplyAdjudicationToAmbiguity]

-- C.14: adjudication only changes status, never severity
theorem adjudication_changes_only_status (a : AmbiguityRecord) (f : FinalAdjudication) :
    (ApplyAdjudicationToAmbiguity a f).severity = a.severity ∧
    (ApplyAdjudicationToAmbiguity a f).status = ApplyAdjudicationToStatus a.status f := by
  simp [ApplyAdjudicationToAmbiguity]

-- C.15: if a list has no blocking ambiguities, applying any adjudication preserves readiness
theorem no_blocking_preserves_readiness (xs : List AmbiguityRecord) (f : FinalAdjudication)
    (h : ComputeProjectionReadiness xs = ProjectionReadiness.ready) :
    ComputeProjectionReadiness (ApplyAdjudicationToList xs f) = ProjectionReadiness.ready := by
  rw [ready_iff_no_unresolved_serious] at h ⊢
  intro ⟨a', ha'_mem, ha'_block⟩
  simp [ApplyAdjudicationToList] at ha'_mem
  obtain ⟨a, ha_mem, rfl⟩ := ha'_mem
  have hnotblock : ¬ IsBlockingAmbiguity a := fun hb => h ⟨a, ha_mem, hb⟩
  -- The adjudicated record is blocking, so its status is unresolved and severity is high/critical
  have ⟨hstat, hsev⟩ := ha'_block
  simp [ApplyAdjudicationToAmbiguity] at hsev
  -- severity is preserved, so a.severity is high or critical
  -- hstat: status after adjudication is unresolved
  simp [ApplyAdjudicationToAmbiguity] at hstat
  -- a must have been blocking: unresolved status and high/critical severity
  have : IsBlockingAmbiguity a := by
    constructor
    · revert hstat; cases a.status <;> cases f <;>
        simp [ApplyAdjudicationToStatus]
    · exact hsev
  exact hnotblock this

-- C.16: if a list is blocked solely because of one unresolved high/critical ambiguity,
-- then applying resolvedPass or resolvedFail makes it ready
theorem single_blocker_resolved_makes_ready
    (a : AmbiguityRecord) (rest : List AmbiguityRecord)
    (_ha_block : IsBlockingAmbiguity a)
    (_hrest : ∀ r ∈ rest, ¬ IsBlockingAmbiguity r)
    (f : FinalAdjudication)
    (hf : f = .resolvedPass ∨ f = .resolvedFail) :
    ComputeProjectionReadiness (ApplyAdjudicationToList (a :: rest) f) = ProjectionReadiness.ready := by
  rcases hf with rfl | rfl
  · -- f = resolvedPass: all statuses become resolved
    exact adjudication_resolvedPass_clears_all (a :: rest)
  · -- f = resolvedFail: all statuses become resolved
    exact adjudication_resolvedFail_clears_all (a :: rest)
```

---

## Section D — Downstream Reuse Note

This fourth connector kernel provides a machine-verified, `sorry`-free bridge
between checkpoint adjudication outcomes (from Kernel 2) and projection readiness
gating (from Kernel 3). It can back downstream tooling as follows:

**Deterministic readiness recalculation after checkpoint adjudication.**
When a checkpoint adjudicates an ambiguity (via `resolvedPass`, `resolvedFail`,
or `escalatedHuman`), the runtime applies `ApplyAdjudicationToList` and then
recomputes `ComputeProjectionReadiness`. Theorems B.8–B.10 guarantee the exact
outcome: `resolvedPass` or `resolvedFail` always clear all blockage (ready),
while `escalatedHuman` preserves any existing blockage (blocked). This enables
a deterministic, single-pass readiness recalculation with no ambiguity about
the result.

**Python validator logic for ambiguity discharge.**
`ApplyAdjudicationToStatus` translates to a three-branch Python function
(`if status == "resolved": return "resolved"; elif adj in {"resolvedPass", "resolvedFail"}: return "resolved"; else: return "unresolved"`).
Theorems B.1–B.7 and B.11–B.12 certify the complete case table: any Python
validator that mirrors this logic inherits the same discharge guarantees.
The severity-invariance lemmas (C.13–C.14) confirm that adjudication never
corrupts severity data, which simplifies the validator's state-consistency checks.

**JSON / state-machine validation for checkpoint-to-readiness transitions.**
The connector law defines an exact finite transition function from
`(AmbiguityStatus × FinalAdjudication)` to `AmbiguityStatus`. This maps
directly to a JSON-Schema `oneOf` constraint or a state-machine transition
table. Theorems B.8–B.10 and C.15–C.16 certify the aggregate list-level
behavior, enabling validators to check not just individual record transitions
but whole-scope readiness outcomes. Because every theorem is machine-verified,
any generated validator inherits formal correctness without independent
re-verification.
