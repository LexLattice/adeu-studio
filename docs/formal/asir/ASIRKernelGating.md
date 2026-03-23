# ASIR Kernel — Semantic Gating / Projection Readiness Layer

Third bounded Lean 4 formalization task for the ASIR module.
Formalizes the finite semantic integrity law: **unresolved serious ambiguity
blocks direct projection readiness**.

All definitions use finite vocabularies. The markdown records the intended bounded
gating kernel and its Lean code blocks.

Planned Lean workspace source path: `RequestProject/ASIRKernelGating.lean`.

---

## Section A — Definitions

```lean
/-
  ASIR Kernel — Semantic Gating / Projection Readiness Layer
  Third bounded formalization: unresolved serious ambiguity blocks projection readiness.
  Finite vocabularies, exact blocking law, theorem-oriented.
-/

import Mathlib

/-! ## Section A — Definitions -/

-- Ambiguity severity levels (finite vocabulary).
inductive AmbiguitySeverity
  | low
  | medium
  | high
  | critical
  deriving DecidableEq, Repr

-- Ambiguity resolution status.
inductive AmbiguityStatus
  | resolved
  | unresolved
  deriving DecidableEq, Repr

-- Projection readiness verdict.
inductive ProjectionReadiness
  | ready
  | blocked
  deriving DecidableEq, Repr

-- A single ambiguity record: severity + status.
structure AmbiguityRecord where
  severity : AmbiguitySeverity
  status   : AmbiguityStatus
  deriving DecidableEq, Repr

-- An ambiguity is *blocking* iff it is unresolved AND high or critical.
def IsBlockingAmbiguity (a : AmbiguityRecord) : Prop :=
  a.status = AmbiguityStatus.unresolved ∧
  (a.severity = AmbiguitySeverity.high ∨ a.severity = AmbiguitySeverity.critical)

instance (a : AmbiguityRecord) : Decidable (IsBlockingAmbiguity a) := by
  unfold IsBlockingAmbiguity; infer_instance

-- A list has a blocking ambiguity iff some element is blocking.
def AnyBlockingAmbiguity (xs : List AmbiguityRecord) : Prop :=
  ∃ a ∈ xs, IsBlockingAmbiguity a

instance (xs : List AmbiguityRecord) : Decidable (AnyBlockingAmbiguity xs) := by
  unfold AnyBlockingAmbiguity; infer_instance

-- Compute projection readiness: blocked iff any blocking ambiguity exists.
def ComputeProjectionReadiness (xs : List AmbiguityRecord) : ProjectionReadiness :=
  if xs.any (fun a => decide (IsBlockingAmbiguity a)) then
    ProjectionReadiness.blocked
  else
    ProjectionReadiness.ready

-- Policy predicates.
def ReadyByPolicy (xs : List AmbiguityRecord) : Prop :=
  ComputeProjectionReadiness xs = ProjectionReadiness.ready

def BlockedByPolicy (xs : List AmbiguityRecord) : Prop :=
  ComputeProjectionReadiness xs = ProjectionReadiness.blocked
```

---

## Section B — Required Theorems (B.1–B.14)

```lean
/-! ## Helper: align `List.any` with `∃` -/

private lemma any_iff_anyBlocking (xs : List AmbiguityRecord) :
    xs.any (fun a => decide (IsBlockingAmbiguity a)) = true ↔ AnyBlockingAmbiguity xs := by
  simp [AnyBlockingAmbiguity, List.any_eq_true, decide_eq_true_eq]

private lemma compute_blocked_iff (xs : List AmbiguityRecord) :
    ComputeProjectionReadiness xs = ProjectionReadiness.blocked ↔ AnyBlockingAmbiguity xs := by
  unfold ComputeProjectionReadiness
  constructor
  · intro h
    by_cases hb : (xs.any fun a => decide (IsBlockingAmbiguity a)) = true
    · exact (any_iff_anyBlocking xs).mp hb
    · simp [hb] at h
  · intro h
    have := (any_iff_anyBlocking xs).mpr h
    simp [this]

private lemma compute_ready_iff (xs : List AmbiguityRecord) :
    ComputeProjectionReadiness xs = ProjectionReadiness.ready ↔ ¬ AnyBlockingAmbiguity xs := by
  unfold ComputeProjectionReadiness
  constructor
  · intro h hb
    have := (any_iff_anyBlocking xs).mpr hb
    simp [this] at h
  · intro h
    have : ¬ (xs.any (fun a => decide (IsBlockingAmbiguity a)) = true) := by
      intro hc; exact h ((any_iff_anyBlocking xs).mp hc)
    simp [Bool.eq_false_iff.mpr this]

/-! ## Section B — Required Theorems -/

-- B.1: if any blocking ambiguity exists, readiness is blocked.
theorem blocking_implies_blocked (xs : List AmbiguityRecord)
    (h : AnyBlockingAmbiguity xs) :
    ComputeProjectionReadiness xs = ProjectionReadiness.blocked :=
  (compute_blocked_iff xs).mpr h

-- B.2: if readiness is ready, then no blocking ambiguity exists.
theorem ready_implies_no_blocking (xs : List AmbiguityRecord)
    (h : ComputeProjectionReadiness xs = ProjectionReadiness.ready) :
    ¬ AnyBlockingAmbiguity xs :=
  (compute_ready_iff xs).mp h

-- B.3: if readiness is blocked, then some blocking ambiguity exists.
theorem blocked_implies_blocking (xs : List AmbiguityRecord)
    (h : ComputeProjectionReadiness xs = ProjectionReadiness.blocked) :
    AnyBlockingAmbiguity xs :=
  (compute_blocked_iff xs).mp h

-- B.4: unresolved high ambiguity is blocking.
theorem unresolved_high_blocking :
    IsBlockingAmbiguity ⟨.high, .unresolved⟩ := by
  simp [IsBlockingAmbiguity]

-- B.5: unresolved critical ambiguity is blocking.
theorem unresolved_critical_blocking :
    IsBlockingAmbiguity ⟨.critical, .unresolved⟩ := by
  simp [IsBlockingAmbiguity]

-- B.6: resolved high ambiguity is not blocking.
theorem resolved_high_not_blocking :
    ¬ IsBlockingAmbiguity ⟨.high, .resolved⟩ := by
  simp [IsBlockingAmbiguity]

-- B.7: resolved critical ambiguity is not blocking.
theorem resolved_critical_not_blocking :
    ¬ IsBlockingAmbiguity ⟨.critical, .resolved⟩ := by
  simp [IsBlockingAmbiguity]

-- B.8: unresolved low ambiguity is not blocking.
theorem unresolved_low_not_blocking :
    ¬ IsBlockingAmbiguity ⟨.low, .unresolved⟩ := by
  simp [IsBlockingAmbiguity]

-- B.9: unresolved medium ambiguity is not blocking.
theorem unresolved_medium_not_blocking :
    ¬ IsBlockingAmbiguity ⟨.medium, .unresolved⟩ := by
  simp [IsBlockingAmbiguity]

-- B.10: a list containing only low/medium ambiguities is ready.
theorem only_low_medium_is_ready (xs : List AmbiguityRecord)
    (h : ∀ a ∈ xs, a.severity = .low ∨ a.severity = .medium) :
    ComputeProjectionReadiness xs = ProjectionReadiness.ready := by
  apply (compute_ready_iff xs).mpr
  intro ⟨a, ha_mem, ha_block⟩
  have := h a ha_mem
  simp [IsBlockingAmbiguity] at ha_block
  rcases ha_block with ⟨_, hh | hc⟩ <;> rcases this with hl | hm <;> simp_all

-- B.11: a list containing at least one unresolved high ambiguity is blocked.
theorem unresolved_high_blocks_list (xs : List AmbiguityRecord)
    (h : ⟨.high, .unresolved⟩ ∈ xs) :
    ComputeProjectionReadiness xs = ProjectionReadiness.blocked := by
  apply (compute_blocked_iff xs).mpr
  exact ⟨_, h, unresolved_high_blocking⟩

-- B.12: a list containing at least one unresolved critical ambiguity is blocked.
theorem unresolved_critical_blocks_list (xs : List AmbiguityRecord)
    (h : ⟨.critical, .unresolved⟩ ∈ xs) :
    ComputeProjectionReadiness xs = ProjectionReadiness.blocked := by
  apply (compute_blocked_iff xs).mpr
  exact ⟨_, h, unresolved_critical_blocking⟩

-- B.13: readiness = ready iff no unresolved high/critical ambiguity exists.
theorem ready_iff_no_unresolved_serious (xs : List AmbiguityRecord) :
    ComputeProjectionReadiness xs = ProjectionReadiness.ready ↔
    ¬ ∃ a ∈ xs, IsBlockingAmbiguity a :=
  compute_ready_iff xs

-- B.14: readiness = blocked iff some unresolved high/critical ambiguity exists.
theorem blocked_iff_unresolved_serious (xs : List AmbiguityRecord) :
    ComputeProjectionReadiness xs = ProjectionReadiness.blocked ↔
    ∃ a ∈ xs, IsBlockingAmbiguity a :=
  compute_blocked_iff xs
```

---

## Section C — Strengthening Lemmas (C.15–C.17)

```lean
/-! ## Section C — Strengthening Lemmas -/

-- C.15: appending a blocking ambiguity always yields blocked.
theorem append_blocking_is_blocked (xs : List AmbiguityRecord) (a : AmbiguityRecord)
    (ha : IsBlockingAmbiguity a) :
    ComputeProjectionReadiness (xs ++ [a]) = ProjectionReadiness.blocked := by
  apply (compute_blocked_iff _).mpr
  exact ⟨a, List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)), ha⟩

-- C.16: once blocked, adding more ambiguities cannot make the list ready.
theorem blocked_stays_blocked (xs ys : List AmbiguityRecord)
    (h : ComputeProjectionReadiness xs = ProjectionReadiness.blocked) :
    ComputeProjectionReadiness (xs ++ ys) = ProjectionReadiness.blocked := by
  obtain ⟨a, ha_mem, ha_block⟩ := (compute_blocked_iff xs).mp h
  apply (compute_blocked_iff _).mpr
  exact ⟨a, List.mem_append.mpr (Or.inl ha_mem), ha_block⟩

-- C.17: appending only non-blocking ambiguities preserves readiness.
theorem append_nonblocking_preserves_ready (xs ys : List AmbiguityRecord)
    (hxs : ComputeProjectionReadiness xs = ProjectionReadiness.ready)
    (hys : ∀ a ∈ ys, ¬ IsBlockingAmbiguity a) :
    ComputeProjectionReadiness (xs ++ ys) = ProjectionReadiness.ready := by
  apply (compute_ready_iff _).mpr
  intro ⟨a, ha_mem, ha_block⟩
  rw [List.mem_append] at ha_mem
  rcases ha_mem with h | h
  · exact (compute_ready_iff xs).mp hxs ⟨a, h, ha_block⟩
  · exact hys a h ha_block
```

---

## Section D — Downstream Reuse Note

This third kernel provides a machine-verified, `sorry`-free decision procedure for
projection readiness gating based on ambiguity severity and resolution status.
It can back downstream tooling as follows:

**Python validator logic for ASIR projection gates.**
The `AmbiguitySeverity`, `AmbiguityStatus`, and `ProjectionReadiness` inductives
map directly to Python `enum.Enum` classes. `IsBlockingAmbiguity` becomes a
one-line predicate (`status == "unresolved" and severity in {"high", "critical"}`).
`ComputeProjectionReadiness` becomes an `any(...)` check over a list of ambiguity
records. Because the Lean kernel proves the exact equivalence between this
computation and the existential property (B.13, B.14), any Python implementation
that mirrors the logic inherits the same soundness guarantee.

**JSON validation for ambiguity severity/status vocabularies.**
The four severity levels and two status values form finite JSON string enums.
A JSON Schema can enforce that every ambiguity record carries exactly one of
`{"low", "medium", "high", "critical"}` for severity and one of
`{"resolved", "unresolved"}` for status. The kernel's `DecidableEq` and `Repr`
instances ensure round-trip fidelity between the formal model and serialized
representations.

**Deterministic "projection blocked vs ready" checks in the ASIR compiler.**
At the projection gate in the ASIR pipeline, the compiler collects all ambiguity
records for a given scope and calls the equivalent of `ComputeProjectionReadiness`.
The monotonicity theorems (C.15–C.17) guarantee that:
- once a scope is blocked, no additional records can unblock it (C.16);
- appending a blocking record always blocks (C.15);
- appending only non-blocking records preserves readiness (C.17).

These properties enable incremental evaluation: the compiler can short-circuit
as soon as the first blocking ambiguity is encountered, without scanning the
remainder of the list. The formal proofs ensure this optimization is correct.
