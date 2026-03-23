# ASIR Kernel — Hybrid Route / Checkpoint / Oracle-Emission Compatibility Layer

Second bounded Lean 4 formalization task extending the first ASIR kernel.
Covers the compatibility relations between resolution routes, checkpoint classes,
oracle emission, and final adjudication.

All definitions use finite enumerations. The markdown records the intended bounded
hybrid kernel and its Lean code blocks.

Planned Lean workspace source path: `RequestProject/ASIRKernelHybrid.lean`.

---

## Lean 4 Code

```lean
/-
  ASIR Kernel — Hybrid Route / Checkpoint / Oracle-Emission Compatibility Layer
  Extends ASIRKernel with oracle emission, route-checkpoint compatibility,
  route-adjudication compatibility, and the full triple-compatibility relation.
  All tables are finite and exact; all theorems are proof-complete.
-/

import RequestProject.ASIRKernel

open ResolutionRoute CheckpointClass FinalAdjudication

/-! ## Section A — Definitions -/

-- Oracle emission tag
inductive OracleEmission
  | noOracle
  | emitsOracle
  deriving DecidableEq, Repr

open OracleEmission

-- Which checkpoint classes each route permits
def RouteAllowsCheckpoint : ResolutionRoute → CheckpointClass → Prop
  | deterministicOnly, deterministicPass => True
  | deterministicOnly, deterministicFail => True
  | oracleAssisted,    oracleNeeded      => True
  | humanOnly,         humanNeeded       => True
  | _, _                                 => False

-- Does a checkpoint class require an oracle?
def CheckpointNeedsOracle : CheckpointClass → Prop
  | oracleNeeded => True
  | _            => False

-- Which oracle emissions each route may produce
def RouteMayEmitOracle : ResolutionRoute → OracleEmission → Prop
  | deterministicOnly, noOracle     => True
  | humanOnly,         noOracle     => True
  | oracleAssisted,    noOracle     => True
  | oracleAssisted,    emitsOracle  => True
  | _, _                            => False

-- Which adjudications each route permits
def AdjudicationAllowedByRoute : ResolutionRoute → FinalAdjudication → Prop
  | deterministicOnly, resolvedPass    => True
  | deterministicOnly, resolvedFail    => True
  | oracleAssisted,    resolvedPass    => True
  | oracleAssisted,    resolvedFail    => True
  | oracleAssisted,    escalatedHuman  => True
  | humanOnly,         escalatedHuman  => True
  | _, _                               => False

-- Full triple compatibility: route allows checkpoint, checkpoint legally
-- transitions to adjudication, and route allows that adjudication.
def RouteClassAdjudicationCompatible
    (r : ResolutionRoute) (c : CheckpointClass) (a : FinalAdjudication) : Prop :=
  RouteAllowsCheckpoint r c ∧ LegalTransition c a ∧ AdjudicationAllowedByRoute r a

/-! ## Section B — Required Theorems -/

/-! ### B.1–B.3: Route → Checkpoint exclusivity -/

-- B.1: deterministicOnly permits exactly deterministicPass or deterministicFail
theorem deterministicOnly_checkpoint_iff (c : CheckpointClass) :
    RouteAllowsCheckpoint deterministicOnly c ↔
      (c = deterministicPass ∨ c = deterministicFail) := by
  cases c <;> simp [RouteAllowsCheckpoint]

-- B.2: oracleAssisted permits exactly oracleNeeded
theorem oracleAssisted_checkpoint_iff (c : CheckpointClass) :
    RouteAllowsCheckpoint oracleAssisted c ↔ c = oracleNeeded := by
  cases c <;> simp [RouteAllowsCheckpoint]

-- B.3: humanOnly permits exactly humanNeeded
theorem humanOnly_checkpoint_iff (c : CheckpointClass) :
    RouteAllowsCheckpoint humanOnly c ↔ c = humanNeeded := by
  cases c <;> simp [RouteAllowsCheckpoint]

/-! ### B.4–B.5: Oracle need -/

-- B.4: oracleNeeded is the only checkpoint that needs oracle
theorem oracle_needed_unique (c : CheckpointClass) :
    CheckpointNeedsOracle c ↔ c = oracleNeeded := by
  cases c <;> simp [CheckpointNeedsOracle]

-- B.5: deterministicPass, deterministicFail, humanNeeded do not need oracle
theorem deterministicPass_no_oracle : ¬ CheckpointNeedsOracle deterministicPass := by
  simp [CheckpointNeedsOracle]
theorem deterministicFail_no_oracle : ¬ CheckpointNeedsOracle deterministicFail := by
  simp [CheckpointNeedsOracle]
theorem humanNeeded_no_oracle : ¬ CheckpointNeedsOracle humanNeeded := by
  simp [CheckpointNeedsOracle]

/-! ### B.6–B.8: Oracle emission -/

-- B.6: deterministicOnly never emits oracle
theorem deterministicOnly_no_emit : ¬ RouteMayEmitOracle deterministicOnly emitsOracle := by
  simp [RouteMayEmitOracle]

-- B.7: humanOnly never emits oracle
theorem humanOnly_no_emit : ¬ RouteMayEmitOracle humanOnly emitsOracle := by
  simp [RouteMayEmitOracle]

-- B.8: oracleAssisted is the only route that may emit emitsOracle
theorem emitsOracle_only_oracleAssisted (r : ResolutionRoute) :
    RouteMayEmitOracle r emitsOracle → r = oracleAssisted := by
  cases r <;> simp [RouteMayEmitOracle]

/-! ### B.9–B.11: Route-constrained adjudication -/

-- B.9: checkpoints allowed by deterministicOnly adjudicate only to resolvedPass or resolvedFail
theorem deterministicOnly_adjudication (c : CheckpointClass) (a : FinalAdjudication)
    (hrc : RouteAllowsCheckpoint deterministicOnly c) (hlt : LegalTransition c a) :
    a = resolvedPass ∨ a = resolvedFail := by
  cases c <;> cases a <;> simp_all [RouteAllowsCheckpoint, LegalTransition]

-- B.10: checkpoints allowed by humanOnly adjudicate only to escalatedHuman
theorem humanOnly_adjudication (c : CheckpointClass) (a : FinalAdjudication)
    (hrc : RouteAllowsCheckpoint humanOnly c) (hlt : LegalTransition c a) :
    a = escalatedHuman := by
  cases c <;> cases a <;> simp_all [RouteAllowsCheckpoint, LegalTransition]

-- B.11: checkpoints allowed by oracleAssisted adjudicate to resolvedPass, resolvedFail, or escalatedHuman
theorem oracleAssisted_adjudication (c : CheckpointClass) (a : FinalAdjudication)
    (hrc : RouteAllowsCheckpoint oracleAssisted c) (hlt : LegalTransition c a) :
    a = resolvedPass ∨ a = resolvedFail ∨ a = escalatedHuman := by
  cases c <;> cases a <;> simp_all [RouteAllowsCheckpoint, LegalTransition]

/-! ### B.12–B.14: Route/checkpoint entailment -/

-- B.12: oracle-needing checkpoint forces oracleAssisted route
theorem oracle_checkpoint_forces_route (r : ResolutionRoute) (c : CheckpointClass)
    (hrc : RouteAllowsCheckpoint r c) (ho : CheckpointNeedsOracle c) :
    r = oracleAssisted := by
  cases r <;> cases c <;> simp_all [RouteAllowsCheckpoint, CheckpointNeedsOracle]

-- B.13: humanOnly forces humanNeeded checkpoint
theorem humanOnly_forces_humanNeeded (r : ResolutionRoute) (c : CheckpointClass)
    (hrc : RouteAllowsCheckpoint r c) (hr : r = humanOnly) :
    c = humanNeeded := by
  subst hr; cases c <;> simp_all [RouteAllowsCheckpoint]

-- B.14: deterministicOnly forces deterministicPass or deterministicFail
theorem deterministicOnly_forces_det_checkpoint (r : ResolutionRoute) (c : CheckpointClass)
    (hrc : RouteAllowsCheckpoint r c) (hr : r = deterministicOnly) :
    c = deterministicPass ∨ c = deterministicFail := by
  subst hr; cases c <;> simp_all [RouteAllowsCheckpoint]

/-! ### B.15: No spurious compatible triples -/

-- Every compatible triple is in the declared tables (exhaustive characterization)
theorem compatible_triples_exhaustive (r : ResolutionRoute) (c : CheckpointClass) (a : FinalAdjudication) :
    RouteClassAdjudicationCompatible r c a ↔
      (r = deterministicOnly ∧ c = deterministicPass ∧ a = resolvedPass) ∨
      (r = deterministicOnly ∧ c = deterministicFail ∧ a = resolvedFail) ∨
      (r = oracleAssisted ∧ c = oracleNeeded ∧ a = resolvedPass) ∨
      (r = oracleAssisted ∧ c = oracleNeeded ∧ a = resolvedFail) ∨
      (r = oracleAssisted ∧ c = oracleNeeded ∧ a = escalatedHuman) ∨
      (r = humanOnly ∧ c = humanNeeded ∧ a = escalatedHuman) := by
  cases r <;> cases c <;> cases a <;>
    simp [RouteClassAdjudicationCompatible, RouteAllowsCheckpoint, LegalTransition,
          AdjudicationAllowedByRoute]

/-! ## Section C — Strengthening Lemmas -/

-- C.16: deterministicOnly triple characterization
theorem compatible_deterministicOnly_iff (c : CheckpointClass) (a : FinalAdjudication) :
    RouteClassAdjudicationCompatible deterministicOnly c a ↔
      (c = deterministicPass ∧ a = resolvedPass) ∨
      (c = deterministicFail ∧ a = resolvedFail) := by
  cases c <;> cases a <;>
    simp [RouteClassAdjudicationCompatible, RouteAllowsCheckpoint, LegalTransition,
          AdjudicationAllowedByRoute]

-- C.17: humanOnly triple characterization
theorem compatible_humanOnly_iff (c : CheckpointClass) (a : FinalAdjudication) :
    RouteClassAdjudicationCompatible humanOnly c a ↔
      (c = humanNeeded ∧ a = escalatedHuman) := by
  cases c <;> cases a <;>
    simp [RouteClassAdjudicationCompatible, RouteAllowsCheckpoint, LegalTransition,
          AdjudicationAllowedByRoute]

-- C.18: oracleAssisted triple characterization
theorem compatible_oracleAssisted_iff (c : CheckpointClass) (a : FinalAdjudication) :
    RouteClassAdjudicationCompatible oracleAssisted c a ↔
      (c = oracleNeeded ∧ (a = resolvedPass ∨ a = resolvedFail ∨ a = escalatedHuman)) := by
  cases c <;> cases a <;>
    simp [RouteClassAdjudicationCompatible, RouteAllowsCheckpoint, LegalTransition,
          AdjudicationAllowedByRoute]
```

---

## Section D — Downstream Mirroring Note

This second kernel gives you a machine-verified, exhaustive truth table for
route/checkpoint/oracle/adjudication compatibility. It can be mirrored into
runtime validators as follows:

**Python validator logic.**
Each `def …Prop` table translates directly into a Python dict or set of allowed
`(route, checkpoint)` / `(route, adjudication)` pairs. The `compatible_triples_exhaustive`
theorem enumerates exactly the six legal `(route, checkpoint, adjudication)` triples;
a Python validator only needs to check membership in that set.

**JSON enum / transition validation.**
The `ResolutionRoute`, `CheckpointClass`, `OracleEmission`, and `FinalAdjudication`
inductives map 1-to-1 to JSON string enums. The compatibility tables become JSON
schema `oneOf` / `enum` constraints or a static allowlist that a JSON-Schema validator
or runtime guard can enforce.

**Deterministic hybrid checkpoint checks in the ASIR module.**
At each checkpoint in the ASIR pipeline, the runtime receives a `(route, checkpoint, adjudication)`
triple. The guard calls the equivalent of `RouteClassAdjudicationCompatible` — a
constant-time lookup against the six-row allowlist. Any triple not in the list is
rejected before further processing. Because the Lean kernel proves this list is
both sound (every listed triple satisfies all three sub-relations) and complete
(no unlisted triple can satisfy them), the runtime guard is provably correct
against the formal spec.
