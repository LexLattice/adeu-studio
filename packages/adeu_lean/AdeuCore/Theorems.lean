import AdeuCore.Semantics

namespace AdeuCore

theorem pred_closed_world_missing_false
    (defs : String → Bool)
    (termId : String)
    (hMissing : defs termId = false) :
    evalPred { defs := defs, docs := fun _ => false } (.defined termId) = false := by
  simpa [evalPred] using hMissing

theorem exception_gating_false_not_defeat
    (ctx : EvalCtx)
    (pred : Pred)
    (hEval : evaluatable ctx pred)
    (hFalse : evalPred ctx pred = false) :
    ¬ exceptionDefeatsNorm ctx pred := by
  intro hDefeats
  have hImpossible : false = true := by
    simpa [exceptionDefeatsNorm, hEval, hFalse] using hDefeats.2
  cases hImpossible

theorem conflict_soundness
    (left right : Prop) :
    conflictCandidate left right → conflict left right := by
  intro hCandidate
  exact hCandidate

end AdeuCore
