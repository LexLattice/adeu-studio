namespace AdeuCore

inductive Pred where
  | defined : String → Pred
  | refersToDoc : String → Pred
  | not : Pred → Pred
  | and : Pred → Pred → Pred
  | or : Pred → Pred → Pred
deriving Repr, DecidableEq

structure EvalCtx where
  defs : String → Bool
  docs : String → Bool

def evalPred (ctx : EvalCtx) : Pred → Bool
  | .defined termId => ctx.defs termId
  | .refersToDoc docRef => ctx.docs docRef
  | .not pred => !(evalPred ctx pred)
  | .and left right => (evalPred ctx left) && (evalPred ctx right)
  | .or left right => (evalPred ctx left) || (evalPred ctx right)

def evaluatable (_ctx : EvalCtx) (_pred : Pred) : Prop := True

def exceptionDefeatsNorm (ctx : EvalCtx) (pred : Pred) : Prop :=
  evaluatable ctx pred ∧ evalPred ctx pred = true

def conflictCandidate (left right : Prop) : Prop := left ∧ right

def conflict (left right : Prop) : Prop := left ∧ right

end AdeuCore
