import Std

namespace AdeuODEU

/-
Ground truth for these literal universes:
  Layer / OKind / EKind / DKind / UKind / EdgeType
comes from:
  packages/adeu_core_ir/src/adeu_core_ir/models.py
-/

inductive Layer where
  | O | E | D | U
deriving Repr, DecidableEq

def Layer.toString : Layer → String
  | .O => "O"
  | .E => "E"
  | .D => "D"
  | .U => "U"

instance : ToString Layer := ⟨Layer.toString⟩

inductive CoreSchemaVersion where
  | adeu_core_ir__0_1
deriving Repr, DecidableEq

def CoreSchemaVersion.toString : CoreSchemaVersion → String
  | .adeu_core_ir__0_1 => "adeu_core_ir@0.1"

instance : ToString CoreSchemaVersion := ⟨CoreSchemaVersion.toString⟩

/- Kind universes (mirrors OKind/EKind/DKind/UKind literals). -/
inductive OKind where
  | Entity | Concept | RelationType
deriving Repr, DecidableEq

def OKind.toString : OKind → String
  | .Entity => "Entity"
  | .Concept => "Concept"
  | .RelationType => "RelationType"

instance : ToString OKind := ⟨OKind.toString⟩

inductive EKind where
  | Claim | Assumption | Question | Evidence
deriving Repr, DecidableEq

def EKind.toString : EKind → String
  | .Claim => "Claim"
  | .Assumption => "Assumption"
  | .Question => "Question"
  | .Evidence => "Evidence"

instance : ToString EKind := ⟨EKind.toString⟩

inductive DKind where
  | PhysicalConstraint | Norm | Policy | Exception
deriving Repr, DecidableEq

def DKind.toString : DKind → String
  | .PhysicalConstraint => "PhysicalConstraint"
  | .Norm => "Norm"
  | .Policy => "Policy"
  | .Exception => "Exception"

instance : ToString DKind := ⟨DKind.toString⟩

inductive UKind where
  | Goal | Metric | Preference
deriving Repr, DecidableEq

def UKind.toString : UKind → String
  | .Goal => "Goal"
  | .Metric => "Metric"
  | .Preference => "Preference"

instance : ToString UKind := ⟨UKind.toString⟩

/-
EdgeType literal universe mirrors:
  EdgeType = Literal["about","defines","supports","refutes","depends_on",
                     "justifies","gates","serves_goal","prioritizes","excepts"]
in packages/adeu_core_ir/src/adeu_core_ir/models.py
-/
inductive EdgeType where
  | about
  | defines
  | supports
  | refutes
  | depends_on
  | justifies
  | gates
  | serves_goal
  | prioritizes
  | excepts
deriving Repr, DecidableEq

def EdgeType.toString : EdgeType → String
  | .about => "about"
  | .defines => "defines"
  | .supports => "supports"
  | .refutes => "refutes"
  | .depends_on => "depends_on"
  | .justifies => "justifies"
  | .gates => "gates"
  | .serves_goal => "serves_goal"
  | .prioritizes => "prioritizes"
  | .excepts => "excepts"

instance : ToString EdgeType := ⟨EdgeType.toString⟩

/- Minimal SourceSpan model (core_ir imports SourceSpan from adeu_ir). -/
structure SourceSpan where
  start : Nat
  end_ : Nat
  h_lt : start < end_
deriving Repr, DecidableEq

/-
Node records (field set aligned to packages/adeu_core_ir/src/adeu_core_ir/models.py).
We keep them simple + total; schema/JSON aliasing is handled in a later bridge module.
-/
structure CoreONode where
  id : String
  kind : OKind
  label : String
  aliases : List String := []
deriving Repr, DecidableEq

structure CoreENode where
  id : String
  kind : EKind
  text : String
  spans : List SourceSpan := []
  confidence : Option Float := none
  ledger_version : Option String := none  -- expects "adeu.sbr.v0_1" when present (checked elsewhere)
  S_milli : Option Int := none
  B_milli : Option Int := none
  R_milli : Option Int := none
  S : Option String := none
  B : Option String := none
  R : Option String := none
deriving Repr, DecidableEq

structure CoreDNode where
  id : String
  kind : DKind
  label : String
  constraint_kind : Option String := none
  modality : Option String := none
  condition : Option String := none
  target : Option String := none
  priority : Option Int := none
deriving Repr, DecidableEq

structure CoreUNode where
  id : String
  kind : UKind
  label : String
  weight : Option Float := none
deriving Repr, DecidableEq

inductive CoreNode where
  | o : CoreONode → CoreNode
  | e : CoreENode → CoreNode
  | d : CoreDNode → CoreNode
  | u : CoreUNode → CoreNode
deriving Repr, DecidableEq

def nodeId : CoreNode → String
  | .o n => n.id
  | .e n => n.id
  | .d n => n.id
  | .u n => n.id

def nodeLayer : CoreNode → Layer
  | .o _ => .O
  | .e _ => .E
  | .d _ => .D
  | .u _ => .U

def nodeKindString : CoreNode → String
  | .o n => toString n.kind
  | .e n => toString n.kind
  | .d n => toString n.kind
  | .u n => toString n.kind

/-
Mechanically matches Python _node_signature(node) = f"{node.layer}.{node.kind}"
in packages/adeu_core_ir/src/adeu_core_ir/models.py
-/
def nodeSignature : CoreNode → String
  | n => s!"{toString (nodeLayer n)}.{nodeKindString n}"

structure CoreEdge where
  type : EdgeType
  from_ref : String
  to_ref : String
deriving Repr, DecidableEq

def CoreEdge.identity (e : CoreEdge) : (EdgeType × String × String) :=
  (e.type, e.from_ref, e.to_ref)

/- Full artifact wrapper aligns to AdeuCoreIR in models.py. -/
structure AdeuCoreIR where
  schema : CoreSchemaVersion := .adeu_core_ir__0_1
  source_text_hash : String
  source_text : Option String := none
  metadata : Option Std.Json := none
  nodes : List CoreNode := []
  edges : List CoreEdge := []
deriving Repr, DecidableEq

end AdeuODEU