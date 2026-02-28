import Std
import AdeuODEU.Artifacts

namespace AdeuODEU

open Std

/-
Ground truth: _LAYER_ORDER in packages/adeu_core_ir/src/adeu_core_ir/models.py
  _LAYER_ORDER = {"O":0,"E":1,"D":2,"U":3}
-/
def layerOrder : Layer → Nat
  | .O => 0
  | .E => 1
  | .D => 2
  | .U => 3

/-
Ground truth: canonical_node_sort_key(node) in models.py
  return (_LAYER_ORDER[node.layer], node.kind, node.id)
-/
def canonicalNodeKey (n : CoreNode) : (Nat × String × String) :=
  (layerOrder (nodeLayer n), nodeKindString n, nodeId n)

/-
Ground truth: canonical_edge_sort_key(edge) in models.py
  return edge.identity == (edge.type, edge.from_ref, edge.to_ref)
-/
def canonicalEdgeKey (e : CoreEdge) : (String × String × String) :=
  (toString e.type, e.from_ref, e.to_ref)

/- A total, deterministic “≤” on keys: ka <= kb iff compare ka kb != gt. -/
def keyLeB {β : Type} [Ord β] (ka kb : β) : Bool :=
  match compare ka kb with
  | Ordering.gt => false
  | _ => true

def keyLe {β : Type} [Ord β] (ka kb : β) : Prop :=
  compare ka kb ≠ Ordering.gt

/-
Deterministic sortedness check (adjacent monotone) equivalent to:
  xs == sorted(xs, key=...)
used in AdeuCoreIR._validate_contract (models.py),
but cheaper + directly runnable in Lean.
-/
def isSortedByB {α : Type} (key : α → β) [Ord β] : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
      keyLeB (key a) (key b) && isSortedByB key (b :: rest)

def NodesSorted (nodes : List CoreNode) : Prop :=
  nodes.Chain' (fun a b => keyLe (canonicalNodeKey a) (canonicalNodeKey b))

def EdgesSorted (edges : List CoreEdge) : Prop :=
  edges.Chain' (fun a b => keyLe (canonicalEdgeKey a) (canonicalEdgeKey b))

/- Helper: finset from a literal list of strings. -/
def fs (xs : List String) : Finset String := xs.toFinset

/-
Mechanically isomorphic encoding of _EDGE_TYPING_MATRIX in:
  packages/adeu_core_ir/src/adeu_core_ir/models.py

We use the same signature strings (e.g. "E.Claim", "D.Policy", "U.Metric", ...)
that Python checks via _node_signature(node).
-/
def allowedFromSigs : EdgeType → Finset String
  | .about =>
      fs ["E.Claim", "E.Assumption", "E.Question", "E.Evidence"]
  | .defines =>
      fs ["E.Claim", "E.Evidence"]
  | .supports =>
      fs ["E.Evidence", "E.Claim"]
  | .refutes =>
      fs ["E.Evidence", "E.Claim"]
  | .depends_on =>
      fs ["E.Claim"]
  | .justifies =>
      fs ["E.Claim", "E.Evidence"]
  | .gates =>
      fs ["D.Policy"]
  | .serves_goal =>
      fs ["D.PhysicalConstraint", "D.Norm", "D.Policy", "E.Claim"]
  | .prioritizes =>
      fs ["U.Preference"]
  | .excepts =>
      fs ["D.Exception"]

def allowedToSigs : EdgeType → Finset String
  | .about =>
      fs ["O.Entity", "O.Concept", "O.RelationType"]
  | .defines =>
      fs ["O.Concept", "O.RelationType"]
  | .supports =>
      fs ["E.Claim"]
  | .refutes =>
      fs ["E.Claim"]
  | .depends_on =>
      fs ["E.Claim", "E.Assumption", "E.Question", "E.Evidence"]
  | .justifies =>
      fs ["D.Norm", "D.Policy"]
  | .gates =>
      fs ["E.Claim", "E.Assumption", "E.Question"]
  | .serves_goal =>
      fs ["U.Goal", "U.Metric"]
  | .prioritizes =>
      fs ["U.Goal", "U.Metric", "D.PhysicalConstraint", "D.Norm", "D.Policy", "D.Exception"]
  | .excepts =>
      fs ["D.PhysicalConstraint", "D.Norm", "D.Policy"]

def AllowedEdge (t : EdgeType) (fromSig toSig : String) : Prop :=
  fromSig ∈ allowedFromSigs t ∧ toSig ∈ allowedToSigs t

def allowedEdgeB (t : EdgeType) (fromSig toSig : String) : Bool :=
  (fromSig ∈ allowedFromSigs t) && (toSig ∈ allowedToSigs t)

/- Deterministic lookup (first match) — contract requires uniqueness anyway. -/
def findNode? (nodes : List CoreNode) (id : String) : Option CoreNode :=
  nodes.find? (fun n => n.id == id)  -- nodeId uniqueness enforced by contract

/-
Edge validity mirrors the inner loop of AdeuCoreIR._validate_contract (models.py):
  - from/to must resolve
  - signatures must satisfy _EDGE_TYPING_MATRIX[edge.type]
-/
def validEdgeB (nodes : List CoreNode) (e : CoreEdge) : Bool :=
  match findNode? nodes e.from_ref, findNode? nodes e.to_ref with
  | some fromN, some toN =>
      allowedEdgeB e.type (nodeSignature fromN) (nodeSignature toN)
  | _, _ => false

def validEdge (nodes : List CoreNode) (e : CoreEdge) : Prop :=
  match findNode? nodes e.from_ref, findNode? nodes e.to_ref with
  | some fromN, some toN =>
      AllowedEdge e.type (nodeSignature fromN) (nodeSignature toN)
  | _, _ => False

def allEdgesValidB (nodes : List CoreNode) : List CoreEdge → Bool
  | [] => true
  | e :: rest => validEdgeB nodes e && allEdgesValidB nodes rest

def allEdgesValid (nodes : List CoreNode) (edges : List CoreEdge) : Prop :=
  ∀ e, e ∈ edges → validEdge nodes e

/-
Contract : Prop (repo-grounded mirror of AdeuCoreIR._validate_contract).
This matches the checks in:
  packages/adeu_core_ir/src/adeu_core_ir/models.py :: AdeuCoreIR._validate_contract
-/
def Contract (ir : AdeuCoreIR) : Prop :=
  NodesSorted ir.nodes ∧
  EdgesSorted ir.edges ∧
  (ir.nodes.map nodeId).Nodup ∧
  (ir.edges.map CoreEdge.identity).Nodup ∧
  allEdgesValid ir.nodes ir.edges

/-
checkContract : Bool (deterministic, replay-friendly).
It checks the *same* conditions as Contract, but computably.
-/
def checkContract (ir : AdeuCoreIR) : Bool :=
  let nodesSortedB := isSortedByB canonicalNodeKey ir.nodes
  let edgesSortedB := isSortedByB canonicalEdgeKey ir.edges
  let nodeIdsNoDupB : Bool := decide ((ir.nodes.map nodeId).Nodup)
  let edgeIdsNoDupB : Bool := decide ((ir.edges.map CoreEdge.identity).Nodup)
  let edgesValidB := allEdgesValidB ir.nodes ir.edges
  nodesSortedB && edgesSortedB && nodeIdsNoDupB && edgeIdsNoDupB && edgesValidB

/-
Next theorem targets (don’t implement yet if you want a “no-sorry” repo):
  theorem checkContract_sound : checkContract ir = true → Contract ir := ...
  theorem checkContract_complete : Contract ir → checkContract ir = true := ...
These will be proven by structural recursion over lists + Chain' facts.
-/

end AdeuODEU