-- Importing Values
import FraudProof.DataStructures.Value

-- Induction proofs
import Mathlib.Data.Nat.Defs

import Mathlib.Control.Bifunctor

/-! # Binary Tree -/

inductive ABTree (α β : Type) : Type
 | leaf (v : α)
 | node (i : β) ( bL bR : ABTree α β )

@[simp]
def ABTree.sizeI {α β : Type} (sa : α -> Nat)(sb : β -> Nat) : ABTree α β -> Nat
  | .leaf a => sa a
  | .node b bl br => sb b + bl.sizeI sa sb + br.sizeI sa sb

@[simp]
def ABTree.size {α β : Type} : ABTree α β -> Nat := ABTree.sizeI (fun _ => 1) (fun _ => 1)
  -- | .leaf _ => 1
  -- | .node _ bl br => 1 + bl.size + br.size

abbrev ABTreeSkeleton := ABTree Unit Unit

-- @[simp]
-- def BTree (α : Type) := ABTree α Unit
-- def BTree.node {α : Type}(bl br : BTree α) : BTree α := ABTree.node () bl br
-- def BTree.leaf {α : Type}(v : α) : BTree α := ABTree.leaf v

-- abbrev BTree (α : Type) := ABTree α Unit

-- BTree Basic Definition
inductive BTree (α : Type ): Type
| leaf (v : α)
| node (bL bR : BTree α )
deriving instance BEq for BTree

def BTree.map {α β : Type}(f : α -> β) : BTree α -> BTree β
 | .leaf v => .leaf $ f v
 | .node bl br => .node (bl.map f) (br.map f)

instance : Functor BTree where
 map := BTree.map

@[simp]
def BTree.toAB {α : Type} : BTree α -> ABTree α Unit
  | .leaf v => .leaf v
  | .node bl br => .node () bl.toAB br.toAB

@[simp]
def ABTree.toB {α : Type} : ABTree α Unit -> BTree α
  | .leaf v => .leaf v
  | .node _ bl br => .node bl.toB br.toB

-- TODO iso ABTree <-> BTree


-- Projector
def ABTree.getI' {α β γ : Type}(p : α -> γ)(q : β -> γ) : ABTree α β -> γ
 | .leaf v => p v
 | .node i _ _ => q i

def ABTree.getI {α β : Type} : ABTree (α × β) β -> β
 := ABTree.getI' (fun p => p.2) id

def ABTree.map {α₁ α₂ β₁ β₂ : Type }
   (f : α₁ -> α₂) (g : β₁ -> β₂)
   : ABTree α₁ β₁ -> ABTree α₂ β₂
   | .leaf v => .leaf $ f v
   | .node i bl br => .node (g i) (bl.map f g) (br.map f g)

instance : Bifunctor ABTree where
 bimap := ABTree.map

theorem getMapLaw {α β δ γ σ : Type}
    (f : α -> δ)
    (g : β -> γ)
    (f' : δ -> σ)
    (g' : γ -> σ)
    (t : ABTree α β)
    : ABTree.getI' f' g' (ABTree.map f g t)
    = ABTree.getI' (f' ∘ f) (g' ∘ g) t
    := by cases t with
    | leaf v => simp [ABTree.getI', ABTree.map]
    | node i bl br => simp [ABTree.getI', ABTree.map]

def ABTree.forget {α β : Type} : ABTree α β -> ABTree Unit Unit
 := ABTree.map (fun _ => ()) (fun _ => ())

-- TODO LawfulBifunctor

-- Shortest path indexed trees.
inductive STree (α β : Type) : (n : Nat) -> Type where
  | leaf (v : α) (i : β) : STree α β 0
  -- Arbitrary decision of using leq here (and not on NodeR)
  | nodeL {n m : Nat} (i : β) (nLeqm : n ≤ m) ( bL : STree α β n )( bR : STree α β m ) : STree α β n.succ
  | nodeR {n m : Nat} (i : β) (mLTn : m < n) ( bL : STree α β n )( bR : STree α β m ) : STree α β m.succ

inductive MMTree (α β : Type) : (_s _l : Nat) -> Type where
  | leaf (v : α) (i : β) : MMTree α β 0 0
  | node {s1 s2 l1 l2 s l : Nat} (i : β) (sBot : min s1 s2 = s) (lTop : max l1 l2 = l) ( bL : MMTree α β s1 l1 )( bR : MMTree α β s2 l2 ) : MMTree α β s.succ l.succ

def MMTree.getI {α β : Type} {s l : Nat} : MMTree α β s l -> β
 | .leaf _ i => i
 | .node i _ _ _ _ => i

abbrev LeafITree (α : Type)(s l : Nat) := MMTree α Unit s l

-- Index by shortest path tree without information
abbrev ITree (α : Type)(n : Nat) := STree α Unit n

def STree.getI {α β : Type} {n : Nat} (t : STree α β n) : β
 := match t with
 | .leaf _ i => i
 | .nodeL i _ _ _ => i
 | .nodeR i _ _ _ => i
----------------------------------------

----------------------------------------
-- * From list to complete BTrees
-- Acc
@[simp]
def pairUp' {α : Type} (acc : Option (BTree α)) (ls : List (BTree α)) : List (BTree α)
  := match ls with
     | .nil => match acc with
              | none => []
              | some a => [a]
     | .cons p ps => match acc with
                    | none => pairUp' (some p) ps
                    | some a => BTree.node a p :: (pairUp' none ps)

theorem pairSize' {α : Type} (ls : List (BTree α))
  : forall (p : Option (BTree α)), (pairUp' p ls).length ≤ ls.length.succ
  := by induction ls with
        | nil => intro p
                 cases p with
                 | none => simp
                 | some _ => simp
        | cons p ps HI =>
           intro w
           cases w with
           | none =>
                  simp
                  have := HI (some p)
                  omega
           | some _ =>
             simp
             have := HI none
             assumption

theorem pairSizeNone {α : Type} (ls : List (BTree α))
  : (pairUp' none ls).length ≤ ls.length
  := by cases ls with
       | nil => simp
       | cons p ps => simp; apply pairSize'

@[simp]
def pairUp {α : Type} (ls : List (BTree α)) := pairUp' none ls

theorem pairSize {α : Type} (ls : List (BTree α))
  : (pairUp ls).length ≤ ls.length
  := by simp; apply pairSizeNone

def List.fromList' {α : Type}(ls : List (BTree α)) : Option (BTree α)
  := match ls with
     | [] => none
     | x :: [] => some x
     | x :: y :: rs => fromList' (pairUp (x :: y :: rs))
     termination_by ls.length
     decreasing_by
       simp_wf
       have := pairSizeNone rs
       omega

def List.fromList {α : Type}(ls : List α) : Option (BTree α)
 := (ls.map BTree.leaf).fromList'

-- Next fromListOne, but need to prove stuff.

-- Element path?
-- abbrev TreePathElem ( α : Type ):=  Sum (BTree α) (BTree α)
abbrev TreePath (α : Type ):= List (Sum (BTree α) (BTree α))

section BTree
    -- Define implicit type variable.
    --
    variable {α : Type}

    ----------------------------------------
    /-! ## Value Contention-/

    /-! ### Value Contention  Definition-/
    -- Dec value is in a Tree
    def valueIn [BEq α] (v : α) ( bt : BTree α ) : Bool :=
        match bt with
        | .leaf vb => v == vb
        | .node l r => valueIn v l ∨ valueIn v r

    -- Value is in tree and proof
    def valueInProof [BEq α](v : α) (bt : BTree α) : Option ( TreePath α ) :=
        match bt with
        | BTree.leaf vb =>
            if v == vb
            then some []
            else none
        | BTree.node l r =>
            match valueInProof v l with
                | some ps => some (ps ++ [ Sum.inr r ])
                | none => match valueInProof v r with
                        | some ps => some (ps ++ [ Sum.inl l ])
                        | none => none

    -- If value is not in tree, there is no proof.
    theorem notValue [BEq α](v : α) (bt : BTree α) :
            valueIn v bt = false -> valueInProof v bt = none
            := by {
            induction bt with
            | leaf vb => {
                    rw [ valueIn, valueInProof ]
                    intro NeqVVB
                    simp
                    assumption}
            | node l r IHL IHR => {
                    rw [ valueIn, valueInProof ]
                    simp
                    intros NotInL NotInR
                    rw [ IHL NotInL , IHR NotInR ]}}

    theorem valueInToProof [BEq α] (v : α) (bt : BTree α)
            : valueIn v bt -> exists (p : TreePath α), valueInProof v bt = some p
            := by {
            induction bt with
            | leaf vb => {
                    rw [ valueIn, valueInProof ]
                    intro EQvvb
                    rw [ EQvvb ]
                    exists []
                    }
            | node l r IHL IHR => {
                    rw [ valueIn ]
                    cases InL : valueIn v l with
                    | false => {
                            cases InR : valueIn v r with
                            | false => { simp }
                            | true => {
                                simp
                                rw [ valueInProof , (notValue v l InL) ]
                                simp
                                cases (IHR InR) with
                                | intro w h => exists w ++ [ Sum.inl l ]; rw [ h ]}}
                    | true => {
                            simp
                            rw [ valueInProof ]
                            cases (IHL InL) with
                            | intro w P => exists w ++ [ Sum.inr r ]; rw [ P ]}}}

    theorem valueInProofToValueIn [BEq α](v : α) (bt : BTree α) :
            (tpath : TreePath α) -> valueInProof v bt = some tpath
            -> valueIn v bt := by {
                induction bt with
                | leaf vb => {
                    intro path
                    rw [ valueInProof , valueIn]
                    simp
                    cases path with
                    | nil => {simp}
                    | cons p ps => { intros; assumption }
                    }
                | node lt rt IHL IHR => {
                    rw [ valueInProof ]
                    cases HVL : valueInProof v lt with
                    | none  => {
                        simp
                        cases HVR : valueInProof v rt with
                        | none => simp
                        | some ps => {
                            simp
                            rw [ valueIn ]
                            have HR : valueIn v rt := by {apply (IHR ps); assumption}
                            simp
                            right
                            assumption
                            }
                    }
                    | some ps =>
                        simp
                        rw [ valueIn ]
                        have HL : valueIn v lt := by { apply (IHL ps) ; assumption }
                        simp
                        left
                        assumption
                    }
                }

    theorem ValueInIFFPath [BEq α](v : α) (bt : BTree α)
            : valueIn v bt <-> exists (p : TreePath α), valueInProof v bt = some p
            := Iff.intro ( valueInToProof v bt ) (by { intro EI; cases EI with | intro p P => apply valueInProofToValueIn v bt p P})
    ----------------------------------------
    /-! ## Utils -/

    def length (bt : BTree α) : Nat :=
      match bt with
        | BTree.leaf _ => 1
        | BTree.node l r => (length l) + (length r)

    -- List View
    def toList (bt : BTree α) : List α :=
    match bt with
      | BTree.leaf v => [v]
      | BTree.node l r => (toList l) ++ (toList r)

    axiom lengthConcat ( l r : List α ) : List.length (l ++ r) = List.length l + List.length r

    theorem sameLength (bt : BTree α) : length bt = List.length (toList bt)
    := by {
    induction bt with
      | leaf v => rw [ length , toList , List.length ]; simp
      | node l r Hl Hr => rw [ length, toList , Hl , Hr, lengthConcat ]
    }

    -- Getting position from List View
    --
    -- def position (v : α) (bt : BTree α) : Fin (length bt)    := _

    ----------------------------------------
    ----------------------------------------
    /-! ## Tree Building from Paths -/
    -- Building Trees from paths.
    -- We can also build trees in a different way.
    def buildTreeN ( accumTree : BTree α) ( path : TreePath α) : BTree α :=
        match path with
        | [] => accumTree
        | p :: ps =>
            match p with
                | Sum.inl pl => buildTreeN ( BTree.node pl accumTree ) ps
                | Sum.inr pr => buildTreeN ( BTree.node accumTree pr ) ps

    def buildTree ( v : α ) ( path : TreePath α ) : BTree α :=
        buildTreeN ( BTree.leaf v ) path
    ----------------------------------------
end BTree
