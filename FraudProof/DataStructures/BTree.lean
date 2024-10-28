-- Importing Values
import FraudProof.DataStructures.Value

-- Induction proofs
import Mathlib.Data.Nat.Defs

/-! # Binary Tree -/

-- BTree Basic Definition
inductive BTree (α : Type ): Type
| leaf (v : α)
| node ( bL bR : BTree α )
deriving instance BEq for BTree

-- Shortest path indexed trees
inductive STree (α β : Type) : (n : Nat) -> Type where
  | leaf (v : α) (i : β) : STree α β 0
  | nodeL {n m : Nat} (i : β) (nLTm : n < m) ( bL : STree α β n )( bR : STree α β m ) : STree α β n.succ
  | nodeR {n m : Nat} (i : β) (mLTn : m < n) ( bL : STree α β n )( bR : STree α β m ) : STree α β m.succ

def STree.getI {α β : Type} {n : Nat} (t : STree α β n) : β
 := match t with
 | .leaf _ i => i
 | .nodeL i _ _ _ => i
 | .nodeR i _ _ _ => i

-- BTree with data in nodes. Useful to store markle tree intermedeari
-- information.
inductive ITree (α β : Type) : Type
 | leaf (v : α)
 | node (n : β) (l r : ITree α β)


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

abbrev TreePathElem ( α : Type ):=  Sum (BTree α) (BTree α)
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
        | BTree.leaf vb => v == vb
        | BTree.node l r => valueIn v l ∨ valueIn v r

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
