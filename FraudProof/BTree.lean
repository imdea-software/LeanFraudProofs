-- Importing Values
import FraudProof.Value

/-! # Binary Tree -/

-- BTree Basic Definition
inductive BTree (α : Type ): Type
| leaf (v : α)
| node ( bL bR : BTree α )

deriving instance BEq for BTree
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
    theorem notValue [BEq α](v : α) (bt : BTree α) : valueIn v bt = false -> valueInProof v bt = none
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
