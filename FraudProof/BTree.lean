-- Importing Values
import FraudProof.Value

-- BTree Basic Definition
inductive BTree : Type
| leaf (v : Value)
| node ( bL bR : BTree )

deriving instance BEq for BTree

def valueIn (v : Value) ( bt : BTree ) : Bool :=
    match bt with
    | BTree.leaf vb => v == vb
    | BTree.node l r => valueIn v l ∨ valueIn v r

abbrev TreePath := List (Sum BTree BTree)
def valueInProof (v : Value) (bt : BTree) : Option TreePath :=
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

theorem notValue (v : Value) (bt : BTree) : valueIn v bt = false -> valueInProof v bt = none
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

theorem valueInToProof (v : Value) (bt : BTree)
        : valueIn v bt -> exists (p : TreePath), valueInProof v bt = some p
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

theorem valueInProofToValueIn (v : Value) (bt : BTree) :
        (tpath : TreePath) -> valueInProof v bt = some tpath
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

theorem ValueInIFFPath (v : Value) (bt : BTree)
        : valueIn v bt <-> exists (p : TreePath), valueInProof v bt = some p
        := Iff.intro ( valueInToProof v bt ) (by { intro EI; cases EI with | intro p P => apply valueInProofToValueIn v bt p P})


-- We can also build trees in a different way.
def buildTreeN ( accumTree : BTree ) ( path : List (Sum BTree BTree)) : BTree :=
    match path with
    | [] => accumTree
    | p :: ps =>
        match p with
            | Sum.inl pl => buildTreeN ( BTree.node pl accumTree ) ps
            | Sum.inr pr => buildTreeN ( BTree.node accumTree pr ) ps

def buildTree ( v : Value ) ( path : List (Sum BTree BTree)) : BTree :=
    buildTreeN ( BTree.leaf v ) path
