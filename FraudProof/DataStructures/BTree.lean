-- Induction proofs
import Mathlib.Data.Nat.Defs

import Mathlib.Control.Bifunctor

/-! # Binary Tree -/

----------------------------------------
-- * Definition
inductive ABTree (α β : Type) : Type
 | leaf (v : α)
 | node (i : β) ( bL bR : ABTree α β )
----------------------------------------

----------------------------------------
-- * Similar (iso) as Mathlib.Data.Tree.Basic :shrug:
----------------------------------------

----------------------------------------
-- * Info getters
--
@[simp]
def ABTree.sizeI {α β : Type} (sa : α -> Nat)(sb : β -> Nat) : ABTree α β -> Nat
  | .leaf a => sa a
  | .node b bl br => sb b + bl.sizeI sa sb + br.sizeI sa sb

@[simp]
def ABTree.size {α β : Type} : ABTree α β -> Nat := ABTree.sizeI (fun _ => 1) (fun _ => 1)
  --
@[simp]
def ABTree.height {α β : Type} : ABTree α β -> Nat := ABTree.sizeI (fun _ => 0) (fun _ => 1)

-- Projector
def ABTree.getI' {α β γ : Type}(p : α -> γ)(q : β -> γ) : ABTree α β -> γ
 | .leaf v => p v
 | .node i _ _ => q i

@[simp]
def ABTree.hget {α : Type} : ABTree α α -> α
 := ABTree.getI' id id

def ABTree.getI {α β : Type} : ABTree (α × β) β -> β
 := ABTree.getI' (fun p => p.2) id

----------------------------------------

----------------------------------------
-- * Tree Operations
@[simp]
def ABTree.fold {α β γ: Type} (l : α -> γ) (n : β -> γ -> γ -> γ) : ABTree α β -> γ
  | .leaf v => l v
  | .node b tl tr => n b (tl.fold l n) (tr.fold l n)

lemma ABTree.fold_node {α β γ: Type}{l : α -> γ} {n : β -> γ -> γ -> γ}
  (bl : ABTree α β)
  (br : ABTree α β)
  (b : β)
  : ABTree.fold  l n (.node b bl br) = n b (bl.fold l n) (br.fold l n)
  := by simp

@[simp]
def ABTree.map {α₁ α₂ β₁ β₂ : Type }
   (f : α₁ -> α₂) (g : β₁ -> β₂)
   : ABTree α₁ β₁ -> ABTree α₂ β₂
   | .leaf v => .leaf $ f v
   | .node i bl br => .node (g i) (bl.map f g) (br.map f g)

theorem abtree_map_compose {α₁ α₂ α₃ β₁ β₂ β₃ : Type }
  (f : α₁ -> α₂) (f' : α₂ -> α₃)
  (g : β₁ -> β₂) (g' : β₂ -> β₃)
  (t : ABTree α₁ β₁)
  : ABTree.map f' g' (ABTree.map f g t) = ABTree.map (f' ∘ f) (g' ∘ g) t
  := by
  induction t with
  | leaf v =>  simp
  | node b bl br HL HR => simp; apply And.intro; all_goals { assumption }

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
-- TODO LawfulBifunctor

----------------------------------------

@[simp]
def abtree_zip_with {α β δ ε ρ η : Type}
  (f : α -> δ -> ρ)
  (g : β -> ε -> η)
  (l : ABTree α β)(r : ABTree δ ε) : Option (ABTree ρ η)
  := match l , r with
    | .leaf a , .leaf d => .some $ .leaf $ f a d
    | .node b bl br , .node e el er =>
      .node (g b e) <$> (abtree_zip_with f g bl el) <*> (abtree_zip_with f g br er)
    | _ , _ => .none

def ABTree.forget {α β : Type} : ABTree α β -> ABTree Unit Unit
 := ABTree.map (fun _ => ()) (fun _ => ())

----------------------------------------

----------------------------------------
-- * BTree (data only in leaves)
abbrev BTree (α : Type) := ABTree α Unit

@[simp]
def BTree.leaf {α : Type} : α -> BTree α := .leaf
@[simp]
def BTree.node {α : Type} : BTree α -> BTree α -> BTree α := .node ()

@[simp]
def BTree.map {α β : Type}(f : α -> β) : BTree α -> BTree β
  := ABTree.map f id

@[simp]
def BTree.fold {α γ: Type}(l : α -> γ)(n : γ -> γ -> γ) : BTree α -> γ
  := ABTree.fold l (fun _ => n)

def BTree.toList {α : Type} : BTree α -> List α
  := BTree.fold List.singleton List.append

instance : Functor BTree where
 map := BTree.map

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
                    | some a => .node a p :: (pairUp' none ps)

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

section BTree
    abbrev TreePath (α : Type ):= List (Sum (BTree α) (BTree α))
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
        | .leaf vb =>
            if v == vb
            then some []
            else none
        | .node l r =>
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
            | node _ l r IHL IHR => {
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
            | node _ l r IHL IHR => {
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
                | node _ lt rt IHL IHR => {
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
        | .leaf _ => 1
        | .node l r => (length l) + (length r)

    -- List View
    def toList (bt : BTree α) : List α :=
    match bt with
      | .leaf v => [v]
      | .node l r => (toList l) ++ (toList r)

    axiom lengthConcat ( l r : List α ) : List.length (l ++ r) = List.length l + List.length r

    theorem sameLength (bt : BTree α) : length bt = List.length (toList bt)
    := by {
    induction bt with
      | leaf v => rw [ length , toList , List.length ]; simp
      | node _ l r Hl Hr => rw [ length, toList , Hl , Hr, lengthConcat ]
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

----------------------------------------
-- * Tree Skeletons
----------------------------------------
abbrev ABTreeSkeleton := ABTree Unit Unit

@[simp]
def complete_tree_skeleton ( lvl : Nat ) : ABTreeSkeleton
  := match lvl with
     | .zero => .leaf ()
     | .succ plvl =>
      have sbtree := complete_tree_skeleton plvl; .node () sbtree sbtree
