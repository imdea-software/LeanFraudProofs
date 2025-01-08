import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.Base.GenericTree -- Generic Game trees

import FraudProof.DataStructures.Sequence

import Mathlib.Data.Fin.Tuple.Basic

-- DA: element is in Tree
structure ElemInMTree (α ℍ : Type) where
  elem : α
  path : Skeleton
  mtree : ℍ
  -- Prop: foldl hash_Path (hash elem) path = mtree

-- Here we do not need to know the whole tree.
-- maybe we need to define some notion of DA promotion.
-- Whatever game we define over Skeletons we can play over trees?

def arbElem {α ℍ : Type}
    (pos : Skeleton)
    [BEq ℍ]
    [o : Hash α ℍ][m : HashMagma ℍ]
    --
    (da : ElemInMTree α ℍ)
    --
    (proposer : Skeleton -> Option (PMoves ℍ))
    (chooser : Skeleton -> PMoves ℍ -> Option ChooserSmp)
    : Winner
    := match _HC : da.path with
       | .nil => condWProp $ o.mhash da.elem == da.mtree
       | .cons sibside rest =>
         match proposer pos with
         | none => Player.Chooser
         | some proposed =>
          match chooser pos proposed with
            | none => Player.Proposer
            | some .Now => condWProp $ hProposed proposed == da.mtree
            | some (.Continue _) =>
                let nextHash := match sibside with
                                | .inl _ => proposed.left
                                | .inr _ => proposed.left
                arbElem (pos ++ [sibside]) ⟨ da.elem , rest, nextHash⟩
                        proposer chooser
    termination_by da.path
    decreasing_by {simp_wf; rw [_HC]; simp}

def arbElemInit {α ℍ : Type} [BEq ℍ] [Hash α ℍ][HashMagma ℍ]
    -- DA
    (da : ElemInMTree α ℍ)
    -- Players
    (proposer : Skeleton -> Option (PMoves ℍ))
    (chooser : Skeleton -> PMoves ℍ -> Option ChooserSmp)
    : Winner
    := arbElem .nil da proposer chooser

-- There is a path of length |n| from the root |mtree| to |elem|
structure ElemInTreeN (n : Nat)(α ℍ : Type) where
  data : α × ISkeleton n
  mtree : ℍ
  -- Let |bt : BTree α| be the implicit data, such that |hash bt = mtree|.
  -- This da says |bt ! data.2| leads to |data.1|

theorem ElemInTreeN0 {α ℍ : Type} (da : ElemInTreeN 0 α ℍ)
 : da.data.2 = nilSeq
 := by have ⟨ ⟨ a , sk ⟩ , mtree ⟩ := da
       simp
       apply funext
       intro empty
       simp [nilSeq]
       have ⟨ n , e ⟩ := empty
       simp at e

structure ElemInTreeH (n : Nat)(ℍ : Type) where
  data : ℍ × ISkeleton n
  mtree : ℍ
  -- Same as above but only using hashes
  -- |dt ! data.2| leads to | data.1| where |data.1| is the hash of the element
  -- in a tree [see the above DA].

def SingleLastStep {α ℍ : Type}[BEq ℍ][h : Hash α ℍ] (data : ElemInTreeN 0 α ℍ) : Winner
  := condWProp $ h.mhash (data.data.1) == data.mtree

def SingleMidStep {ℍ : Type}[BEq ℍ][m : HashMagma ℍ ](data : ℍ × ℍ × ℍ) : Winner
  := condWProp $ m.comb data.2.1 data.2.2 == data.1

def elemInHGame {α ℍ : Type}
    [BEq ℍ][Hash α ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeN n α ℍ)
    (proposer : Sequence n (Option (PMoves ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : Winner
    := match n with
       | 0 => SingleLastStep da
       | .succ _pn =>
         match headSeq proposer with
         | .none => Player.Chooser -- Proposer forfeits the game
         | .some (.Next proposed) =>
           match headSeq chooser ⟨ da.mtree , proposed ⟩ with
           | .none => Player.Proposer -- Chooser forfeits the game
           | .some .Now => SingleMidStep ⟨ da.mtree , proposed ⟩
           | .some (.Continue _) =>
             have nextHash := match headSeq da.data.2 with
                    | .inl _ => proposed.1
                    | .inr _ => proposed.2
             elemInHGame
               -- Next step DA
               ⟨⟨ da.data.1, tailSeq da.data.2⟩ , nextHash ⟩
               -- Next step players
               (tailSeq proposer)
               (tailSeq chooser)

-- Here we can have some troubles. We do not know if we really are talking about
-- the same element.
def SingleLastStepH {ℍ : Type}[BEq ℍ] (data : ElemInTreeH 0 ℍ) : Winner
  := condWProp $ data.data.1 == data.mtree

def elemInHGameH {ℍ : Type}
    [BEq ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (Option (PMoves ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : Winner
    := match n with
       | 0 => SingleLastStepH da
       | .succ _pn =>
         match headSeq proposer with
         | .none => Player.Chooser -- Proposer forfeits the game
         | .some (.Next proposed) =>
           match headSeq chooser ⟨ da.mtree , proposed ⟩ with
           | .none => Player.Proposer -- Chooser forfeits the game
           | .some .Now => SingleMidStep ⟨ da.mtree , proposed ⟩
           | .some (.Continue _) =>
             have nextHash := match headSeq da.data.2 with
                    | .inl _ => proposed.1
                    | .inr _ => proposed.2
             elemInHGameH
               -- Next step DA
               ⟨⟨ da.data.1, tailSeq da.data.2⟩ , nextHash ⟩
               -- Next step players
               (tailSeq proposer)
               (tailSeq chooser)

-- Building a Tree out of skelentons.
-- This function keeps size.
-- ABTree.size is height
def skeleton_to_tree {n : Nat} (sk : ISkeleton n) : ABTree Unit Unit
 := match n with
   | .zero => .leaf ()
   | .succ _pn => match headSeq sk with
                 | .inl _ =>
                        .node () (skeleton_to_tree (Fin.tail sk)) (.leaf ())
                 | .inr _ =>
                        .node ()  (.leaf ()) (skeleton_to_tree (Fin.tail sk))

def skl_to_maybe_elem {α : Type} {n : Nat}
  (a : α) (sk : ISkeleton n) : ABTree (Option α) Unit
    := match n with
    | .zero => .leaf a
    | .succ _pn => match headSeq sk with
                    | .inl _ =>
                            .node () (skl_to_maybe_elem a (Fin.tail sk)) (.leaf none)
                    | .inr _ =>
                            .node () (.leaf none) (skl_to_maybe_elem a (Fin.tail sk))

def build_proposer {ℍ : Type}{n : Nat}
  (data : ℍ × ISkeleton n) (rev : Sequence n (Option (PMoves ℍ)))
  : ABTree (Option ℍ) (Option (Unit × ℍ × ℍ))
  := match n with
  | .zero => .leaf <| .some data.1
  | .succ _pn => let rest_tree := build_proposer ⟨ data.1 , Fin.tail data.2⟩ (Fin.tail rev)
     match headSeq rev with
       | .none => .node .none rest_tree (.leaf .none)
       | .some (.Next ⟨ hl , hr⟩)=>
         match headSeq data.2 with
         | .inl _ =>
           .node (.some ⟨ (), hl, hr ⟩)
                 rest_tree
                 (.leaf (.some hr))
         | .inr _ =>
           .node (.some ⟨ (), hl, hr ⟩)
                 (.leaf (.some hl))
                 rest_tree

def build_chooser {ℍ : Type}{n : Nat}
  (data : ℍ × ISkeleton n)
  (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
  : ABTree Unit (ℍ × Unit × ℍ × ℍ -> Option ChooserMoves)
  := match n with
    | .zero => .leaf ()
    | .succ _pn =>
      let side_choose (s : Chooser.Side) (arg : ℍ × Unit × ℍ × ℍ) : Option ChooserMoves :=
          have ⟨ ht , _ , hl , hr ⟩ := arg
          (headSeq chooser ⟨ ht, hl , hr ⟩).map
            (fun ch => match ch with
                       | .Now => .Now
                       | .Continue _ => .Continue s)
      match headSeq data.2 with
      | .inl _ =>
        .node
          (side_choose .Left)
          (build_chooser ⟨data.1 , Fin.tail data.2⟩ (Fin.tail chooser))
          (.leaf ())
      | .inr _ =>
        .node
          (side_choose .Right)
          (.leaf ())
          (build_chooser ⟨data.1 , Fin.tail data.2⟩ (Fin.tail chooser))

def elem_in_tree_gen_tree {ℍ : Type}
    [BEq ℍ][mag : HashMagma ℍ]
    -- DA
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    --
    (proposer : Sequence n (Option (PMoves ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    --
    : Winner
    :=
    let da_tree : CompTree (Option ℍ) Unit ℍ := {data := skl_to_maybe_elem da.data.1 da.data.2 , res := da.mtree}
    let tree_revealer : ABTree (Option ℍ) (Option (Unit × ℍ × ℍ))
      := build_proposer da.data proposer
    let tree_chooser : ABTree Unit (ℍ × Unit × ℍ × ℍ -> Option ChooserMoves)
      := build_chooser da.data chooser
    treeCompArbGame
      (fun opth _h1 h2 =>
        match opth with
        | .none => -- this case is a bit artificial
        -- chooser should challenge previous step.
          Player.Proposer
        | .some hp => condWProp <| (hp == h2)
      )
      (fun _ _ hres pl pr =>
        -- _nodeh and hres should be the same.
           condWProp <| mag.comb pl pr == hres)
      da_tree tree_revealer tree_chooser
