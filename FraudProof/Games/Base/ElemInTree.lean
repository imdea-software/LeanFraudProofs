import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.Base.GenericTree -- Generic Game trees

import FraudProof.DataStructures.Sequence

import Mathlib.Data.Fin.Tuple.Basic

----------------------------------------
-- * Element in Tree basic game definitions Linear game and simple games playing
-- with the idea of needing to have the element in question or not. If we do not
-- have the element, we play games only with hashes.

-- DA: element is in Tree
structure ElemInMTree (α ℍ : Type) where
  elem : α
  path : Skeleton
  mtree : ℍ
  -- Prop: foldl hash_Path (hash elem) path = mtree

-- Here we do not need to know the whole tree.
-- maybe we need to define some notion of DA promotion.
-- Whatever game we define over Skeletons we can play over trees?

def leaf_condition {α ℍ : Type}[BEq ℍ][o : Hash α ℍ]
    (a : α)(h : ℍ) : Winner
    := condWProp $ o.mhash a == h

def mid_condition {ℍ : Type}[BEq ℍ][mag : HashMagma ℍ]
    ( p :  PMoves ℍ ) (h : ℍ) : Winner
    := match p with
      | .Next ⟨hl, hr⟩ => condWProp $ mag.comb hl hr == h

-- Element in Tree arbitration game! Intermediate steps
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
       | .nil => leaf_condition da.elem da.mtree
       | .cons sibside rest =>
         match proposer pos with
         | none => Player.Chooser
         | some proposed =>
          match chooser pos proposed with
            | none => Player.Proposer
            | some .Now => mid_condition proposed da.mtree
            | some (.Continue _) =>
                let nextHash := match sibside with
                                | .inl _ => proposed.left
                                | .inr _ => proposed.left
                arbElem (pos ++ [sibside]) ⟨ da.elem , rest, nextHash⟩
                        proposer chooser
    termination_by da.path
    decreasing_by {simp_wf; rw [_HC]; simp}

-- Element in Tree arbitration game!
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
           | .some .Now =>
             SingleMidStep  ⟨ da.mtree , proposed ⟩
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

structure ElemInTreeH (n : Nat)(ℍ : Type) where
  data : ISkeleton n -- This is the 'skeleton proof'
  mtree : ℍ × ℍ
  -- Same as above but only using hashes
  -- |dt ! data| leads to | mtree.2.2 | where |mtree.2.1| is the hash of the element
  -- in a tree [see the above DA].

-- Here we can have some troubles. We do not know if we really are talking about
-- the same element.
-- If path is of length 0, then elements should be the same. Although, hashes
-- are the same, elements maybe not be.
def SingleLastStepH {ℍ : Type}[BEq ℍ] (data : ElemInTreeH 0 ℍ) : Winner
  := condWProp $ data.mtree.1 == data.mtree.2

def elem_in_tree_backward {ℍ : Type}
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
           match headSeq chooser ⟨ da.mtree.2 , proposed ⟩ with
           | .none => Player.Proposer -- Chooser forfeits the game
           | .some .Now => SingleMidStep  ⟨ da.mtree.2 , proposed ⟩
           | .some (.Continue _) =>
             have nextHash := match headSeq da.data with
                    | .inl _ => proposed.1
                    | .inr _ => proposed.2
             elem_in_tree_backward
               -- Next step DA
               { data := tailSeq da.data, mtree := ⟨ da.mtree.1 , nextHash⟩  }
               -- Next step players
               (tailSeq proposer)
               (tailSeq chooser)

@[simp]
def forward_mid_step_condition {ℍ : Type}[BEq ℍ][m : HashMagma ℍ ]
  (side : SkElem) (data : ℍ × ℍ) (res : ℍ) : Winner
  := condWProp $ op_side side data.1 data.2 == res

-- Reverse game -- It is not (*JUST*) the reverse game.
-- Proposer proposes different hashes that the previos linear game.
--
def elem_in_tree_forward {ℍ : Type}[BEq ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (Option (PMoves ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : Winner
    := match n with
      | 0 => SingleLastStepH da
      | .succ _pn =>
        match lastSeq proposer with
        | .none => Player.Chooser
        | .some (.Next proposed) =>
            match lastSeq chooser ⟨ da.mtree.1, proposed ⟩ with
            | .none  => Player.Proposer
            | .some .Now =>
              forward_mid_step_condition
                (lastSeq da.data) ⟨ da.mtree.1 , proposed.2⟩ proposed.1
            | .some (.Continue _) =>
              elem_in_tree_forward
                {data := Fin.init da.data, mtree := ⟨ proposed.1 , da.mtree.2⟩}
                (Fin.init proposer)
                (Fin.init chooser)
