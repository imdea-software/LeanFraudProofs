import FraudProof.Games.GameDef -- Players, Winner

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

def Fhead {α : Type} {n : Nat}  : (Fin n.succ -> α) -> α
 := fun seq => seq ⟨ 0 , by simp ⟩

def elemInHGame {α ℍ : Type}
    [BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeN n α ℍ)
    (proposer : Fin n -> Option (PMoves ℍ))
    (chooser : Fin n -> ℍ × ℍ -> Option ChooserSmp)
    : Winner
    := match n with
       | 0 =>
         condWProp $ o.mhash da.data.1 == da.mtree
       | .succ _pn =>
         match Fhead proposer with
         | .none => Player.Chooser
         | .some (.Next proposed) =>
           match Fhead chooser proposed with
           | .none => Player.Proposer
           | .some .Now => condWProp $ m.comb proposed.1 proposed.2 == da.mtree
           | .some (.Continue _) =>
             have nextHash := match Fhead da.data.2 with
                    | .inl _ => proposed.1
                    | .inr _ => proposed.2
             elemInHGame ⟨⟨ da.data.1, Fin.tail da.data.2⟩ , nextHash ⟩
                           (Fin.tail proposer)
                           (Fin.tail chooser)
