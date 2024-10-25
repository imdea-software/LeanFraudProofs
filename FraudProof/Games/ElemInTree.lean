import FraudProof.DAssertions
import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Players

-- DA: element is in Tree
structure ElemInMTree (α ℍ : Type) where
  elem : α
  path : Skeleton
  mtree : ℍ
  -- Prop: foldl hash_Path (hash elem) path = mtree

def arbElem {α ℍ : Type}
    (pos : Skeleton)
    [BEq ℍ]
    [o : Hash α ℍ][m : HashMagma ℍ]
    --
    (da : ElemInMTree α ℍ)
    --
    (proposer : Skeleton -> ProposerMoves ℍ)
    (chooser : Skeleton -> ProposerMoves ℍ -> ChooserSmp)
    : Winner
    := match _HC : da.path with
       | .nil => condWProp $ o.mhash da.elem == da.mtree
       | .cons sibside rest =>
         let proposed := proposer pos
         match chooser pos proposed with
         | .Now => condWProp $ hProposed proposed == da.mtree
         | .Continue _ =>
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
    (proposer : Skeleton -> ProposerMoves ℍ)
    (chooser : Skeleton -> ProposerMoves ℍ -> ChooserSmp)
    : Winner
    := arbElem .nil da proposer chooser
