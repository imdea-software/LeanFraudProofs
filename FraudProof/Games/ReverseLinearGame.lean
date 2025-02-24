import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.GenericTree -- Generic Game trees
import FraudProof.Games.ElemInTree -- Linear basic game definition

import FraudProof.DataStructures.Sequence

----------------------------------------
-- * Rev Linear Game Transformation
-- When we are proving |[a -> b]|, we can begin from |b| and reach |a| or begin
-- from |a| and reach |b|.
-- Here we prove their are equivalent games.
--
-- There is one difference in the mid_challenges.
-- + Backward reveling:
--  [a->b]!n.succ <=>
--    1. R->(c,side,d)
--    2. Choose: [a->c]!n or op_side side c d = b
-- + Forward reveling:
--  [a->b]!n.succ <=>
--    1. R->(c,side,d)
--    2. Choose: [c->b]!n or op_side side a d = c
-- Steps 2 are different

def backward_to_forward_proposer
    {ℍ : Type}{mag : HashMagma ℍ}
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (back_proposer : Sequence n (Option (PMoves ℍ)))
    : Sequence n (Option (PMoves ℍ))
    :=  Sequence.zip_with (
    fun skl opt_mov =>
      (fun mov =>
        match skl,  mov with
           | .Left , ⟨ l , r ⟩
             => ⟨ mag.comb l r , r ⟩
           | .Right , ⟨ l , r ⟩
             => ⟨ mag.comb r l , l ⟩
      ) <$> opt_mov
      ) da.data back_proposer

theorem equiv_lin_forward_backward {ℍ : Type}[BEq ℍ][mag : HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (Option (PMoves ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : elem_in_tree_backward da proposer chooser
    = elem_in_tree_forward  da
      (@backward_to_forward_proposer _ mag _ da proposer) chooser
    := by sorry
