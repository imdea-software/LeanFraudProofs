import FraudProof.Games.GameDef -- Players, Winner
-- import FraudProof.Players

import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

import Mathlib.Data.Fin.Tuple.Basic -- Fin.tail

-- What if I modeled no posible moves as game ending.
-- Adding a checking move as move. | LastElemChk |.
--
-- This is a /semi/ good proposer. Skeletons could be of /wrong size/.
def SemiGoodProposer {α ℍ : Type}
   (data : ABTree α ℍ)
   (skl : Skeleton)
   : Option (ProposerMoves ℍ)
   := match skl with
   | .nil => match data with
             | .leaf _ _ => none
             | .node _ bl br => some ⟨ bl.getI , br.getI ⟩
   | .cons s sk => match s , data with
                   | .inl _ , .node _ l _ => SemiGoodProposer l sk
                   | .inr _ , .node _ _ r => SemiGoodProposer r sk
                   | _ , _ => none

-- Function generating a /good proposer/ from a tree, i.e. a proposer winning
-- the game.
def GoodProposer {α ℍ : Type} {m n : Nat}
    ( _mLTn : m < n )
    (data : STree α ℍ n)
    (skl : ISkeleton m)
    --
    :  ProposerMoves ℍ
    := match _Hm : m with
    | 0 => match data with
           | .nodeL _ _ bl br => ⟨ bl.getI , br.getI ⟩
           | .nodeR _ _ bl br => ⟨ bl.getI , br.getI ⟩
    | .succ pm =>
      let fst := skl ⟨ 0 , by simp ⟩
      match fst with
      | .inl _ => match data with
                  | .nodeL _ _ bl _ => GoodProposer (by omega) bl $ Fin.tail skl
                  | .nodeR _ _ bl _ => GoodProposer (by omega) bl $ Fin.tail skl
      | .inr _ => match data with
                  | .nodeL _ _ _ br => GoodProposer (by omega) br $ Fin.tail skl
                  | .nodeR _ _ _ br => GoodProposer (by omega) br $ Fin.tail skl
