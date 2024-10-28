import FraudProof.Games.GameDef -- Players, Winner
-- import FraudProof.Players

import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

-- Function generating a /good proposer/, i.e. a proposer winning the game.
def GoodProposer {α ℍ : Type} {n m : Nat}
    (data : STree α ℍ n)
    (mLTn : m < n)
    (skl : ISkeleton m)
    --
    :  ProposerMoves ℍ
    := match n with
    | 0 => match data with
           | .nodeL _ _ bl br => ⟨ bl.getI , br.getI ⟩
           | .nodeR _ _ bl br => ⟨ bl.getI , br.getI ⟩
    | .succ pn =>
      let fst := skl ⟨ 0 , by omega ⟩
      match fst with
      | .inl _ => _
      | .inr _ => _
