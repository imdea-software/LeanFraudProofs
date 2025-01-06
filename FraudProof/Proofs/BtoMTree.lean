import FraudProof.Games.Base.FromBtoMTree
import FraudProof.Players.FromBToMTree

import FraudProof.DataStructures.Hash
import FraudProof.Extras.BToMTree -- medTrees, computing hashes and stuff

def isInTree {α : Type}(t : BTree α)(sk : Skeleton) : Bool
  := match sk , t with
     | .nil , _ => true -- path shorter than tree
     | .cons (.inl _) sk , .node bl _ => isInTree bl sk
     | .cons (.inr _) sk , .node _ br => isInTree br sk
     | .cons _ _ , .leaf _ => false -- path longer than tree


theorem defenseW {α ℍ : Type}[BEq ℍ][LawfulBEq ℍ] [Hash α ℍ][ε : HashMagma ℍ]
        (data : BTree α)
        (pos : Skeleton)
        (pInData : isInTree data pos)
        : forall (chooser : Skeleton -> PMoves ℍ -> Option ChooserMoves)
        , have itree := medTrees data
          have da := ⟨ data , itree.getI ⟩
        arbitrage pos da (SemiGoodProposer itree) chooser = Player.Proposer
:= by
  revert pos
  induction data with
  | leaf v =>
    simp [arbitrationInit , arbitrage, medTrees, ABTree.getI, condWProp, propTree,ABTree.getI', ABTree.map]
  | node bl pr IL IR =>
    intros pos posInTree chooser
    unfold arbitrage
    simp [medTrees]
    unfold SemiGoodProposer
    sorry


-- Propose can defend.
theorem defenseWins {α ℍ : Type}[BEq ℍ][LawfulBEq ℍ] [Hash α ℍ][HashMagma ℍ]
        (data : BTree α)
        : forall (chooser : Skeleton -> PMoves ℍ -> Option ChooserMoves)
        , have itree := medTrees data
          have da := ⟨ data , itree.getI ⟩
        arbitrationInit da (SemiGoodProposer itree) chooser = Player.Proposer :=
 by intro chooser
    induction data with
    | leaf v =>  simp [arbitrationInit , arbitrage, medTrees, ABTree.getI, condWProp, propTree,ABTree.map, ABTree.getI']
    | node bl br blH brH =>
      simp at *
      unfold arbitrationInit; unfold arbitrage; unfold SemiGoodProposer
      simp [medTrees]
      sorry

-- We are going to hit a wall here. Proposer can defend when skeleton is a valid
-- path in the tree.
