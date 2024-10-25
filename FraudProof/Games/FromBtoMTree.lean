import FraudProof.DAssertions
import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Players

import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

-- Simply structuere
structure FromBtoMTree (α ℍ: Type) where
  data : BTree α
  merkleTree : ℍ
  -- Implicit assumption: this.merkleTree = MTree.hash $ hash_BTree this.data
  -- This is missing BEq ℍ, isn't it?

-- We assume the DA |da| was proposed by the proposer.
-- If it is right, the proposer wins.
-- If it is wrong, the chooser wins.
--
-- Each call function call here is a contract invokation.
def arbitrage
    {α ℍ : Type}
    [BEq ℍ]
    [o : Hash α ℍ][m : HashMagma ℍ]
    (pos : Skeleton)
    --
    (da : FromBtoMTree α ℍ)
    -- Naive way to implement it. Sequencial moves,
    -- the |chooser| sees what the |proposer| proposes, and then (in the next
    -- step) the |proposer| seer what the |chooser| chosed through the |pos|.
    (proposer : Skeleton -> ProposerMoves ℍ)
    (chooser : Skeleton -> ProposerMoves ℍ -> ChooserMoves)
    -- Think a bit more about this one.
    : Winner
    :=
    match _h : da.data with
    -- End of the game!
    | .leaf v => if o.mhash v == da.merkleTree then Player.Proposer else Player.Chooser
    -- Moves are required
    | .node bl br =>
      -- Proposer moves
      let proposed := proposer pos
      -- Chooser moves
      match chooser pos proposed with
      -- Chooser challenges proposed hashes
      | .Now => if m.comb proposed.left proposed.right == da.merkleTree
                then Player.Proposer
                else Player.Chooser
      -- Chooser continues the game choosing one branch
      | .Continue s =>
         -- Next step is super similar
         match s with
         | .Left =>
           arbitrage
             (pos ++ [ Sum.inl () ]) -- Next position
             ⟨ bl , proposed.left ⟩ -- Next DA to check.
             proposer chooser -- Players don not change
         | .Right =>
           arbitrage
             (pos ++ [ Sum.inr () ]) ⟨ br , proposed.right ⟩
             proposer chooser -- Players don not change
    termination_by sizeOf da.data
    decreasing_by
      all_goals { simp_wf; rw [_h]; simp; try omega}
