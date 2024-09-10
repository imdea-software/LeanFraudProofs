import FraudProof.Hash
import FraudProof.Value
import FraudProof.MTree


section Challenger
----------------------------------------------------------------------
-- ** Challengers play two roles.
-- They initialize the game and also play it.
-- structure Challenger where
--     -- To begin the game, challengers propose a position, an element and it's hash.
--     init : Nat × Value × Hash
--     -- To play the game, at each turn, challengers, given the current hashes,
--     -- propose a new hash in the middle.
--     strategy : Hash → Hash → ( Nat × Hash)
--     -- Final step, given bot and top such that pos(bot) + 1 == pos(top), produces
--     -- the missing hash.
--     final : Hash → Hash → Hash

structure HC (n : Nat) where
  -- Hashes along the way
  pathNode : Fin ( n + 1 ) -> Hash
  -- Path elem knows how to hash.
  pathSib : Fin n -> PathElem

-- Hash Structure describing |n| moves.
structure HashChallenger ( n : Nat) where
  -- Nodes
  node : Fin n  -> Hash
  -- Siblings
  sibling : Fin n -> PathElem

-- Simpler definition.
structure  Challenger ( gameLength : Nat) where
    -- Leaf value
    value : Value
    -- Hash Strategies
    hashStr : HashChallenger gameLength
----------------------------------------------------------------------
end Challenger

section Challenged
----------------------------------------------------------------------
-- Challenged
-- ** Defender can choose between two different ranges.
-- So we define the two possible moves as
inductive Side : Type :=
    | Left
    | Right

-- Challenged players chose between hashes at each moment.
structure Challenged where
    -- Strategy, given two ranges of hashes chosses one.
    -- [Hbot, Hmid] , [Hmid, Htop] -> Left/Right
    strategy : Hash → Hash → Hash → Side

end Challenged
