import FraudProof.Hash
import FraudProof.Value
import FraudProof.MTree


import Batteries.Data.List.Basic

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

-- Hash Structure describing |n| moves.
structure HashChallenger ( n : Nat) where
  -- Nodes
  node : Fin n -> Hash
  -- Siblings
  sibling : Fin n -> PathElem

-- Simpler definition.
structure  Challenger ( gameLength : Nat) where
    -- Leaf value
    value : Value
    -- Hash Strategies
    hashStr : HashChallenger gameLength

