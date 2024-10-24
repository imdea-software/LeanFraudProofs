import FraudProof.DataStructures.Hash
import FraudProof.Players

inductive Player : Type := | Proposer | Chooser
abbrev Winner := Player

-- inductive Winner : Type := | Proposer | Chooser
-- inductive Player : Type := | Proposer | Chooser


-- |Singlecutgame| describes a game cutting once at |cut| the game verifies that
-- there is a path of length |len| between |hb| and |ht|.
-- structure SingleCutGame (cut len : Nat)( hb ht : Hash ) where
--  -- this is the min trusted computation.
--  oneStep : Hash -> Hash -> Hash -> Prop
--  --
--  POne : Proposer.IPlayer cut len hb ht
--  PTwo : Chooser.IPlayer cut len hb ht
