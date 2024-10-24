import FraudProof.DAssertions
import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Players

import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

-- We assume the DA |da| was proposed by the proposer.
-- If it is right, the proposer wins.
-- If it is wrong, the chooser wins.
-- Each call function call here is a contract invokation.
def arbitrage
    {α ℍ : Type}
    [BEq ℍ]
    [o : Hash α ℍ][HashMagma ℍ]
    --
    (da : FromBtoMTree α ℍ)
    -- Naive way to implement it.
    (proposer : ℍ -> (ℍ × ℍ)) -- Destruct hashes
    -- Why not |BNodeTree ℍ × ℍ|?
    (chooser : ℍ -> ℍ -> ℍ -> Chooser.Side)
    -- Think a bit more about this one.
    : Winner
    :=
    match da.data with
    | .leaf v => if o.mhash v == da.merkleTree then Player.Proposer else Player.Chooser
    | .node bl br =>
      let ⟨ hl , hr ⟩ := proposer da.merkleTree
      match chooser da.merkleTree hl hr with
      | .Left => arbitrage ⟨ bl , hl ⟩ sorry sorry -- TODO
      | .Right => arbitrage ⟨ br , hr ⟩ sorry sorry -- TODO

-- The problem with this is that |proposer| and |chooser| are super general, and
-- not real implementations.
