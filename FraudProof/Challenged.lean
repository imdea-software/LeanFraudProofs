import FraudProof.Hash

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
