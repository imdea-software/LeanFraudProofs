import FraudProof.DataStructures.Hash
import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.MTree

-- * Disputable Assertions
-- Disputable assertins (from Arbitrum) are assertions made by agents in the
-- system that can be disputed/challenged.
-- In a way, DAs are pieces of data plus the result of some computation.


structure GenDA (α β : Type) where
  dt : α
  res : β
  -- From context there is a computational process |f| such that: |res = f(dt)|
  -- Other agents can challenge that.

structure FromBtoMTree (α ℍ: Type) where
  data : BTree α
  merkleTree : ℍ
  -- Implicit assumption: this.merkleTree = hash_BTree this.data
