-- import FraudProof.DAssertions
import FraudProof.Games.GameDef -- Players, Winner

import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

-- import FraudProof.Extras.BToMTree -- Indexing MMTrees

import FraudProof.Games.GenericTree -- Generic Game

----------------------------------------
-- * BTree as hashes.
-- We know the structure of the data plus the hashes of their leaves.
structure ComputationTree (ℍ : Type) where
  computation : BTree ℍ -- Btree in this case, in can be generalized
  res : ℍ
  -- {𝔸}, fold 𝔸_hash computation = res
  -- one binary operation and leafs (In this case, that's why BTree)
----------------------------------------

@[simp]
def treeArbitrationGame {α ℍ : Type}
    [BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
    (da : ComputationTree ℍ)
    --
    (reveler : ABTree (Option α) (Option (ℍ × ℍ)) )
    (chooser : ABTree Unit (ℍ × ℍ × ℍ -> Option ChooserMoves))
    --
    : Winner :=
    @treeCompArbGame ℍ α Unit ℍ
      -- Leaf winning condition
      (fun ha data res => (o.mhash data == ha) ∧ (ha == res))
      -- Node winning condition
      (fun _ r hl hr =>  m.comb hl hr == r)
      -- DA
      ⟨ da.computation , da.res ⟩
      -- Revelear Strategy
      reveler
      -- Chooser Strategy
      (ABTree.map
        (fun _ => ())
        (fun fhs ⟨hrs , hl , hr ⟩ => fhs ⟨ hrs, hl , hr ⟩)
        chooser)
----------------------------------------

@[simp]
def arbitrationTree {α ℍ : Type}
    [BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
    (arena : ABTree Unit Unit)
    (res : ℍ)
    --
    (reveler : ABTree (Option α) (Option (ℍ×ℍ)) )
    (chooser : ABTree Unit (ℍ × ℍ × ℍ -> Option ChooserMoves))
    --
    : Winner :=
    @treeCompArbGame Unit α Unit ℍ
      -- Leaf winning condition
      (fun _ a hres => o.mhash a == hres)
      -- Node winning condition
      (fun _ r hl hr =>  m.comb hl hr == r)
      -- DA
      ⟨ arena , res ⟩
      -- Revelear Strategy
      reveler
      -- Chooser Strategy
      (ABTree.map (fun _ => ()) (fun fhs ⟨hrs , hl , hr ⟩ => fhs ⟨ hrs, hl , hr ⟩) chooser)
