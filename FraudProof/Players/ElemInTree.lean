import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Players

-- Data Structures
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

import FraudProof.Extras.BToMTree

----------------------------------------
-- * Proposer
-- Functional
def proposerPath {α ℍ : Type}
    [hash : Hash α ℍ][maghash : HashMagma ℍ]
    (data : BTree α)
    (path : Skeleton)
    : Option (Fin path.length -> Option (ℍ × ℍ))
 :=
 -- compute intermedeate hashes
 have abdata := @propTree _ _ hash maghash data
 match OBCollect (fun p => some p.2) path abdata with
    -- Path leading to a value
    | .some (⟨ seq , .inl _ ⟩ ) => some seq
    -- Path leading to a node in the tree.
    | .some (⟨ _   , .inr _ ⟩ ) => none
    -- Path longer than tree (following that path).
    | .none => none

def proposerPathN {α ℍ : Type}{n : Nat}
    [hash : Hash α ℍ][maghash : HashMagma ℍ]
    (data : BTree α)
    (path : ISkeleton n)
    : Option (Fin n -> Option (ℍ × ℍ))
 := -- compute intermedeate hashes
 have abdata := @propTree _ _ hash maghash data
 match OBCollectI (fun p => some p.2) path abdata with
    -- Path leading to a value
    | .some (⟨ seq , .inl _ ⟩ ) => some seq
    -- Path leading to a node in the tree.
    | .some (⟨ _   , .inr _ ⟩ ) => none
    -- Path longer than tree (following that path).
    | .none => none
----------------------------------------

----------------------------------------
-- * Chooser
-- Fun fuct: Intermediate chooser does not need to know elements.
-- To challenge a DA, Choosers need to know the elements.
--

def chooserNoData {ℍ : Type}
  [BEq ℍ][mag : HashMagma ℍ]
  : (ℍ × ℍ × ℍ -> Option ChooserSmp)
  := fun ⟨ h , hl , hr ⟩
     => some $ if h != mag.comb hl hr
        then .Now
        else .Continue ()

def replicate {α : Type}{n : Nat}(c : α) : Fin n -> α
 := fun _ => c

def hasManyChoosers {ℍ : Type}{n : Nat}
  [BEq ℍ][HashMagma ℍ]
  : Fin n -> (ℍ × ℍ × ℍ -> Option ChooserSmp)
  := replicate chooserNoData
----------------------------------------
