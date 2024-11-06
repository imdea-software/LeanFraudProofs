import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Players

-- Data Structures
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

import FraudProof.Extras.BToMTree

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


-- Functional
def chooserPath {α ℍ : Type}
    [hash : Hash α ℍ][maghash : HashMagma ℍ]
   -- knowledge
   (data : BTree α)
   -- path to element
   (path : Skeleton)
   : Option (Fin path.length -> ℍ × ℍ -> Option ChooserSmp)
   -- Compute hashes
   := have abdata := @propTree _ _ hash maghash data
   sorry
   -- match OBCollect _ path abdata with
   -- | .some ( ⟨ _ , .inl _ ⟩ ) => some _
   -- -- Bad cases
   -- | .some (⟨ _ , .inr _ ⟩ ) => none
   -- | .none => none
