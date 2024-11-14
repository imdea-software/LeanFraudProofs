import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Players

-- Data Structures
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

import FraudProof.Extras.BToMTree

import FraudProof.Games.Base.ElemInTree -- ElemInTree DA and defs

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
--
-- ** Dataless Choosers.
--
-- Fun fuct: Intermediate chooser does not need to know elements.
-- To challenge a DA, Choosers need to know the elements.
--
-- Here, after doing some proofs, I hit a wall of Hash Assumptions.
-- Maybe I can skip them using full data choosers.
--
def chooserNoData {ℍ : Type}
  [BEq ℍ][mag : HashMagma ℍ]
  : (ℍ × ℍ × ℍ -> Option ChooserSmp)
  := fun ⟨ h , hl , hr ⟩
     => some $ if h != mag.comb hl hr
        then .Now
        else .Continue ()

def hasManyChoosers {ℍ : Type}{n : Nat}
  [BEq ℍ][HashMagma ℍ]
  :  Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp)
  := replicate chooserNoData


-- ** Dataful Choosers
-- Here we do not say anything about it being wrong, right?
-- So, we have a path, an element and an implicit tree.
-- Implicit tree |t : BTree α| such that | foldHash t = da.mtree|.
-- We know tke tree and we play a game to discover some wrong hash in the path.
-- We stop when we found one.
def chooserData {α ℍ : Type} { n : Nat }
  [BEq ℍ]
  -- Here I am skipping some steps assuming we know
  -- the tree elements and all intermediate hashes.
  (data : ABTree (α × ℍ) (ℍ × ℍ × ℍ))
  --
  (da : ElemInTreeN n α ℍ)
  --
  : (Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
  := match n , data with
  | .zero , _ => nilSeq
  -- Okay
  | .succ _pn , .node trustedH hl hr  =>
    Fin.cons
      -- This step strategy
       (fun proposed => -- we know that hashes are correct here.
       if proposed.2.1 != hl.getHash ∨ proposed.2.2 != hr.getHash
       then some .Now
       else some (.Continue ()))
      -- Rest steps.
      -- Here if we continue playing means that /proposed.2.1 = trustedH.2.1/
      -- and /proposed.2.2 = trustedH.2.2/
      (match da.data.2 0 with
      | .inl _ => chooserData hl ⟨ ⟨ da.data.1 , Fin.tail da.data.2 ⟩ , trustedH.2.1 ⟩
      | .inr _ => chooserData hr ⟨ ⟨ da.data.1 , Fin.tail da.data.2 ⟩ , trustedH.2.2 ⟩)
  -- Challenge in any other case.
  | _ , _ => replicate (fun _ => some .Now)

----------------------------------------
