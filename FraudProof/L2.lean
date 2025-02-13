-- Data Structures
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

-- Import Data Challenge
-- Players Data Availability Challenge
import FraudProof.Players.FromBToMTree
-- Data Availability Challenge Game
import FraudProof.Games.Base.FromBtoMTree
-- End Data Challenge
-- Players Data Availability Challenge

def find_left_invalid {α : Type}
  (val : α -> Bool) : BTree α -> Option Skeleton
  | .leaf a => if val a then none else some []
  | .node bl br =>
    match find_left_invalid val bl with
    | .none => (find_left_invalid val br).map (fun ls => ls.concat (.inr ()))
    | .some ph => .some $ ph.concat $ .inl ()


def honest_chooser_safe_layer2_scheme {α ℍ : Type}
  [BEq ℍ]
  [hash : Hash α ℍ][mag : HashMagma ℍ]
  --
  (val_fun : α -> Bool)
  -- this could be a sequence too
  (public_data : (ABTree α Unit) )
  -- Prop Player
  ( da_gen : ABTree α Unit
           -- Proposer generates a DA and gives their strategy
           -> (ABTree ℍ Unit × ℍ )
           × (ABTree (Option α) (Option (ℍ × ℍ))) )
  : Option (ABTree ℍ Unit × ℍ)
 := -- From public_data proposer proposes a hash tree and top hash
    have ⟨ proposed , proposer_str ⟩ := da_gen public_data
    -- We would like to have something like this, but we cannot.
    -- if chooser_challenge_hash_tree (public_data.toB.map hash.mhash) proposed.2
    -- [Future Martin: why not? it is public knowledge]
    -- if chooser_challenge_hash_tree (proposed.1.toB) proposed.2
    if chooser_challenge_hash_tree (public_data.toB.map hash.mhash) proposed.2
    -- Other challenges, but comitting to top hash.
    -- Chooser accepts proposed data matches hashes. Now, everything should be
    -- other violations. For example, repeated elements, invalid elements.
    then
      match find_left_invalid val_fun public_data.toB with
      | .none => some proposed -- accepted
      | .some path =>
        -- One way is to challenge it while we reveal path.
        match elem_in_tree_forward ⟨ path , ( _ , proposed.2 ) ⟩
                     _ -- we are
                     _chooser
        with
        | Player.Proposer => .none
        | Player.Chooser => _ -- impossible case
        -- Another is ask it to reveal a path and challenge validity.

    -- Challenge markle tree construction.
    else match @treeArbitrationGame _ _ _ hash mag
                    -- DA challenging
                    ⟨ proposed.1.toB , proposed.2 ⟩
                    -- Strategies
                    proposer_str (@simpChooser _ _ _ ⟨ id ⟩ _ proposed.1.toB)
         with
         | .Chooser => none
         -- This is dead code, good chooser does not lose when plays.
         | .Proposer => some proposed
