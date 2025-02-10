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


def honest_chooser_safe_layer2_scheme {α ℍ : Type}
  [BEq ℍ]
  [hash : Hash α ℍ][mag : HashMagma ℍ]
  (public_data : (ABTree α Unit) )
  -- Prop Player
  ( da_gen : ABTree α Unit -> (ABTree ℍ Unit × ℍ ) × (ABTree (Option α) (Option (ℍ × ℍ))) )
  -- ( str_gen : ABTree α Unit ->   )
  -- Chooser
  : Option (ABTree ℍ Unit × ℍ)
 := -- From public_data proposer proposes a hash tree and top hash
    have ⟨ proposed , proposer_str ⟩ := da_gen public_data
    -- We would like to have something like this, but we cannot.
    -- if chooser_challenge_hash_tree (public_data.toB.map hash.mhash) proposed.2
    if chooser_challenge_hash_tree (proposed.1.toB) proposed.2
    -- Other challenges, but comitting to top hash.
    -- Chooser accepts proposed data matches hashes. Now, everything should be
    -- other violations. For example, repeated elements, invalid elements.
    then sorry
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
