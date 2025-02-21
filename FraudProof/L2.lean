-- Data Structures
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes
import FraudProof.DataStructures.Sequence

-- Import Data Challenge
-- Players Data Availability Challenge
import FraudProof.Players.FromBToMTree
-- Data Availability Challenge Game
import FraudProof.Games.Base.FromBtoMTree
import FraudProof.Games.Base.ElemInTree
-- End Data Challenge
-- Players Data Availability Challenge

def find_left_invalid {α : Type}
  (val : α -> Bool) : BTree α -> Option ((i : Nat) × ISkeleton i)
  | .leaf a => if val a then none else some ⟨ 0 , nilSeq ⟩
  | .node bl br =>
    match find_left_invalid val bl with
    | .none => (find_left_invalid val br).map
     (fun ⟨ n , ls ⟩ => ⟨ n.succ, snocSeq (.inr ()) ls⟩ )
    | .some ⟨ n , ls ⟩ => .some $ ⟨ n.succ, snocSeq (.inl ()) ls ⟩

inductive HonestActions (Path : Type) : Type where | DAC | Invalid Path | Ok

section OneHonestAgentArbLegacy

-- Value Type and Hash types
variable (α ℍ : Type)
variable (hash : Hash α ℍ)

def honest_chooser [BEq ℍ]
  (val_fun : α -> Bool)
  -- this could be a sequence too
  (public_data : BTree α)
  --
  (da_data : BTree α)
  (da_mtree : ℍ)
  : HonestActions
 :=
 if da_mtree == public_data.hash_BTree.hash
 then match find_left_invalid val_fun public_data with
      | .none => .Ok
      | .some ph => Invalid ph
 else DAC

end OneHonestAgentArbLegacy
