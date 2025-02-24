-- Data Structures
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes
import FraudProof.DataStructures.Sequence

-- Import Data Challenge
-- Data Availability Challenge Game
import FraudProof.Games.GameDef
import FraudProof.Games.FromBtoMTree
import FraudProof.Games.ElemInTree
-- End Data Challenge
-- Players Data Availability Challenge

def IndexPath : Type := ( i : Nat ) × ISkeleton i

-- find (if there is one) the leftest invalid value.
def find_left_invalid {α : Type}
  (val : α -> Bool) : BTree α -> Option IndexPath
  | .leaf a => if val a then none else some ⟨ 0 , .nil ⟩
  | .node bl br =>
    match find_left_invalid val bl with
    | .none => (find_left_invalid val br).map
     (fun ⟨ n , ls ⟩ => ⟨ n.succ, ls.snoc .Right⟩ )
    | .some ⟨ n , ls ⟩ => .some $ ⟨ n.succ, ls.snoc .Left ⟩

inductive HonestActions (Path : Type) : Type
  where | DAC | Invalid (p : Path) | Ok

def honest_chooser {α ℍ : Type}
  [BEq ℍ][Hash α ℍ][HashMagma ℍ]
  (val_fun : α -> Bool)
  (public_data : BTree α) (da_mtree : ℍ)
  : HonestActions IndexPath
 :=
 -- Check if the merkle tree matches. bs
 if da_mtree == public_data.hash_BTree
 then match find_left_invalid val_fun public_data with
      | .none => .Ok
      | .some ph => .Invalid ph
 else .DAC

def honest_chooser_filter {α ℍ : Type}
  [BEq α][BEq ℍ][Hash α ℍ][HashMagma ℍ]
   (val_fun : α -> Bool)
   --
   (proposed_da : BTree α × ℍ)(proposed_str : ABTree (Option α) (Option (ℍ × ℍ)))
   --
   : Option (BTree α × ℍ)
   := match honest_chooser val_fun proposed_da.1 proposed_da.2 with
   | .Ok => .some proposed_da
   | .Invalid ph =>
     match elem_in_tree_forward ⟨ ph , ( _ , proposed_da.2) ⟩ _proposer _chooser with
        | .Proposer => .some proposed_da
        | .Chooser => .none
   | .DAC =>
     match data_challenge_game ⟨ proposed_da.1 , proposed_da.2 ⟩ proposed_str _chooser with
    | .Proposer => .some proposed_da
    | .Chooser => .none
