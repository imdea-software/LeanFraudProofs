import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.Base.GenericTree -- Generic Game trees
import FraudProof.Games.Base.ElemInTree -- Linear basic game definition
import FraudProof.Games.Base.LogarithmicTransformation

import FraudProof.DataStructures.Sequence

-- Non-emtpy path to generate complete perfect tree
@[simp]
def toTreeSeq (lgn : Nat) := Sequence (2^lgn.succ - 1)

def skeleton_arena {lgn : Nat}
  (skl : toTreeSeq lgn SkElem)
  : ABTree SkElem Unit
  := ABTree.map id (fun _ => ())
  $ perfectSeq skl

-- One follows side
def get_spine {α : Type} (side : SkElem)( e : α × α ) : α
  := match side with
     | .inl _ => e.1
     | .inr _ => e.2
-- the other one the opposite
def get_sibling {α : Type} (side : SkElem)( e : α × α ) : α
  := match side with
     | .inl _ => e.2
     | .inr _ => e.1

-- Extracting from proposer
def extract_intermed_hashes {ℍ : Type}{n : Nat}
  (skl : Sequence n SkElem) (prop : Sequence n (ℍ × ℍ))
  : Sequence n ℍ
  := seq_zip_with get_spine skl prop

def extract_sibling_hashes {ℍ : Type}{n : Nat}
  (skl : Sequence n SkElem) (prop : Sequence n (ℍ × ℍ))
  : Sequence n ℍ
  := seq_zip_with get_sibling skl prop

-- Fussioning everything together here are all triangles such that
-- proposer says
-- (a , b , c) {side} := op_side side a c = b
def gen_triangles {ℍ : Type}{n : Nat}{nNZ : 0 < n}
  (skl : Sequence n SkElem)
  (top_hash : ℍ)
  (hashes : Sequence n (ℍ × ℍ))
  : Sequence n (ℍ × ℍ × ℍ)
  :=
  have spine : Sequence n ℍ := extract_intermed_hashes skl hashes
  have tupled_interval : Sequence n (ℍ × ℍ)
    := seq_zip_with (fun a b => (a,b)) spine
      (sequence_coerce (by apply Nat.succ_pred_eq_of_pos; assumption)
      $ Fin.snoc (tailSeq' spine) top_hash)
  seq_zip_with (fun (a,b) c => (a,b,c)) tupled_interval (extract_sibling_hashes skl hashes)

def triangles_tree_to_range {ℍ : Type}
  : ABTree (ℍ × ℍ × ℍ) (ℍ × ℍ × ℍ) -> ABTree ℍ (Range ℍ × Range ℍ)
  | .leaf (_ , _ , sib) => .leaf sib
  | .node (_ , mid, _ ) nleft nright => _

-- def proposer_transformation {ℍ : Type}{lgn:Nat}
--     (top_hash : ℍ)
--     (skl : Sequence (2^lgn.succ - 2)  SkElem)
--     (hashes : Sequence (2^lgn.succ - 2) (ℍ × ℍ))
--     : ABTree ℍ ℍ
--     := have spine : Sequence (2^lgn.succ - 1) ℍ
--             := sequence_coerce (by simp; sorry )
--                $ Fin.snoc (extract_intermed_hashes skl hashes) top_hash
--     perfectSeq spine
