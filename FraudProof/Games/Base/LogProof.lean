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

-- def comb_tree {α β: Type}(inj : α -> β) (f : β -> β -> β) (p q : ABTree α β) : ABTree α β
--  := .node (f (ABTree.getI' inj id p) (ABTree.getI' inj id q)) p q

def comb_tree_homogeneous {α: Type}(f : α -> α -> α) (p q : ABTree α α) : ABTree α α
 := .node (f (ABTree.hget p) (ABTree.hget q)) p q

def triangles_tree {ℍ : Type}{lgn : Nat}
  (triag : Sequence (2^lgn) (ℍ × ℍ × ℍ) )
  : ABTree (ℍ × ℍ × ℍ) (ℍ × ℍ × ℍ)
  :=
  consume_seq
  (comb_tree_homogeneous
    (fun l r => ( l.1  , r.2.1 , l.2.1 ))) -- l.2.1 = r.1 (it's the connection)
  (seqMap .leaf triag)

-- Now we can define two revelers, depending on the game.
-- One that offers the /hidden/ hash, mid or sibling hash.
def game_triangles_tree_single_hash {ℍ : Type}
  (tree : ABTree (ℍ × ℍ × ℍ) (ℍ × ℍ × ℍ))
  : ABTree ℍ ℍ
  := ABTree.map (fun t => t.2.2) (fun t => t.2.2) tree

def proposer_triangles_tree_single_hash {ℍ : Type} {lgn : Nat}
  (skl : Sequence (2^lgn) SkElem)
  (top_hash : ℍ)
  (hashes : Sequence (2^lgn) (ℍ × ℍ))
  : ABTree ℍ ℍ
  := game_triangles_tree_single_hash
    $ triangles_tree
    $ @gen_triangles _ _ (by exact pow_gt_zero) skl top_hash hashes

-- One that offers ranges and siblings at leaves.
def game_triangles_tree {ℍ : Type}
  (tree : ABTree (ℍ × ℍ × ℍ) (ℍ × ℍ × ℍ))
  : ABTree ℍ (Range ℍ × Range ℍ)
  := ABTree.map (fun t => t.2.2) (fun t => ((t.1, t.2.2) , (t.2.2, t.2.1))) tree

--
def proposer_triangles_tree {ℍ : Type} {lgn : Nat}
  (skl : Sequence (2^lgn) SkElem)
  (top_hash : ℍ)
  (hashes : Sequence (2^lgn) (ℍ × ℍ))
  : ABTree ℍ (Range ℍ × Range ℍ)
  := game_triangles_tree
    $ triangles_tree
    $ @gen_triangles _ _ (by exact pow_gt_zero) skl top_hash hashes

-- * Chooser
-- Similar to proposer, but what's the chooser transformation.
-- It is actually similar, no? We know what to do at each level.
-- But how do we decide mid levels?
