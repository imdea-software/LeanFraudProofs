import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.GenericTree -- Generic Game trees
import FraudProof.Games.ElemInTree -- Linear basic game definition

import FraudProof.DataStructures.Sequence

def comb_tree_heterogeneous {α β: Type}(lf : α -> β) (f : β -> β -> β) (p q : ABTree α β) : ABTree α β
 := .node (f (ABTree.getI' lf id p) (ABTree.getI' lf id q)) p q

def comb_tree_homogeneous {α: Type}(f : α -> α -> α) (p q : ABTree α α) : ABTree α α
 := .node (f (ABTree.hget p) (ABTree.hget q)) p q

-- Log game
def game_arena {lgn : Nat}
  (skl : Sequence (2^lgn) SkElem)
  : ABTree SkElem Unit
  := Sequence.consume_pow (comb_tree_heterogeneous (fun _ => ()) (fun _ _ => ()))
   $ skl.map .leaf

-- One follows side
def get_spine {α : Type} (side : SkElem)( e : α × α ) : α
  := match side with
     | .Left => e.1
     | .Right => e.2

-- the other one the opposite
def get_sibling {α : Type} (side : SkElem)( e : α × α ) : α
  := match side with
     | .Left => e.2
     | .Right => e.1

-- Extracting from proposer
@[simp]
def extract_intermed_hashes {ℍ : Type}{n : Nat}
  (skl : Sequence n SkElem) (prop : Sequence n (ℍ × ℍ))
  : Sequence n ℍ
  := skl.zip_with get_spine prop

@[simp]
def extract_sibling_hashes {ℍ : Type}{n : Nat}
  (skl : Sequence n SkElem) (prop : Sequence n (ℍ × ℍ))
  : Sequence n ℍ
  := skl.zip_with get_sibling prop

-- * Arena
def built_up_arena {n : Nat}
   : Sequence (2^n) SkElem -> ABTree SkElem Unit
   := gen_info_perfect_tree (Sequence.constant ())

def built_up_arena_backward {n : Nat}
   : Sequence (2^n) SkElem -> ABTree SkElem Unit
   := gen_info_perfect_tree (Sequence.constant ()) ∘ Sequence.reverse

def backward_proposer_to_tree {α : Type}{ n : Nat}
    (sides : Sequence (2^n) SkElem)
    (prop : Sequence (2^n) (α × α) )
    : ABTree α α
    := gen_info_perfect_tree
       -- nodes
       (Sequence.reverse
       $ Sequence.init -- Drop last hash (in this case is hash of the element [forward])
       $ sequence_coerce (by have pg := @pow_gt_zero n; omega) -- 2^n - 1 + 1 = 2^n [lengt computation]
       $ extract_intermed_hashes sides prop) -- Spine hashes)
       -- leaves
       (Sequence.reverse $ extract_sibling_hashes sides prop)

-- Forward proposer gives |p.1| as top and |p.2| as sibling.
def forward_proposer_to_tree {α : Type}{ n : Nat}
    -- (sides : Sequence (2^n) SkElem)
    (prop : Sequence (2^n) (α × α) )
    : ABTree α α
    := gen_info_perfect_tree
       -- nodes
       ( Sequence.init -- Drop last hash  (top hash [forward])
       $ sequence_coerce (by have pg := @pow_gt_zero n; omega) -- 2^n - 1 + 1 = 2^n [lengt computation]
       $ Sequence.map (fun p => p.1) prop) -- Spine hashes
       ( Sequence.map (fun p => p.2) prop) -- leaves


theorem proposer_winning_mod {ℍ : Type} {lgn : Nat}
       [BEq ℍ][LawfulBEq ℍ][HashMagma ℍ] -- Condition checking
       (da : ElemInTreeH (2^lgn) ℍ)
       (proposer : Sequence (2^lgn) (ℍ × ℍ))
       (wProp : elem_in_reveler_winning_condition_backward da proposer)
       (chooser : ABTree Unit (Range ℍ -> ℍ -> Option ChooserMoves))
       : spl_game
         ({data := built_up_arena_backward da.data , res := da.mtree})
         ( ABTree.map .some .some $ backward_proposer_to_tree da.data proposer)
         chooser
         = Player.Proposer
       := by
       apply simp_game_reveler_wins
       sorry

theorem proposer_winning_mod_forward {ℍ : Type} {lgn : Nat}
       [BEq ℍ][LawfulBEq ℍ][HashMagma ℍ] -- Condition checking
       (da : ElemInTreeH (2^lgn) ℍ)
       (proposer : Sequence (2^lgn) (ℍ × ℍ))
       (wProp : elem_in_reveler_winning_condition_forward da proposer)
       (chooser : ABTree Unit (Range ℍ -> ℍ -> Option ChooserMoves))
       : spl_game
         ({data := built_up_arena da.data , res := da.mtree})
         ( ABTree.map .some .some $ forward_proposer_to_tree proposer)
         chooser
         = Player.Proposer
 := by
    apply simp_game_reveler_wins
    revert lgn; intro lgn
    induction lgn with
    | zero =>
        intros da proposer wProp
        unfold reveler_winning_condition_simp_game
        simp [built_up_arena,gen_info_perfect_tree,get_sibling]
        simp [forward_proposer_to_tree]
        simp [gen_info_perfect_tree]
        simp [elem_in_reveler_winning_condition_forward] at wProp
        have ⟨ singH , midH ⟩ := wProp
        simp [SingleLastStepH] at midH
        rw [singH]
        assumption
    | succ pnlgn HInd =>
       intros da proposer wProp
       unfold reveler_winning_condition_simp_game
       simp [forward_proposer_to_tree, built_up_arena, gen_info_perfect_tree]
       apply And.intro
       ·
         have hind := HInd ⟨ (half_split_pow da.data).1
                           , ⟨ da.mtree.1
                           , ((Sequence.init ( @sequence_coerce _ _ (2^(pnlgn.succ) -1 + 1) sorry (proposer.map (fun p => p.1) )) ).perfect_split).2.1 ⟩ ⟩
                             (half_split_pow proposer).1
         simp [built_up_arena] at hind
         simp [forward_proposer_to_tree] at hind
         rw [<- half_perfect_split_same]
         rw [<- perfect_split_constant]
         -- Half_split map
         -- apply hind
         sorry
       · sorry

-- * Chooser
-- Similar to proposer, but what's the chooser transformation.
-- It is actually similar, no? We know what to do at each level.
-- But how do we decide mid levels?
