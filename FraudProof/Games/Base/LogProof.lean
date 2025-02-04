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

def comb_tree_heterogeneous {α β: Type}(lf : α -> β) (f : β -> β -> β) (p q : ABTree α β) : ABTree α β
 := .node (f (ABTree.getI' lf id p) (ABTree.getI' lf id q)) p q

def comb_tree_homogeneous {α: Type}(f : α -> α -> α) (p q : ABTree α α) : ABTree α α
 := .node (f (ABTree.hget p) (ABTree.hget q)) p q

-- Log game
def game_arena {lgn : Nat}
  (skl : Sequence (2^lgn) SkElem)
  : ABTree SkElem Unit
  := consume_seq (comb_tree_heterogeneous (fun _ => ()) (fun _ _ => ()))
   $ seqMap .leaf skl

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
@[simp]
def extract_intermed_hashes {ℍ : Type}{n : Nat}
  (skl : Sequence n SkElem) (prop : Sequence n (ℍ × ℍ))
  : Sequence n ℍ
  := seq_zip_with get_spine skl prop

@[simp]
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

theorem proposer_winning {ℍ : Type} {lgn : Nat}
       [BEq ℍ][LawfulBEq ℍ][HashMagma ℍ] -- Condition checking
       (da : ElemInTreeH (2^lgn) ℍ)
       (proposer : Sequence (2^lgn) (ℍ × ℍ))
       (wProp : elem_in_reveler_winning_condition_backward da (seqMap (.Next) proposer))
       (chooser : ABTree Unit
                      ((Range ℍ × Unit × Range ℍ × Range ℍ)
                      -> Option ChooserMoves))
       : tree_computation ({data := game_arena da.data , res := da.mtree})
         (ABTree.map .some (fun p => .some ((), p) ) (proposer_triangles_tree da.data da.mtree.2 proposer))
         chooser = Player.Proposer
        := by revert lgn
              intro lgn
              induction lgn with
              | zero =>
                intros da proposer wProp
                simp [tree_computation, proposer_triangles_tree, gen_triangles, extract_intermed_hashes,get_spine,extract_sibling_hashes]
                simp [get_sibling, triangles_tree, comb_tree_homogeneous,consume_seq]
                simp [game_triangles_tree, game_arena, consume_seq, treeCompArbGame]
                simp [leaf_condition_length_one, condWProp]
                simp [elem_in_reveler_winning_condition_backward] at wProp
                have ⟨ mid, lastH ⟩ := wProp
                simp [SingleLastStepH] at lastH
                simp [SingleMidStep] at mid
                simp [condWProp] at *
                rw [<- mid]
                cases HC : da.data 0
                all_goals {
                  rw [HC] at lastH; simp at *; rw [lastH]
                }
              | succ plgn HInd =>
                intros da proposer wProp
                simp [proposer_triangles_tree,tree_computation,game_triangles_tree, triangles_tree, consume_seq,treeCompArbGame]
                simp [gen_triangles]
                -- simp [seq_zip_with]
                sorry


-- * Arena
def built_up_arena {n : Nat}
   : Sequence (2^n) SkElem -> ABTree SkElem Unit
   := gen_info_perfect_tree (seq_constant ())

def built_up_arena_backward {n : Nat}
   : Sequence (2^n) SkElem -> ABTree SkElem Unit
   := gen_info_perfect_tree (seq_constant ()) ∘ sequence_reverse

def backward_proposer_to_tree {α : Type}{ n : Nat}
    (sides : Sequence (2^n) SkElem)
    (prop : Sequence (2^n) (α × α) )
    : ABTree α α
    := gen_info_perfect_tree
       -- nodes
       (sequence_reverse
       $ Fin.init -- Drop last hash (in this case is hash of the element [forward])
       $ sequence_coerce (by have pg := @pow_gt_zero n; omega) -- 2^n - 1 + 1 = 2^n [lengt computation]
       $ extract_intermed_hashes sides prop) -- Spine hashes)
       -- leaves
       (sequence_reverse $ extract_sibling_hashes sides prop)

-- Forward proposer gives |p.1| as top and |p.2| as sibling.
def forward_proposer_to_tree {α : Type}{ n : Nat}
    -- (sides : Sequence (2^n) SkElem)
    (prop : Sequence (2^n) (α × α) )
    : ABTree α α
    := gen_info_perfect_tree
       -- nodes
       ( Fin.init -- Drop last hash  (top hash [forward])
       $ sequence_coerce (by have pg := @pow_gt_zero n; omega) -- 2^n - 1 + 1 = 2^n [lengt computation]
       $ seqMap (fun p => p.1) prop) -- Spine hashes
       ( seqMap (fun p => p.2) prop) -- leaves

def split_da {ℍ : Type}{lgn : Nat}
 (da : ElemInTreeH (2^lgn.succ) ℍ)
 (proposer : Sequence (2^lgn.succ) (ℍ × ℍ))
 : ( ElemInTreeH (2^lgn) ℍ × ElemInTreeH (2^lgn) ℍ)
 :=
 have mid := extract_intermed_hashes da.data proposer ⟨ 2^lgn - 1 , by sorry ⟩
 have ( left_da , right_da ) := half_split_pow da.data -- backwards
 ( ⟨ right_da , ⟨ da.mtree.1 , mid ⟩ ⟩, ⟨ left_da , ⟨ mid, da.mtree.2⟩ ⟩ )

def split_winning_condition_left {ℍ : Type} {lgn : Nat}
       [BEq ℍ][LawfulBEq ℍ][HashMagma ℍ] -- Condition checking
       (da : ElemInTreeH (2^lgn.succ) ℍ)
       (proposer : Sequence (2^lgn.succ) (ℍ × ℍ))
       (wProp : elem_in_reveler_winning_condition_backward da (seqMap (.Next) proposer))
       :
       elem_in_reveler_winning_condition_backward ( ( split_da da proposer).1 ) ( seqMap (.Next) (half_split_pow proposer).2 )
       := by
 revert lgn; intro lgn; induction lgn with
 | zero =>
   intros da proposer wProp; simp at *
   simp [split_da]
   simp [half_split_pow, Fin.tail, Fin.cons]
   unfold elem_in_reveler_winning_condition_backward; simp
   unfold elem_in_reveler_winning_condition_backward
   simp [SingleMidStep,SingleLastStepH, condWProp]
   simp [seqPerfectSplit,splitSeq, Fin.init, get_spine]
   unfold elem_in_reveler_winning_condition_backward at wProp; simp at wProp
   unfold elem_in_reveler_winning_condition_backward at wProp; simp at wProp
   unfold elem_in_reveler_winning_condition_backward at wProp
   simp [SingleMidStep,SingleLastStepH,condWProp] at wProp
   simp [Fin.tail] at wProp
   apply And.intro
   · exact wProp.2.1
   · exact wProp.2.2
 | succ pnlgn HInd =>
   intros da proposer wProp
   -- have lg :2^(pnlgn.succ) = 2^(pnlgn.succ) - 1 + 1 := sorry
   unfold elem_in_reveler_winning_condition_backward
   sorry

theorem proposer_winning_mod {ℍ : Type} {lgn : Nat}
       [BEq ℍ][LawfulBEq ℍ][HashMagma ℍ] -- Condition checking
       (da : ElemInTreeH (2^lgn) ℍ)
       (proposer : Sequence (2^lgn) (ℍ × ℍ))
       (wProp : elem_in_reveler_winning_condition_backward da (seqMap (.Next) proposer))
       (chooser : ABTree Unit (Range ℍ -> ℍ -> Option ChooserMoves))
       : spl_game
         ({data := built_up_arena_backward da.data , res := da.mtree})
         ( ABTree.map .some .some $ backward_proposer_to_tree da.data proposer)
         chooser
         = Player.Proposer
       := by
       apply simp_game_reveler_wins
       revert lgn; intro lgn
       induction lgn with
       | zero =>
   intros da proposer wProp
   unfold reveler_winning_condition_simp_game
   simp [built_up_arena_backward,gen_info_perfect_tree,get_sibling]
   simp [backward_proposer_to_tree]
   simp [gen_info_perfect_tree]
   simp [leaf_condition_length_one, get_sibling]
   simp [elem_in_reveler_winning_condition_backward] at wProp
   have ⟨ midH , singH ⟩ := wProp
   unfold SingleLastStepH at singH
   unfold SingleMidStep at midH
   simp [condWProp,sequence_reverse] at *
   cases HC : da.data 0
   all_goals { rw [HC] at singH; simp at *; rw [singH]; assumption }
       | succ pnlgn HInd =>
       intros da proposer wProp
       simp [backward_proposer_to_tree, built_up_arena_backward, gen_info_perfect_tree]
       simp [reveler_winning_condition_simp_game]
       rw [half_split_rev]
       simp
       rw [<- perfect_split_constant]
       apply And.intro
       ·
         have hind := HInd
          ⟨ (half_split_pow da.data).2
          , (da.mtree.1, (seqPerfectSplit (sequence_reverse $ Fin.init
                            $ @sequence_coerce _ _ ((2^pnlgn.succ) - 1 + 1) (by have pw := @pow_gt_zero pnlgn.succ; omega)
                            (seq_zip_with get_spine da.data proposer))).2.1 )⟩
          (half_split_pow proposer).1 sorry
         simp at hind
         unfold built_up_arena_backward at hind
         unfold backward_proposer_to_tree at hind
         unfold extract_sibling_hashes at hind
         unfold extract_intermed_hashes at hind
         rw [half_split_rev]
         rw [half_zip_with]
         -- rw [half_zip_with]
         -- rw [<- half_perfect_split_same]
         sorry
         -- exact hind
       ·
         have hind := HInd
          ⟨ (half_split_pow da.data).2
          , ((seqPerfectSplit (Fin.init
                            $ @sequence_coerce _ _ ((2^pnlgn.succ) - 1 + 1) sorry
                            (seq_zip_with get_spine da.data proposer))).2.1 , da.mtree.2)⟩
          (half_split_pow proposer).2 sorry
         sorry

theorem proposer_winning_mod_forward {ℍ : Type} {lgn : Nat}
       [BEq ℍ][LawfulBEq ℍ][HashMagma ℍ] -- Condition checking
       (da : ElemInTreeH (2^lgn) ℍ)
       (proposer : Sequence (2^lgn) (ℍ × ℍ))
       (wProp : elem_in_reveler_winning_condition_forward da (seqMap (.Next) proposer))
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
        simp [leaf_condition_length_one, get_sibling]
        simp [elem_in_reveler_winning_condition_forward] at wProp
        have ⟨ singH , midH ⟩ := wProp
        simp [SingleLastStepH] at midH
        simp [condWProp] at *
        cases HC : da.data 0
        all_goals {
            simp; rw [HC] at singH; simp at singH
            rw [<- midH]
            assumption
        }
    | succ pnlgn HInd =>
       intros da proposer wProp
       unfold reveler_winning_condition_simp_game
       simp [forward_proposer_to_tree, built_up_arena, gen_info_perfect_tree]
       apply And.intro
       ·
         have hind := HInd ⟨ (half_split_pow da.data).1
                           , ⟨ da.mtree.1
                             , (seqPerfectSplit (Fin.init ( @sequence_coerce _ _ (2^(pnlgn.succ) -1 + 1) sorry (seqMap (fun p => p.1) proposer)) )).2.1 ⟩ ⟩
                             (half_split_pow proposer).1
         simp [built_up_arena] at hind
         simp [forward_proposer_to_tree] at hind
         rw [<- half_perfect_split_same]
         rw [<- perfect_split_constant]
         apply hind
         _
       · sorry

       -- simp [backward_proposer_to_tree, built_up_arena, gen_info_perfect_tree]
       -- simp [reveler_winning_condition_simp_game]
       -- rw [half_split_rev]
       -- simp
       -- rw [<- perfect_split_constant]
       -- apply And.intro




-- * Chooser
-- Similar to proposer, but what's the chooser transformation.
-- It is actually similar, no? We know what to do at each level.
-- But how do we decide mid levels?
