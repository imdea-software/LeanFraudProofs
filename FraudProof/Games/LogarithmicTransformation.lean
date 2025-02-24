import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.GenericTree -- Generic Game trees
import FraudProof.Games.ElemInTree -- Linear basic game definition

import FraudProof.DataStructures.Sequence
import FraudProof.Games.RangeDAConditions

----------------------------------------
-- * Tree Search
-- Here is a simple game template, groing through range splitting.
-- DA is 'I know the info such that this computation-tree-scheme is proof that
-- hash |a| reaches hash |b|'. [a,b]
-- At each step at nodes, the reveler provides two segments and the chooser can
-- choose to challenge now if segments do not combine or continues challenging
-- one of the segments.
-- At the last step, the reveler provides a sibiling hash. Taking the side from
-- the computation tree, we can check if the information matches.
--
-- Leaves are path of lenght 1. After that, continuining the game makes no
-- sense. At this point, the proposer need to revel the sibling hash (and side)
-- completing the triplet.
-- [a,b] -> side, c such that |op_side| side a c == b
-- def leaf_condition_length_one {ℍ : Type}[BEq ℍ][HashMagma ℍ]
--   : SkElem -> ℍ -> Range ℍ -> Bool
--   := (fun side prop ⟨ src , dst ⟩ => op_side side src prop == dst)

-- Leaf Triangle approach
-- When checking the triangle
--     h_mid
--   /      \
--   a       b.
--   We need two sides and hashes.
--   + h_mid = op_side side1 a h1
--   + b = op_sid side2 hmid h2
def leaf_triangle {ℍ : Type}[BEq ℍ][HashMagma ℍ]
  : (SkElem × SkElem) -> (ℍ × ℍ) -> Range ℍ -> Bool
  := (fun sides hashes ⟨ src , dst ⟩
  => have h_mid := op_side sides.1 src hashes.1
    op_side sides.2 h_mid hashes.2 == dst
    )

def mid_condition_da_checking {ℍ : Type}[BEq ℍ]
  -- Arena conditions
  : Unit -> Range ℍ -> Range ℍ -> Range ℍ
  -> Bool
  := (fun _
        hres hl hr =>
        let ⟨ parent_from , parent_to⟩ := hres
        let ⟨ left_from , left_to⟩ := hl
        let ⟨ right_from , right_to⟩ := hr
          -- Mid condition is the expected one
        all_true
          -- Path consistency
          -- [a, b] <=> [a,c] and [c,b]
          [ parent_from == left_from
          , parent_to == right_to
          , left_to == right_from
          ]
      )

def tree_computation {ℍ : Type}[BEq ℍ][m : HashMagma ℍ]
    -- DA provides last two sides.
    (da : CompTree SkElem Unit (Range ℍ))
    --
    (proposer : ABTree (Option ℍ)
                       (Option (Range ℍ × Range ℍ)))
    (chooser : ABTree Unit
                      ((Range ℍ × Range ℍ × Range ℍ)
                      -> Option ChooserMoves))
    --
    :=
    treeCompArbGame
      leaf_condition_length_one
      mid_condition_da_checking
      da proposer chooser

-- Min path 2
def tree_computation_triangle {ℍ : Type}[BEq ℍ][m : HashMagma ℍ]
    -- DA provides last two sides.
    (da : CompTree (SkElem × SkElem) Unit (Range ℍ))
    --
    (proposer : ABTree (Option (ℍ × ℍ))
                       (Option (Range ℍ × Range ℍ)))
    (chooser : ABTree Unit
                      ((Range ℍ × Range ℍ × Range ℍ)
                      -> Option ChooserMoves))
    --
    :=
    treeCompArbGame
      leaf_triangle
      mid_condition_da_checking
      da proposer chooser

----------------------------------------
--
-- We want to stop at the last level. And we need an arena prepared for that.
-- A la Haskell
def merge_last_level {α β : Type}
  (tree : ABTree α β)
  : Option (ABTree (α × β × α) β)
  := match tree with
     | .leaf _ => .none
     | .node b (.leaf a1) (.leaf a2) => .some $ .leaf ⟨ a1 , b , a2 ⟩
     | .node b bl br =>
       .node b <$> merge_last_level bl <*> merge_last_level br

def sequence_to_merged_tree {α : Type}{lgn : Nat}
    (seq : Sequence (2^lgn.succ.succ - 1) α)
    : ABTree (α × α × α) α
    := match lgn with
      | .zero => .leaf ⟨ seq.head , seq.tail.head , seq.tail.tail.head ⟩
      | .succ _plgn =>
        have ⟨left, mid, right ⟩ := seq.perfect_split
        .node mid
              (sequence_to_merged_tree left)
              (sequence_to_merged_tree right)

@[simp]
def skeleton_to_merged_tree {lgn : Nat}
  (skl : Sequence (2^lgn.succ.succ - 1) SkElem)
  : ABTree (SkElem × SkElem × SkElem) SkElem
  := sequence_to_merged_tree skl

@[simp]
def triangle_arena {lgn : Nat}
  (skl : Sequence (2^lgn.succ.succ - 1) SkElem)
  : ABTree (SkElem × SkElem) Unit
  := ABTree.map (fun t => ⟨ t.1 , t.2.2 ⟩) (fun _ => ())
  $ sequence_to_merged_tree skl

-- * Chooser is as bit complex.
-- Chooser needs to know the data to build a propoer chooser.
-- I am not sure we can define chooser transformation, same as we did with
-- proposer.
----------------------------------------

----------------------------------------
-- DA + Proposer Algebra?

def da_coerce {α : Type}{n m : Nat}
  (eqN : n = m) (a : ElemInTreeH n α) : ElemInTreeH m α
  := { data := sequence_coerce eqN a.data
     , mtree := a.mtree}

def da_sum {ℍ : Type}{n m : Nat}
  (da_l : ElemInTreeH n ℍ)
  (da_r : ElemInTreeH m ℍ)
  -- (_eq_bounds : da_l.mtree = da_r.data.1)
  : ElemInTreeH (n + m) ℍ
  := { data := da_l.data.append da_r.data
     , mtree := ⟨ da_l.mtree.1 , da_r.mtree.2⟩
     }

def da_split {ℍ : Type}{n : Nat}
  -- Cut
  ( m : Nat ) (mLtn : m ≤ n)
  ( da : ElemInTreeH n ℍ )
  ( mid : ℍ )
  : ElemInTreeH m ℍ × ElemInTreeH (n - m) ℍ
  := have ⟨ left , right ⟩ := da.data.split m mLtn
  ⟨ {data := left , mtree := ⟨ da.mtree.1 , mid ⟩}
  , {data := right, mtree := ⟨ mid , da.mtree.2 ⟩ } ⟩

def da_take {ℍ : Type}{n : Nat}
  -- Cut
  ( m : Nat ) (mLtn : m ≤ n)
  ( da : ElemInTreeH n ℍ )
  ( mid : ℍ )
  : ElemInTreeH m ℍ := (da_split m mLtn da mid).1

def da_drop {ℍ : Type}{n : Nat}
  -- Cut
  ( m : Nat ) (mLtn : m ≤ n)
  ( da : ElemInTreeH n ℍ )
  ( mid : ℍ )
  : ElemInTreeH (n - m) ℍ := (da_split m mLtn da mid).2

lemma da_split_paste {ℍ : Type}{n : Nat}
  -- Cut
  ( m : Nat ) (mLtn : m ≤ n)
  ( da : ElemInTreeH n ℍ )
  ( mid : ℍ )
  : have ⟨l , r ⟩ := da_split m mLtn da mid
    da_coerce (by omega) (da_sum l r)
    = da
  := by
  simp [da_split, da_coerce, da_sum]
  have split_lemma := @split_seq_eq _ _ m mLtn da.data
  simp at split_lemma
  rw [<- split_lemma]
----------------------------------------

----------------------------------------
-- * Alternative definition
-- Intermediary hashes with bounds (coming down from top)
-- to_mid_step [0] = mtree
-- to_mid_step [last] = hash_botom
-- This is the spine. We followed this approach the first time.
-- In this case, we are not checking anything. Good Proposers may have their
-- properties.
-- THIS IS WRONG! We are computing it!
def node_hashes_backward { ℍ : Type }{n : Nat}[HashMagma ℍ]
    (bot_hash : ℍ)
    (skl : Sequence n SkElem)
    (proposer : Sequence n (PMoves ℍ))
    : Sequence n.succ ℍ
    := Sequence.snoc
      (Sequence.zip_with
        (fun side pm => op_side side pm.left pm.right)
        skl
        proposer)
      bot_hash

def logarithmic_proposer_hashes {ℍ}{lgn : Nat}[HashMagma ℍ]
    (da : ElemInTreeH (2^lgn.succ - 1 - 1) ℍ)
    (proposer : Sequence (2^lgn.succ - 1 - 1) (PMoves ℍ))
    : Sequence (2^lgn.succ - 1) ℍ
    := sequence_coerce (by simp; have pZ := @pow_gt_zero lgn; omega)
    $ Sequence.reverse -- We need hash[0] = mtree.1, ... , hash[n] = mtree.2
    $ node_hashes_backward da.mtree.1 da.data proposer

-- Complete Tree Proposer
-- + leftest leaf has da.mtree.1
-- + rightest leaf has da.mtree.2 (computed)
-- There are two lemmas down the file explictly saying this (using sequences).
def complete_tree_proposer
    {ℍ : Type}{lgn : Nat}[HashMagma ℍ]
    (da : ElemInTreeH (2^lgn.succ - 1 - 1) ℍ)
    (proposer : Sequence (2^lgn.succ - 1 - 1) (PMoves ℍ))
    : ABTree ℍ ℍ
    := perfectSeq $ logarithmic_proposer_hashes da proposer

lemma complete_tree_decomp {ℍ : Type}{lgn : Nat}[HashMagma ℍ]
    -- At least two levels. One to use perfectSeq and another to put in mid.
    (da : ElemInTreeH (2^lgn.succ.succ - 1 - 1 ) ℍ)
    (proposer : Sequence (2^lgn.succ.succ -1 -1 ) (PMoves ℍ))
    :
    have ⟨ left, mid, right ⟩ := (logarithmic_proposer_hashes da proposer).perfect_split
    -- perfectSeq (logarithmic_proposer_hashes da proposer)
    complete_tree_proposer da proposer
    = .node mid (perfectSeq left) (perfectSeq right)
    := by
      revert lgn
      intro lgn
      induction lgn with
      | zero =>
        intros da proposer
        simp at *
        simp [complete_tree_proposer,logarithmic_proposer_hashes, node_hashes_backward, perfectSeq]
      | succ pn HInd =>
        intros da proposer
        cases HSeqLeft : (logarithmic_proposer_hashes da proposer).perfect_split with
        | mk left_prop rest =>
          cases HSeqRest : rest with
          | mk mid_prop right_prop =>
            simp [complete_tree_proposer]
            unfold perfectSeq
            simp
            apply And.intro
            · rw [HSeqLeft, HSeqRest]
            · apply And.intro
              · rw [HSeqLeft]; simp [Sequence.perfect_split , perfectSeq]
              · rw [HSeqLeft,HSeqRest]; simp [Sequence.perfect_split, perfectSeq]

-- getters

@[simp]
def get_tree_distance {ℍ : Type}
  : ABTree (ℍ × Nat) (ℍ × Nat × ℍ × Nat × ℍ ) -> Nat
  := ABTree.getI' (fun p => p.2) (fun p=> p.2.1 + p.2.2.2.1)

def get_bot_hash {ℍ : Type}
  : ABTree (ℍ × Nat) (ℍ × Nat × ℍ × Nat × ℍ ) -> ℍ
  := ABTree.getI' (fun p => p.1) (fun p => p.1)
def get_top_hash {ℍ : Type}
  : ABTree (ℍ × Nat) (ℍ × Nat × ℍ × Nat × ℍ ) -> ℍ
  := ABTree.getI' (fun p => p.1) (fun p => p.2.2.2.2)

def tree_distance {ℍ : Type}
  : ABTree ℍ ℍ -> ABTree (ℍ × Nat) (ℍ × Nat × ℍ × Nat × ℍ )
  | .leaf b => .leaf ⟨ b, 0 ⟩
  | .node h bl br =>
      let bl' := tree_distance bl
      let br' := tree_distance br
      .node ⟨ get_bot_hash bl'
            , if get_tree_distance bl' = 0 then 1 else get_tree_distance bl'
            , h
            , if get_tree_distance br' = 0 then 1 else get_tree_distance br'
            , get_top_hash br'
            ⟩
        bl' br'

-- lemmas
lemma get_bot_from_sequence {ℍ : Type}{lgn : Nat}
  (seq_hashes : Sequence (2^lgn.succ - 1) ℍ)
  : seq_hashes.head' sorry
    = get_bot_hash
            (tree_distance
              (perfectSeq seq_hashes))
  := by induction lgn with
        | zero => simp [perfectSeq, tree_distance,get_bot_hash]
                  simp [ABTree.getI']
        | succ pnlgn HInd =>
          simp [perfectSeq, get_bot_hash]
          simp [ABTree.getI']
          have seq_left_ind := HInd (seq_hashes.perfect_split).1
          simp [tree_distance]
          rw [<- seq_left_ind]
          simp [Sequence.perfect_split, Sequence.split]
          sorry

----------------------------------------

-- We are defining the same lemmas and theorems as the first implementations.
-- theorem forall_mid_step {ℍ : Type}
--     [BEq ℍ][HashMagma ℍ] {n : Nat}
--     (da : ElemInTreeH n ℍ)
--     (proposer : Sequence n (PMoves ℍ))
--     (winning_cond : elem_in_reveler_winning_condition_backward da proposer)
--     :
--     forall (i : Nat)(iNZ : 0 < i)(iLtn : i < n),
--         SingleMidStep ⟨ (node_hashes_backward da.mtree.1 da.data proposer).getI i (by omega)
--                       , (proposer.getI i iLtn)
--                       ⟩ = Player.Proposer
--     := sorry

-- theorem last_hash_node_hashes {ℍ : Type}
--     [BEq ℍ][HashMagma ℍ] {n : Nat}
--     (da : ElemInTreeH n ℍ)
--     (proposer : Sequence n (PMoves ℍ))
--     -- We do not need winning_cond here
--     (winning_cond : elem_in_reveler_winning_condition_backward da proposer)
--     : da.mtree.1 =  (node_hashes_backward da.mtree.1 da.data proposer).last
--     := sorry

-- theorem first_hash_node_hashes {ℍ : Type}
--     [BEq ℍ][HashMagma ℍ] {n : Nat}
--     (da : ElemInTreeH n ℍ)
--     (proposer : Sequence n (PMoves ℍ))
--     -- Here we need winning_cond that provides
--     -- |da.mtree.2| = |op_side side proposer 0.left proposer 0.right|
--     (winning_cond : elem_in_reveler_winning_condition_backward da proposer)
--     : da.mtree.2 = (node_hashes_backward da.mtree.1 da.data proposer).head
--     := sorry

-- This are the winning conditions, I first proposed long time ago.
-- So we already have a logarithmic proposer definition and a winning condition.

-- Perfect Splitting DAs  + Reveler + Winning conditions
theorem split_da_perfect_left {ℍ}[BEq ℍ][HashMagma ℍ]{lgn : Nat}
  (da : ElemInTreeH (2^lgn.succ - 1) ℍ)
  (rev : Sequence (2^lgn.succ - 1) (PMoves ℍ))
  -- Good rev
  (lin_rev : elem_in_reveler_winning_condition_backward da rev)
  : let ⟨ left_skl, mid_skl, right_skl ⟩ := da.data.perfect_split
    let ⟨ left_rev, mid_rev, right_rev ⟩ := rev.perfect_split
    let ⟨ h_rev_l , h_rev_r ⟩ := mid_rev
    let top_hash := match mid_skl with
                          | .Left => h_rev_l
                          | .Right => h_rev_r
    let da_left := {data := left_skl , mtree := ⟨ da.mtree.1 ,top_hash ⟩}
    elem_in_reveler_winning_condition_backward da_left left_rev
  := sorry

theorem split_da_perfect_right {ℍ}[BEq ℍ][HashMagma ℍ]{lgn : Nat}
  (da : ElemInTreeH (2^lgn.succ - 1) ℍ)
  (rev : Sequence (2^lgn.succ - 1) (PMoves ℍ))
  -- Good rev
  (lin_rev : elem_in_reveler_winning_condition_backward da rev)
  : let ⟨ left_skl, mid_skl, right_skl ⟩ := da.data.perfect_split
    let ⟨ left_rev, mid_rev, right_rev ⟩ := rev.perfect_split
    let ⟨ h_rev_l , h_rev_r ⟩ := mid_rev
    let bot_hash := match mid_skl with
                          | .Left => h_rev_l
                          | .Right => h_rev_r
    --
    let da_right := { data  := right_skl
                    , mtree := ⟨ op_side mid_skl h_rev_l h_rev_r, da.mtree.2⟩}
    elem_in_reveler_winning_condition_backward da_right right_rev
  := sorry
----------------------------------------

-- theorem linear_to_log_winning_proposer {ℍ : Type}
--     [BEq ℍ][LawfulBEq ℍ][mag : HashMagma ℍ]
--     -- DA
--     {lgn : Nat}
--     (da : ElemInTreeH (2^lgn.succ - 1 - 1) ℍ) -- total path of 2^lgn.succ - 1
--     -- Reveler
--     (lin_reveler : Sequence (2^lgn.succ - 1 - 1) (PMoves ℍ))
--     (win_lin : elem_in_reveler_winning_condition_backward da lin_reveler)
--     : reveler_winning_condition
--         leaf_condition_transformation
--         mid_condition_transformation
--         -- DA is just a tree generate of height lgn and
--         -- boundaries [da.data.1, da.mtree]
--         (gen_tree lgn da.mtree.1 da.mtree.2)
--         --
--         ((tree_da_generator (complete_tree_proposer da lin_reveler)).map .some .some)
--     := by
--     revert lgn
--     intro lgn
--     induction lgn with
--     | zero =>
--       intros da lin_rev HElem
--       simp [complete_tree_proposer,perfectSeq,logarithmic_proposer_hashes, tree_da_generator]
--       simp [tree_distance]
--       simp [node_hashes_backward]
--       simp [gen_tree]
--       simp [gen_empty_perfect_tree,reveler_winning_condition]
--       simp [leaf_condition_transformation]
--       simp [condWProp, sequence_reverse]
--       unfold elem_in_reveler_winning_condition_backward at HElem
--       simp [SingleLastStepH,condWProp] at HElem
--       constructor
--       rw [HElem]
--       simp [Fin.snoc]
--       assumption
--     | succ plgn HInd =>
--       intros da lin_rev HElem
--       have prop_perfect := concat_perfect_split (@sequence_coerce _ _ (2^plgn.succ.succ - 1) (by simp; sorry) (node_hashes_backward da.mtree.1 da.data lin_rev))
--       have compl_decomp := complete_tree_decomp da lin_rev
--       simp at compl_decomp; rw [compl_decomp]
--       simp [tree_da_generator, tree_distance]
--       simp [da_generator]
--       simp [gen_tree, gen_empty_perfect_tree, reveler_winning_condition]
--       simp [ABTree.getI', mid_condition_transformation]
--       -- simp [condWProp]
--       apply And.intro
--       · apply And.intro
--         · have elem_0 := last_hash_node_hashes da lin_rev HElem
--           have bot_hash := get_bot_from_sequence (logarithmic_proposer_hashes da lin_rev)
--           sorry
--         · sorry
--       · sorry
