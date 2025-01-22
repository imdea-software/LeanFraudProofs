import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.Base.GenericTree -- Generic Game trees
import FraudProof.Games.Base.ElemInTree -- Linear basic game definition

import FraudProof.DataStructures.Sequence
import FraudProof.Games.Base.RangeDAConditions

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
def leaf_condition_length_one {ℍ : Type}[BEq ℍ][HashMagma ℍ]
  : SkElem -> ℍ -> Range ℍ -> Winner
  := (fun side prop ⟨ src , dst ⟩
  => condWProp $ op_side side src prop == dst)

-- Leaf Triangle approach
-- When checking the triangle
--     h_mid
--   /      \
--   a       b.
--   We need two sides and hashes.
--   + h_mid = op_side side1 a h1
--   + b = op_sid side2 hmid h2
def leaf_triangle {ℍ : Type}[BEq ℍ][HashMagma ℍ]
  : (SkElem × SkElem) -> (ℍ × ℍ) -> Range ℍ -> Winner
  := (fun sides hashes ⟨ src , dst ⟩
  => have h_mid := op_side sides.1 src hashes.1
    condWProp $ op_side sides.2 h_mid hashes.2 == dst
    )

def mid_condition_da_checking {ℍ : Type}[BEq ℍ]
  -- Arena conditions
  : Unit -> Unit
  -> Range ℍ -> Range ℍ -> Range ℍ
  -> Winner
  := (fun _ _
        hres hl hr =>
        let ⟨ parent_from , parent_to⟩ := hres
        let ⟨ left_from , left_to⟩ := hl
        let ⟨ right_from , right_to⟩ := hr
          -- Mid condition is the expected one
        condWProp $
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
                       (Option (Unit × Range ℍ × Range ℍ)))
    (chooser : ABTree Unit
                      ((Range ℍ × Unit × Range ℍ × Range ℍ)
                      -> Option ChooserMoves))
    --
    :=
    treeCompArbGame
      leaf_condition_length_one
      mid_condition_da_checking
      da proposer chooser

def tree_computation_triangle {ℍ : Type}[BEq ℍ][m : HashMagma ℍ]
    -- DA provides last two sides.
    (da : CompTree (SkElem × SkElem) Unit (Range ℍ))
    --
    (proposer : ABTree (Option (ℍ × ℍ))
                       (Option (Unit × Range ℍ × Range ℍ)))
    (chooser : ABTree Unit
                      ((Range ℍ × Unit × Range ℍ × Range ℍ)
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
      | .zero => .leaf ⟨ seq ⟨ 0 , by simp ⟩ , seq ⟨ 1 , by simp ⟩ , seq ⟨ 2 , by simp ⟩ ⟩
      | .succ _plgn =>
        have ⟨left, mid, right ⟩ := seqPerfectSplit seq
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

----------------------------------------
-- Logarithmic Search Definitions
-- It should be vector, but I wanna keep the other.

-- def iskehash {ℍ : Type} {n : Nat}
--   (side_skeleton : ISkeleton n)
--   (rev : Sequence n (Option (PMoves ℍ)))
--   : Sequence n (Option (Sum ℍ ℍ))
--   := seq_zip_with
--      (fun sk opt_moves =>
--      match sk with
--      | .inl _ => opt_moves.map ( .inl ∘ fun x => match x with | .Next p => p.1)
--      | .inr _ => opt_moves.map ( .inr ∘ fun x => match x with | .Next p => p.2)
--      )
--      side_skeleton rev

-- abbrev Side (ℍ : Type) := Sum ℍ ℍ
-- def build_log_proposer {ℍ : Type}{lgn : Nat}
--   (rev : Sequence (2^lgn.succ - 1) (Option (Side ℍ)))
--   : ABTree (Option (Side ℍ)) (Option (Side ℍ))
--   := perfectSeq rev

-- def from_side {α : Type} (sa : Side α) : α :=
--   match sa with
--   | .inl a => a
--   | .inr a => a

-- Macro to make everything shorter.
-- @[simp]
-- def Range (α : Type) := α × α

--------------------------------------------------------------------------------
-- * Range plus length
-- Here I follow a dfferente approach, but I think it is problematic.
-- We do not only have ranges but also the length of the path.
-- The thing is that the computation-tree-scheme should be enough.
-- We are constantly checking that numbers match-up. Length-0 when we reach
-- leaves and add-up conditions at mid steps.
-- Why did I add it in the first place? Because now I can add conditional checks
-- to mid steps. In a way, I have more context to work on than just ranges. I
-- know where in the path we are.
----------------------------------------
-- * Da Definition
-- Path definition
structure DA_Statement (ℍ : Type) where
  -- From
  src : ℍ
  -- To
  dst : ℍ
  -- Path length
  len : Nat

--
@[simp]
def Tree_Reveler (ℍ : Type)
  := ABTree (Option ℍ) (Option (Unit × DA_Statement ℍ × DA_Statement ℍ))

@[simp]
def Tree_Reveler.top {ℍ : Type} : Tree_Reveler ℍ -> Option ℍ
  | .leaf oh => oh
  | .node (.some ⟨ _, ⟨ _, hmid , _⟩ , _ ⟩ ) _ _ => .some hmid
  | _ => .none
-- Good DAs also have some stuff like
-- da.len = 0 => da.src = da.dst
-- They form a metric space, topology and stuff

@[simp]
def Tree_DA (ℍ : Type) :=
  CompTree
    -- No info at leave s
    Unit
    -- No info, but we can add something like (nat, nat) noting length on each
    -- child
    Unit
    (DA_Statement ℍ) -- [a, b] and length ...

def leaf_condition_transformation {ℍ : Type}[BEq ℍ]
  : Unit -> ℍ -> DA_Statement ℍ-> Winner
  := (fun _ prop ⟨ src , dst , len ⟩
    -- Unitary range and proposed same hash
    -- This is the end of the game. If nothing happened before.
     => condWProp $ all_true
     -- Unitary range [prop,prop] of length 0
     [ len == 0
     , prop == src
     , src == dst
     ]
     )

def mid_condition_transformation{ℍ : Type}[BEq ℍ][mag : HashMagma ℍ]
  -- Arena conditions
  : Unit -> Unit
  -> DA_Statement ℍ -> DA_Statement ℍ -> DA_Statement ℍ
  -> Winner
  := (fun _ _
        hres hl hr =>
        let ⟨ parent_from , parent_to, len ⟩ := hres
        let ⟨ left_from , left_to, left_len ⟩ := hl
        let ⟨ right_from , right_to, right_len ⟩ := hr
          -- Mid condition is the expected one
        condWProp $
          all_true
          -- Path consistency
          [ parent_from == left_from
          , parent_to == right_to
          , left_to == right_from
          , left_len + right_len == len
          , left_len > 0
          , right_len > 0
          -- Last condition (before leaf)
          , (not (len == 2))
            || (mag.comb parent_from parent_to == left_to)
          ]
      )

def element_in_tree_transform {ℍ : Type}[BEq ℍ][m : HashMagma ℍ]
    --
    -- Da is a computation arena plus a range
    -- Given |[hl, hr]| you play the arena to prove that there is a path
    -- from |h_l| to |h_r| of length |len| (DA_Statement)
    (da : CompTree Unit Unit (DA_Statement ℍ))
    --
    (proposer : ABTree (Option ℍ)
                       (Option (Unit × (DA_Statement ℍ) × (DA_Statement ℍ))))
    (chooser : ABTree Unit
                      (DA_Statement ℍ × Unit × (DA_Statement ℍ) × (DA_Statement ℍ)
                      -> Option ChooserMoves))
    --
    :=
    treeCompArbGame
      leaf_condition_transformation
      mid_condition_transformation
      da proposer chooser

-- @[simp]
-- def total_range_tree {ℍ : Type}
--   : (ABTree ℍ (Range ℍ × Range ℍ)) -> Range ℍ
--   | .leaf h => ⟨ h , h ⟩
--   | .node ⟨ left_range , right_range ⟩ _ _ => ⟨ left_range.1, right_range.2 ⟩

-- @[simp]
-- def get_total_range_tree {ℍ : Type}
--   (tree : ABTree (Option ℍ) (Option (Unit × (Range ℍ) × (Range ℍ))))
--   : Option (Range ℍ)
--   := match tree with
--   | .leaf (.some h) => .some ⟨ h , h ⟩
--   | .node (.some ⟨_, left_range , right_range ⟩) _ _ =>
--     .some $ ⟨ left_range.1 , right_range.2 ⟩
--   | _ => .none

-- Proposer transformatino
-- def logarithmic_proposer {ℍ : Type}{mag : HashMagma ℍ}{lgn : Nat}
--   (sides : ISkeleton (2^lgn.succ - 1))
--   (proposer : Sequence (2^lgn.succ - 1) (Option (PMoves ℍ)))
--   : ABTree (Option ℍ) (Option (Unit × (Range ℍ) × (Range ℍ)))
--   := match lgn with
--      | .zero =>
--        .leaf $
--          (headSeq proposer).map
--             (fun (.Next ⟨hl , hr⟩)
--               => -- We return the sibiling hash!
--                 match headSeq sides with
--                  | .inl _ => hr
--                  | .inr _ => hl
--               -- h_extra -- @op_side ℍ mag (headSeq sides) h_bot h_extra
--               )
--             -- TODO add Unit range -> true
--             -- let h_top := @op_side ℍ mag (headSeq sides) h_bot h_extra
--             -- .node (.some ⟨ (), ⟨ h_bot , h_bot⟩ , ⟨ h_top , h_top ⟩ ⟩)
--             --       -- Leafs are winning positions for the proposer.
--             --       (.leaf $ .some h_bot)
--             --       (.leaf $ .some h_top)
--      | .succ _pn =>
--        -- Sides path info
--        let ⟨ sides_left, sides_mid , sides_right ⟩ := seqPerfectSplit sides
--        -- Reveler data
--        let ⟨ prop_left, prop_mid, prop_right ⟩ := seqPerfectSplit proposer
--        let left_tree := @logarithmic_proposer _ mag _ sides_left prop_left
--        let right_tree := @logarithmic_proposer _ mag _ sides_right prop_right
--        match prop_mid
--              , get_total_range_tree left_tree
--              , get_total_range_tree right_tree
--        with
--        | .some (.Next p) , .some left_range, .some right_range =>
--          -- This is the mid condition that hashes meet here.
--          -- TODO Warning here
--          let h_mid := op_side sides_mid p.1 p.2
--          -- let h_mid := mag.comb p.1 p.2 -- I am not so sure about op_side
--          -- END TODO Warning here
--          -- But I need to get bounds from recursive calls.
--          let h_bot : ℍ := left_range.1
--          let h_top : ℍ := right_range.2
--          .node (.some ⟨(), ⟨ h_bot , h_mid ⟩, ⟨ h_mid , h_top ⟩⟩)
--                left_tree right_tree
--        | _ ,_ ,_ => .node .none left_tree right_tree
----------------------------------------


-- Thm Winning proposer to winning proposer.
-- We have revealer/proposer winning conditions. I think we can prove through
-- that.
--
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
  := { data := concatSeq da_l.data da_r.data
     , mtree := ⟨ da_l.mtree.1 , da_r.mtree.2⟩
     }

def da_split {ℍ : Type}{n : Nat}
  -- Cut
  ( m : Nat ) (mLtn : m ≤ n)
  ( da : ElemInTreeH n ℍ )
  ( mid : ℍ )
  : ElemInTreeH m ℍ × ElemInTreeH (n - m) ℍ
  := have ⟨ left , right ⟩ := splitSeq da.data m mLtn
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
    := Fin.snoc
      (seq_zip_with
        (fun side pm => op_side side pm.left pm.right)
        skl
        proposer)
      bot_hash

def logarithmic_proposer_hashes {ℍ}{lgn : Nat}[HashMagma ℍ]
    (da : ElemInTreeH (2^lgn.succ - 1 - 1) ℍ)
    (proposer : Sequence (2^lgn.succ - 1 - 1) (PMoves ℍ))
    : Sequence (2^lgn.succ - 1) ℍ
    := sequence_coerce (by simp; have pZ := @pow_gt_zero lgn; omega)
    $ sequence_reverse -- We need hash[0] = mtree.1, ... , hash[n] = mtree.2
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
    have ⟨ left, mid, right ⟩ := seqPerfectSplit (logarithmic_proposer_hashes da proposer)
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
        cases HSeqLeft : seqPerfectSplit (logarithmic_proposer_hashes da proposer) with
        | mk left_prop rest =>
          cases HSeqRest : rest with
          | mk mid_prop right_prop =>
            simp [complete_tree_proposer]
            unfold perfectSeq
            simp
            apply And.intro
            · rw [HSeqLeft, HSeqRest]
            · apply And.intro
              · rw [HSeqLeft]; simp [seqPerfectSplit, perfectSeq]
              · rw [HSeqLeft,HSeqRest]; simp [seqPerfectSplit, perfectSeq]

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
  : headSeq' seq_hashes (by simp)
    = get_bot_hash
            (tree_distance
              (perfectSeq seq_hashes))
  := by induction lgn with
        | zero => simp [perfectSeq, tree_distance,get_bot_hash]
                  simp [ABTree.getI']
        | succ pnlgn HInd =>
          simp [perfectSeq, get_bot_hash]
          simp [ABTree.getI']
          have seq_left_ind := HInd (seqPerfectSplit seq_hashes).1
          simp [tree_distance]
          rw [<- seq_left_ind]
          simp [seqPerfectSplit, splitSeq]

lemma get_top_from_sequence {ℍ : Type}{lgn : Nat}
  (seq_hashes : Sequence (2^lgn.succ - 1) ℍ)
  : lastSeq'' seq_hashes (by have pZ := @pow_gt_zero lgn; omega)
    = get_top_hash
            (tree_distance
              (perfectSeq seq_hashes))
  := by sorry -- should be similar to the other one.

def da_generator {ℍ : Type}
  (info : ℍ × Nat × ℍ × Nat × ℍ )
  : DA_Statement ℍ × DA_Statement ℍ
  := ⟨ {src := info.1, dst := info.2.2.1, len := info.2.1}
     , {src := info.2.2.1, dst := info.2.2.2.2, len := info.2.2.2.1} ⟩

def tree_da_generator {ℍ : Type}
  : ABTree ℍ  ℍ
  -> ABTree ℍ (DA_Statement ℍ × DA_Statement ℍ)
  := ABTree.map (fun p => p.1) da_generator
     ∘ tree_distance

----------------------------------------

-- We are defining the same lemmas and theorems as the first implementations.
theorem forall_mid_step {ℍ : Type}
    [BEq ℍ][HashMagma ℍ] {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (PMoves ℍ))
    (winning_cond : elem_in_reveler_winning_condition_backward da proposer)
    :
    forall (i : Nat)(iNZ : 0 < i)(iLtn : i < n),
        SingleMidStep ⟨ node_hashes_backward da.mtree.1 da.data proposer ⟨ i , by omega ⟩
                      , (proposer ⟨ i , iLtn ⟩).destruct
                      ⟩ = Player.Proposer
    := sorry

theorem last_hash_node_hashes {ℍ : Type}
    [BEq ℍ][HashMagma ℍ] {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (PMoves ℍ))
    -- We do not need winning_cond here
    (winning_cond : elem_in_reveler_winning_condition_backward da proposer)
    : da.mtree.1 =  lastSeq (node_hashes_backward da.mtree.1 da.data proposer)
    := sorry

theorem first_hash_node_hashes {ℍ : Type}
    [BEq ℍ][HashMagma ℍ] {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (PMoves ℍ))
    -- Here we need winning_cond that provides
    -- |da.mtree.2| = |op_side side proposer 0.left proposer 0.right|
    (winning_cond : elem_in_reveler_winning_condition_backward da proposer)
    : da.mtree.2 = headSeq (node_hashes_backward da.mtree.1 da.data proposer)
    := sorry

-- This are the winning conditions, I first proposed long time ago.
-- So we already have a logarithmic proposer definition and a winning condition.


theorem winning_reveler_sum {ℍ : Type}
    [BEq ℍ][LawfulBEq ℍ][HashMagma ℍ]
    {n m : Nat}
    -- Revelers
    -- Left
    (da_l : ElemInTreeH n ℍ)(proposer_l : Sequence n (PMoves ℍ))
    (good_left : elem_in_reveler_winning_condition_backward da_l proposer_l)
    -- Right
    (da_r : ElemInTreeH m ℍ)(proposer_r : Sequence m (PMoves ℍ))
    (good_right : elem_in_reveler_winning_condition_backward da_r proposer_r)
    -- Such that share a meeting point
    (eq_mid : da_l.mtree.2 = da_r.mtree.1)
    : elem_in_reveler_winning_condition_backward
          (da_sum da_l da_r)
          (concatSeq proposer_l proposer_r)
    := by sorry
-- This one should be easy if we move to the forall realm. We did this already.

-- -- We can split das, but we need a ℍ to split it.
-- def split_da {ℍ}{n : Nat}
--     (da : ElemInTreeH n ℍ)
--     (cut_h : ℍ)
--     (m : Nat)( mLtn : m ≤ n) -- 0 < n
--     : (ElemInTreeH m ℍ × ElemInTreeH (n - m) ℍ)
--     := let ⟨ left_skl , right_skl ⟩ := splitSeq da.data.2 m mLtn
--       ⟨ {data := ⟨ da.data.1 , left_skl⟩ , mtree := cut_h}
--       , {data := ⟨ cut_h , right_skl⟩ , mtree := da.mtree} ⟩

-- General cuttings
theorem split_da_concatSeq_left {ℍ}[BEq ℍ][HashMagma ℍ]{n : Nat}
  (da : ElemInTreeH n ℍ)
  (rev : Sequence n (PMoves ℍ))
  --
  (lin_rev : elem_in_reveler_winning_condition_backward da rev)
  --
  (cut : Nat)(cutLtn : cut ≤ n)
  : let .Next p := (rev ⟨ cut , by sorry ⟩)
    let ⟨ da_left, _ ⟩ :=
      da_split cut cutLtn da
        (match da.data ⟨ cut , by sorry ⟩ with
         | .inl _ => p.1
         | .inr _ => p.2)
    elem_in_reveler_winning_condition_backward da_left (splitSeq rev cut (by omega)).1
  := sorry

-- Perfect Splitting DAs  + Reveler + Winning conditions
theorem split_da_perfect_left {ℍ}[BEq ℍ][HashMagma ℍ]{lgn : Nat}
  (da : ElemInTreeH (2^lgn.succ - 1) ℍ)
  (rev : Sequence (2^lgn.succ - 1) (PMoves ℍ))
  -- Good rev
  (lin_rev : elem_in_reveler_winning_condition_backward da rev)
  : let ⟨ left_skl, mid_skl, right_skl ⟩ := seqPerfectSplit da.data
    let ⟨ left_rev, mid_rev, right_rev ⟩ := seqPerfectSplit rev
    let ⟨ h_rev_l , h_rev_r ⟩ := mid_rev.destruct
    let top_hash := match mid_skl with
                          | .inl _ => h_rev_l
                          | .inr _ => h_rev_r
    let da_left := {data := left_skl , mtree := ⟨ da.mtree.1 ,top_hash ⟩}
    elem_in_reveler_winning_condition_backward da_left left_rev
  := sorry

theorem split_da_perfect_right {ℍ}[BEq ℍ][HashMagma ℍ]{lgn : Nat}
  (da : ElemInTreeH (2^lgn.succ - 1) ℍ)
  (rev : Sequence (2^lgn.succ - 1) (PMoves ℍ))
  -- Good rev
  (lin_rev : elem_in_reveler_winning_condition_backward da rev)
  : let ⟨ left_skl, mid_skl, right_skl ⟩ := seqPerfectSplit da.data
    let ⟨ left_rev, mid_rev, right_rev ⟩ := seqPerfectSplit rev
    let ⟨ h_rev_l , h_rev_r ⟩ := mid_rev.destruct
    let bot_hash := match mid_skl with
                          | .inl _ => h_rev_l
                          | .inr _ => h_rev_r
    --
    let da_right := { data  := right_skl
                    , mtree := ⟨ op_side mid_skl h_rev_l h_rev_r, da.mtree.2⟩}
    elem_in_reveler_winning_condition_backward da_right right_rev
  := sorry
----------------------------------------

@[simp]
def log_winning_game {ℍ : Type}
    [BEq ℍ][HashMagma ℍ]
    (da : Tree_DA ℍ)
    -- Players
    (reveler : Tree_Reveler ℍ)
    : Prop
    := reveler_winning_condition
        leaf_condition_transformation
        mid_condition_transformation
        da reveler

def gen_tree {ℍ : Type}(height : Nat)(l r : ℍ)
  : Tree_DA ℍ
  := { data := gen_empty_perfect_tree height
     , res := ⟨ l, r , (2^height.succ - 1 - 1) ⟩ }

-- def da_to_tree {ℍ : Type}{lgn : Nat}
--     (da : ElemInTreeH (2^lgn.succ - 1) ℍ)
--     : Tree_DA ℍ
--     := { data := perfectSeq $ seqMap (fun _ => ()) da.data.2
--        , res  := ⟨ da.data.1 , da.mtree ⟩}

-- def tree_composition {ℍ : Type}
--     [BEq ℍ][LawfulBEq ℍ][mag : HashMagma ℍ]
--     --
--     (left_da  : Tree_DA ℍ)
--     (left_rev : Tree_Reveler ℍ)
--     --
--     (right_da  : Tree_DA ℍ)
--     (right_rev : Tree_Reveler ℍ)
--     -- Stuff
--     : Tree_DA ℍ × Tree_Reveler ℍ :=
--     let h_mid := mag.comb <$> left_rev.top <*> right_rev.top
--     ⟨{ data := .node () left_da.data right_da.data
--       , res := ⟨ left_da.res.1 , right_da.res.2⟩} -- [a , b]
--     , .node ( h_mid.map (fun h => ⟨ ()
--                                   , ⟨left_da.res.1 , h⟩ -- [a, mid]
--                                   , ⟨h , right_da.res.2⟩ ⟩)) -- [mid , b]
--             left_rev right_rev ⟩

-- theorem tree_composition_winning {ℍ : Type}
      -- log_winning_game
      --    {data := .node _ _ _
      --    , res := ⟨ left_da.data.1 , right_da.mtree ⟩}
      --    (.node (.some ( ⟨ () , ⟨left_da.data.1 , h_mid⟩ , ⟨ h_mid ,right_da.mtree ⟩ ⟩))
      --                  (@logarithmic_proposer _ mag _ left_da.data.2
      --                                                  (seqMap .some left_rev))
      --                  (@logarithmic_proposer _ mag _ right_da.data.2
      --                                     (seqMap .some right_rev))
      --    )


theorem linear_to_log_winning_proposer {ℍ : Type}
    [BEq ℍ][LawfulBEq ℍ][mag : HashMagma ℍ]
    -- DA
    {lgn : Nat}
    (da : ElemInTreeH (2^lgn.succ - 1 - 1) ℍ) -- total path of 2^lgn.succ - 1
    -- Reveler
    (lin_reveler : Sequence (2^lgn.succ - 1 - 1) (PMoves ℍ))
    (win_lin : elem_in_reveler_winning_condition_backward da lin_reveler)
    : reveler_winning_condition
        leaf_condition_transformation
        mid_condition_transformation
        -- DA is just a tree generate of height lgn and
        -- boundaries [da.data.1, da.mtree]
        (gen_tree lgn da.mtree.1 da.mtree.2)
        --
        ((tree_da_generator (complete_tree_proposer da lin_reveler)).map .some (fun p => .some ⟨ (), p⟩))
    := by
    revert lgn
    intro lgn
    induction lgn with
    | zero =>
      intros da lin_rev HElem
      simp [complete_tree_proposer,perfectSeq,logarithmic_proposer_hashes, tree_da_generator]
      simp [tree_distance]
      simp [node_hashes_backward]
      simp [gen_tree]
      simp [gen_empty_perfect_tree,reveler_winning_condition]
      simp [leaf_condition_transformation]
      simp [condWProp]
      unfold elem_in_reveler_winning_condition_backward at HElem
      simp [SingleLastStepH,condWProp] at HElem
      constructor
      rw [HElem]
      simp [Fin.snoc]
      assumption
    | succ plgn HInd =>
      intros da lin_rev HElem
      have prop_perfect := concat_perfect_split (@sequence_coerce _ _ (2^plgn.succ.succ - 1) (by simp; sorry) (node_hashes_backward da.mtree.1 da.data lin_rev))
      have compl_decomp := complete_tree_decomp da lin_rev
      simp at compl_decomp; rw [compl_decomp]
      simp [tree_da_generator, tree_distance]
      simp [da_generator]
      simp [gen_tree, gen_empty_perfect_tree, reveler_winning_condition]
      simp [ABTree.getI', mid_condition_transformation]
      simp [condWProp]
      apply And.intro
      · apply And.intro
        · have elem_0 := last_hash_node_hashes da lin_rev HElem
          have bot_hash := get_bot_from_sequence (logarithmic_proposer_hashes da lin_rev)
          sorry
        · sorry
      · sorry
