import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.Base.GenericTree -- Generic Game trees

import FraudProof.DataStructures.Sequence

import Mathlib.Data.Fin.Tuple.Basic

-- DA: element is in Tree
structure ElemInMTree (α ℍ : Type) where
  elem : α
  path : Skeleton
  mtree : ℍ
  -- Prop: foldl hash_Path (hash elem) path = mtree

-- Here we do not need to know the whole tree.
-- maybe we need to define some notion of DA promotion.
-- Whatever game we define over Skeletons we can play over trees?

def arbElem {α ℍ : Type}
    (pos : Skeleton)
    [BEq ℍ]
    [o : Hash α ℍ][m : HashMagma ℍ]
    --
    (da : ElemInMTree α ℍ)
    --
    (proposer : Skeleton -> Option (PMoves ℍ))
    (chooser : Skeleton -> PMoves ℍ -> Option ChooserSmp)
    : Winner
    := match _HC : da.path with
       | .nil => condWProp $ o.mhash da.elem == da.mtree
       | .cons sibside rest =>
         match proposer pos with
         | none => Player.Chooser
         | some proposed =>
          match chooser pos proposed with
            | none => Player.Proposer
            | some .Now => condWProp $ hProposed proposed == da.mtree
            | some (.Continue _) =>
                let nextHash := match sibside with
                                | .inl _ => proposed.left
                                | .inr _ => proposed.left
                arbElem (pos ++ [sibside]) ⟨ da.elem , rest, nextHash⟩
                        proposer chooser
    termination_by da.path
    decreasing_by {simp_wf; rw [_HC]; simp}

def arbElemInit {α ℍ : Type} [BEq ℍ] [Hash α ℍ][HashMagma ℍ]
    -- DA
    (da : ElemInMTree α ℍ)
    -- Players
    (proposer : Skeleton -> Option (PMoves ℍ))
    (chooser : Skeleton -> PMoves ℍ -> Option ChooserSmp)
    : Winner
    := arbElem .nil da proposer chooser

-- There is a path of length |n| from the root |mtree| to |elem|
structure ElemInTreeN (n : Nat)(α ℍ : Type) where
  data : α × ISkeleton n
  mtree : ℍ
  -- Let |bt : BTree α| be the implicit data, such that |hash bt = mtree|.
  -- This da says |bt ! data.2| leads to |data.1|

theorem ElemInTreeN0 {α ℍ : Type} (da : ElemInTreeN 0 α ℍ)
 : da.data.2 = nilSeq
 := by have ⟨ ⟨ a , sk ⟩ , mtree ⟩ := da
       simp
       apply funext
       intro empty
       simp [nilSeq]
       have ⟨ n , e ⟩ := empty
       simp at e

structure ElemInTreeH (n : Nat)(ℍ : Type) where
  data : ℍ × ISkeleton n
  mtree : ℍ
  -- Same as above but only using hashes
  -- |dt ! data.2| leads to | data.1| where |data.1| is the hash of the element
  -- in a tree [see the above DA].

def SingleLastStep {α ℍ : Type}[BEq ℍ][h : Hash α ℍ] (data : ElemInTreeN 0 α ℍ) : Winner
  := condWProp $ h.mhash (data.data.1) == data.mtree

def SingleMidStep {ℍ : Type}[BEq ℍ][m : HashMagma ℍ ](data : ℍ × ℍ × ℍ) : Winner
  := condWProp $ m.comb data.2.1 data.2.2 == data.1

def elemInHGame {α ℍ : Type}
    [BEq ℍ][Hash α ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeN n α ℍ)
    (proposer : Sequence n (Option (PMoves ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : Winner
    := match n with
       | 0 => SingleLastStep da
       | .succ _pn =>
         match headSeq proposer with
         | .none => Player.Chooser -- Proposer forfeits the game
         | .some (.Next proposed) =>
           match headSeq chooser ⟨ da.mtree , proposed ⟩ with
           | .none => Player.Proposer -- Chooser forfeits the game
           | .some .Now => SingleMidStep ⟨ da.mtree , proposed ⟩
           | .some (.Continue _) =>
             have nextHash := match headSeq da.data.2 with
                    | .inl _ => proposed.1
                    | .inr _ => proposed.2
             elemInHGame
               -- Next step DA
               ⟨⟨ da.data.1, tailSeq da.data.2⟩ , nextHash ⟩
               -- Next step players
               (tailSeq proposer)
               (tailSeq chooser)

-- Here we can have some troubles. We do not know if we really are talking about
-- the same element.
def SingleLastStepH {ℍ : Type}[BEq ℍ] (data : ElemInTreeH 0 ℍ) : Winner
  := condWProp $ data.data.1 == data.mtree

def elemInHGameH {ℍ : Type}
    [BEq ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (Option (PMoves ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : Winner
    := match n with
       | 0 => SingleLastStepH da
       | .succ _pn =>
         match headSeq proposer with
         | .none => Player.Chooser -- Proposer forfeits the game
         | .some (.Next proposed) =>
           match headSeq chooser ⟨ da.mtree , proposed ⟩ with
           | .none => Player.Proposer -- Chooser forfeits the game
           | .some .Now => SingleMidStep ⟨ da.mtree , proposed ⟩
           | .some (.Continue _) =>
             have nextHash := match headSeq da.data.2 with
                    | .inl _ => proposed.1
                    | .inr _ => proposed.2
             elemInHGameH
               -- Next step DA
               ⟨⟨ da.data.1, tailSeq da.data.2⟩ , nextHash ⟩
               -- Next step players
               (tailSeq proposer)
               (tailSeq chooser)

--------------------------------------------------------------------------------
-- Transformation from a Sequence to the /same/ game played over Trees arenas.
--------------------------------------------------------------------------------

-- Building a Tree out of skelentons.
-- This function keeps size.
-- ABTree.size is height
def skeleton_to_tree {n : Nat} (sk : ISkeleton n) : ABTree Unit Unit
 := match n with
   | .zero => .leaf ()
   | .succ _pn => match headSeq sk with
                 | .inl _ =>
                        .node () (skeleton_to_tree (Fin.tail sk)) (.leaf ())
                 | .inr _ =>
                        .node ()  (.leaf ()) (skeleton_to_tree (Fin.tail sk))

@[simp]
def skl_to_maybe_elem {α : Type} {n : Nat}
  (a : α) (sk : ISkeleton n) : ABTree (Option α) Unit
    := match n with
    | .zero => .leaf a
    | .succ _pn => match headSeq sk with
                    | .inl _ =>
                            .node () (skl_to_maybe_elem a (Fin.tail sk)) (.leaf none)
                    | .inr _ =>
                            .node () (.leaf none) (skl_to_maybe_elem a (Fin.tail sk))

@[simp]
def build_proposer {ℍ : Type}{n : Nat}
  (data : ℍ × ISkeleton n) (rev : Sequence n (Option (PMoves ℍ)))
  : ABTree (Option ℍ) (Option (Unit × ℍ × ℍ))
  := match n with
  | .zero => .leaf <| .some data.1
  | .succ _pn => let rest_tree := build_proposer ⟨ data.1 , Fin.tail data.2⟩ (Fin.tail rev)
     match headSeq rev with
       | .none => .node .none rest_tree (.leaf .none)
       | .some (.Next ⟨ hl , hr⟩)=>
         match headSeq data.2 with
         | .inl _ =>
           .node (.some ⟨ (), hl, hr ⟩)
                 rest_tree
                 (.leaf (.some hr))
         | .inr _ =>
           .node (.some ⟨ (), hl, hr ⟩)
                 (.leaf (.some hl))
                 rest_tree
@[simp]
def build_chooser {ℍ : Type}{n : Nat}
  (data : ℍ × ISkeleton n)
  (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
  : ABTree Unit (ℍ × Unit × ℍ × ℍ -> Option ChooserMoves)
  := match n with
    | .zero => .leaf ()
    | .succ _pn =>
      let side_choose (s : Chooser.Side) (arg : ℍ × Unit × ℍ × ℍ) : Option ChooserMoves :=
          have ⟨ ht , _ , hl , hr ⟩ := arg
          (headSeq chooser ⟨ ht, hl , hr ⟩).map
            (fun ch => match ch with
                       | .Now => .Now
                       | .Continue _ => .Continue s)
      match headSeq data.2 with
      | .inl _ =>
        .node
          (side_choose .Left)
          (build_chooser ⟨data.1 , Fin.tail data.2⟩ (Fin.tail chooser))
          (.leaf ())
      | .inr _ =>
        .node
          (side_choose .Right)
          (.leaf ())
          (build_chooser ⟨data.1 , Fin.tail data.2⟩ (Fin.tail chooser))

def elem_in_tree_gen_tree {ℍ : Type}
    [BEq ℍ][mag : HashMagma ℍ]
    -- DA
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    --
    (proposer : Sequence n (Option (PMoves ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    --
    : Winner
    :=
    let da_tree : CompTree (Option ℍ) Unit ℍ := {data := skl_to_maybe_elem da.data.1 da.data.2 , res := da.mtree}
    let tree_revealer : ABTree (Option ℍ) (Option (Unit × ℍ × ℍ))
      := build_proposer da.data proposer
    let tree_chooser : ABTree Unit (ℍ × Unit × ℍ × ℍ -> Option ChooserMoves)
      := build_chooser da.data chooser
    treeCompArbGame
      (fun opth _h1 h2 =>
        match opth with
        | .none => -- this case is a bit artificial
        -- chooser should challenge previous step.
          Player.Proposer
        | .some hp => condWProp <| (hp == h2)
      )
      (fun _ _ hres pl pr =>
        -- _nodeh and hres should be the same.
           condWProp <| mag.comb pl pr == hres)
      da_tree tree_revealer tree_chooser

----------------------------------------
-- Are both games equivs?
--
--Two games (in this case) are equivalente if they have the same outcome to the
--same players.

theorem seq_equiv_tree {ℍ : Type}[BEq ℍ][HashMagma ℍ]
  -- DA
  {n : Nat}(da : ElemInTreeH n ℍ)
  -- Players
  (proposer : Sequence n (Option (PMoves ℍ)))
  (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
  : elemInHGameH da proposer chooser = elem_in_tree_gen_tree da proposer chooser
  := by revert n
        intro n
        induction n with
        | zero =>
          intros da prop cho
          simp [elemInHGameH , elem_in_tree_gen_tree, SingleLastStepH, treeCompArbGame]
        | succ pn HInd =>
          intros da prop cho
          simp [elemInHGameH, elem_in_tree_gen_tree ]
          cases prop 0 with
          | none =>
            simp [treeCompArbGame]
          | some proposed =>
            cases proposed with
            | End v => contradiction
            | Next e =>
              simp
              match HCho : cho 0 (da.mtree, e) with
              | none =>
                simp [treeCompArbGame]
                match da.data.2 0 with
                | .inl _ => simp [treeCompArbGame]; rw [HCho]; simp
                | .inr _ => simp [treeCompArbGame]; rw [HCho]; simp
              | some choosed =>
                match choosed with
                | .Now =>
                  simp [SingleMidStep]
                  cases da.data.2 0 with
                    | inl _ => simp [treeCompArbGame]; rw [HCho]; simp
                    | inr _ => simp [treeCompArbGame]; rw [HCho]; simp
                | .Continue _ =>
                  simp
                  cases da.data.2 0 with
                    | inl _ =>
                      simp [treeCompArbGame]
                      rw [HCho]; simp
                      apply HInd
                    | inr _ =>
                      simp [treeCompArbGame]
                      rw [HCho]; simp
                      apply HInd
----------------------------------------

----------------------------------------
-- Logarithmic Search

-- It should be vector, but I wanna keep the other.

def iskehash {ℍ : Type} {n : Nat}
  (side_skeleton : ISkeleton n)
  (rev : Sequence n (Option (PMoves ℍ)))
  : Sequence n (Option (Sum ℍ ℍ))
  := seq_zip_with
     (fun sk opt_moves =>
     match sk with
     | .inl _ => opt_moves.map ( .inl ∘ fun x => match x with | .Next p => p.1)
     | .inr _ => opt_moves.map ( .inr ∘ fun x => match x with | .Next p => p.2)
     )
     side_skeleton rev

abbrev Side (ℍ : Type) := Sum ℍ ℍ
def build_log_proposer {ℍ : Type}{lgn : Nat}
  (rev : Sequence (2^lgn.succ - 1) (Option (Side ℍ)))
  : ABTree (Option (Side ℍ)) (Option (Side ℍ))
  := perfectSeq  rev

def from_side {α : Type} (sa : Side α) : α :=
  match sa with
  | .inl a => a
  | .inr a => a

-- Same as opHash??
-- I use SkElem to signal where the path is going.
def op_side {α : Type}[mag : HashMagma α] (o : SkElem) (a b : α) : α
 := match o with
   | .inl _ => mag.comb a b
   | .inr _ => mag.comb b a

abbrev Range (α : Type) := α × α

@[simp]
def all_true (ls : List Bool) : Bool := ls.all id

def element_in_tree_transform {ℍ : Type}[BEq ℍ][m : HashMagma ℍ]
    --
    {lgn : Nat}(da : ElemInTreeH (2^lgn.succ - 1) ℍ)
    --
    (proposer : ABTree (Option ℍ) (Option (Unit × (Range ℍ) × (Range ℍ))))
    (chooser : ABTree Unit (Range ℍ × Unit × (Range ℍ) × (Range ℍ) -> Option ChooserMoves))
    --
    :=
    -- + |data| is a balance sequence of hashing data from one hash to another
    -- hash.
    -- + |res| are the extremes of the chain mentioned above.
    let balanced_da : CompTree SkElem SkElem (Range ℍ)
        := { data := perfectSeq da.data.2
           , res  := ⟨ da.data.1 , da.mtree ⟩}
    treeCompArbGame
      -- Leaf condition. In this case, if proposer reaches leaf, it wins.
      (fun side top ⟨ hl, hr ⟩ => condWProp $ op_side side hl hr == top)
      -- Mid condtion is where the fun is.
      (fun (_side : SkElem) (_t : Unit)
           hres hl hr =>
        let ⟨ h_bot , h_top ⟩ := hres
        let ⟨ h_botP , h_midP ⟩ := hl
        let ⟨ h_midP' , h_topP ⟩ := hr
        -- Mid condition is the expected one
        condWProp $
        -- Unit range, wins proposer
        -- or (h_bot == h_top) $
        --
        all_true
        -- Range consistency
        [ h_bot == h_botP
        , h_top == h_topP
        , h_midP == h_midP'
        -- If trigger at the rigth moment and using |side|, we should be able to
        -- compute hashes.
        -- This condition makes sense when |mid| hash is the one proposed as
        -- intermediary.
        -- , op_side side h_bot h_midP == h_top (No intermediary condition here.)
        -- I am not super sure about this condition. I need to check it.
        ]
      )
      balanced_da
      proposer chooser

def get_total_range_tree {ℍ : Type}
  (tree : ABTree (Option ℍ) (Option (Unit × (Range ℍ) × (Range ℍ))))
  : Option (Range ℍ)
  := match tree with
  | .leaf (.some h) => .some ⟨ h , h ⟩
  | .node (.some ⟨_, left_range , right_range ⟩) _ _ =>
    .some $ ⟨ left_range.1 , right_range.2 ⟩
  | _ => .none

-- Proposer transformatino
def logarithmic_proposer {ℍ : Type}{mag : HashMagma ℍ}{lgn : Nat}
  (sides : ISkeleton (2^lgn.succ - 1))
  (proposer : Sequence (2^lgn.succ - 1) (Option (PMoves ℍ)))
  : ABTree (Option ℍ) (Option (Unit × (Range ℍ) × (Range ℍ)))
  := match lgn with
     | .zero =>
       .leaf $
         (headSeq proposer).map
            (fun (.Next ⟨h_bot, h_extra⟩)
              => @op_side ℍ mag (headSeq sides) h_bot h_extra)
            -- TODO add Unit range -> true
            -- let h_top := @op_side ℍ mag (headSeq sides) h_bot h_extra
            -- .node (.some ⟨ (), ⟨ h_bot , h_bot⟩ , ⟨ h_top , h_top ⟩ ⟩)
            --       -- Leafs are winning positions for the proposer.
            --       (.leaf $ .some h_bot)
            --       (.leaf $ .some h_top)
     | .succ _pn =>
       let ⟨ sides_left, sides_mid , sides_right ⟩ := seqPerfectSplit sides
       let ⟨ prop_left, prop_mid, prop_right ⟩ := seqPerfectSplit proposer
       let left_tree := @logarithmic_proposer _ mag _ sides_left prop_left
       let right_tree := @logarithmic_proposer _ mag _ sides_right prop_right
       match prop_mid
             , get_total_range_tree left_tree
             , get_total_range_tree right_tree
       with
       | .some (.Next p) , .some left_range, .some right_range =>
         -- This is the mid condition that hashes meet here.
         let h_mid := op_side sides_mid p.1 p.2
         -- But I need to get bounds from recursive calls.
         let h_bot : ℍ := left_range.1
         let h_top : ℍ := right_range.2
         .node (.some ⟨(), ⟨ h_bot , h_mid ⟩, ⟨ h_mid , h_top ⟩⟩)
               left_tree right_tree
       | _ ,_ ,_ => .node .none left_tree right_tree

-- Thm Winning proposer to winning proposer.
-- We have revealer/proposer winning conditions. I think we can prove through
-- that.

----------------------------------------
