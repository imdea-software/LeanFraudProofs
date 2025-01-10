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

def leaf_condition {α ℍ : Type}[BEq ℍ][o : Hash α ℍ]
    (a : α)(h : ℍ) : Winner
    := condWProp $ o.mhash a == h

def mid_condition {ℍ : Type}[BEq ℍ][mag : HashMagma ℍ]
    ( p :  PMoves ℍ ) (h : ℍ) : Winner
    := match p with
      | .Next ⟨hl, hr⟩ => condWProp $ mag.comb hl hr == h

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
       | .nil => leaf_condition da.elem da.mtree
       | .cons sibside rest =>
         match proposer pos with
         | none => Player.Chooser
         | some proposed =>
          match chooser pos proposed with
            | none => Player.Proposer
            | some .Now => mid_condition proposed da.mtree
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

-- Same as opHash??
-- I use SkElem to signal where the path is going.
@[simp]
def op_side {α : Type}[mag : HashMagma α] (o : SkElem) (a b : α) : α
 := match o with
   | .inl _ => mag.comb a b
   | .inr _ => mag.comb b a

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
           | .some .Now =>
             SingleMidStep  ⟨ da.mtree , proposed ⟩
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
           | .some .Now => SingleMidStep  ⟨ da.mtree , proposed ⟩
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
           condWProp $ mag.comb pl pr == hres)
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
-- Logarithmic Search Definitions
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
  := perfectSeq rev

def from_side {α : Type} (sa : Side α) : α :=
  match sa with
  | .inl a => a
  | .inr a => a

abbrev Range (α : Type) := α × α

@[simp]
def all_true (ls : List Bool) : Bool := ls.all id

def leaf_condition_transformation {ℍ : Type}[BEq ℍ][mag : HashMagma ℍ]
  : SkElem -> ℍ -> Range ℍ -> Winner
  := (fun side prop ⟨ bot, top ⟩
     -- |[bot, top]| and |prop| is supposed to be in the middle.
     -- => condWProp $ mag.comb bot prop == top)
     => condWProp $ op_side side bot prop == top)

def mid_condition_transformation{ℍ : Type}[BEq ℍ]
  : SkElem -> Unit -> Range ℍ -> Range ℍ -> Range ℍ -> Winner
  := (fun (_side : SkElem) (_t : Unit)
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
    let balanced_da : CompTree SkElem SkElem (Range ℍ)
        := { data := perfectSeq da.data.2
    -- + |res| are the extremes of the chain mentioned above.
           , res  := ⟨ da.data.1 , da.mtree ⟩}
    treeCompArbGame
      leaf_condition_transformation
      mid_condition_transformation
      balanced_da
      proposer chooser

@[simp]
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
            (fun (.Next ⟨hl , hr⟩)
              => -- We return the sibiling hash!
                match headSeq sides with
                 | .inl _ => hr
                 | .inr _ => hl
              -- h_extra -- @op_side ℍ mag (headSeq sides) h_bot h_extra
              )
            -- TODO add Unit range -> true
            -- let h_top := @op_side ℍ mag (headSeq sides) h_bot h_extra
            -- .node (.some ⟨ (), ⟨ h_bot , h_bot⟩ , ⟨ h_top , h_top ⟩ ⟩)
            --       -- Leafs are winning positions for the proposer.
            --       (.leaf $ .some h_bot)
            --       (.leaf $ .some h_top)
     | .succ _pn =>
       -- Sides path info
       let ⟨ sides_left, sides_mid , sides_right ⟩ := seqPerfectSplit sides
       -- Reveler data
       let ⟨ prop_left, prop_mid, prop_right ⟩ := seqPerfectSplit proposer
       let left_tree := @logarithmic_proposer _ mag _ sides_left prop_left
       let right_tree := @logarithmic_proposer _ mag _ sides_right prop_right
       match prop_mid
             , get_total_range_tree left_tree
             , get_total_range_tree right_tree
       with
       | .some (.Next p) , .some left_range, .some right_range =>
         -- This is the mid condition that hashes meet here.
         -- TODO Warning here
         let h_mid := op_side sides_mid p.1 p.2
         -- let h_mid := mag.comb p.1 p.2 -- I am not so sure about op_side
         -- END TODO Warning here
         -- But I need to get bounds from recursive calls.
         let h_bot : ℍ := left_range.1
         let h_top : ℍ := right_range.2
         .node (.some ⟨(), ⟨ h_bot , h_mid ⟩, ⟨ h_mid , h_top ⟩⟩)
               left_tree right_tree
       | _ ,_ ,_ => .node .none left_tree right_tree
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

-- Proposer wins all possible games.
-- leaf and mid winning conditions
@[simp]
def elem_in_reveler_winning_condition {ℍ : Type}
    [BEq ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (Option (PMoves ℍ)))
    : Prop
    := match n with
       | .zero => SingleLastStepH da = Player.Proposer
       | .succ _pn =>
         match headSeq proposer with
         | .some (.Next proposed) =>
           SingleMidStep  ⟨ da.mtree , proposed ⟩ = Player.Proposer
           ∧ elem_in_reveler_winning_condition
              (match headSeq da.data.2 with
                | .inl _ =>
                       ⟨ ⟨ da.data.1 , tailSeq da.data.2⟩ , proposed.1⟩
                | .inr _ =>
                       ⟨ ⟨ da.data.1 , tailSeq da.data.2⟩ , proposed.2⟩
                )
               (tailSeq proposer)
         | .none => False

def to_mid_step { ℍ : Type } {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (Option (PMoves ℍ)))
    (m : Nat)( mLt : m < n)
    : Option ℍ
    := match m with
      | .zero => da.mtree
      | .succ pm =>
        let proposer' : Sequence n.pred.succ (Option (PMoves ℍ))
          := sequence_coerce (by rw [Eq.comm]; apply Nat.succ_pred; omega ) proposer
        let sides : ISkeleton n.pred.succ
          := sequence_coerce (by rw [Eq.comm]; apply Nat.succ_pred; omega ) da.data.2
        match headSeq proposer' with
        | .none => .none
        | .some (.Next proposed) =>
          let nextHash :=
            match headSeq sides with
            | .inl _ => proposed.1
            | .inr _ => proposed.2
          @to_mid_step _ n.pred
                   {data := ⟨ da.data.1 , Fin.tail sides ⟩
                   , mtree := nextHash}
                   (Fin.tail proposer')
                   pm (by
                      let eqN : pm.succ.pred = pm := by exact Nat.pred_succ pm
                      rw [<- eqN]
                      apply Nat.pred_lt_pred
                      simp
                      assumption
                      )

-- We are defining the same lemmas and theorems as the first implementations.
theorem forall_mid_step {ℍ : Type}
    [BEq ℍ][HashMagma ℍ] {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (Option (PMoves ℍ)))
    : elem_in_reveler_winning_condition da proposer ->
      forall (i : Nat)(iNZ : 0 < i)(iLtn : i < n),
       exists (h_mid : ℍ)(proposed : ℍ × ℍ),
        proposer ⟨ i, iLtn ⟩ = .some (.Next proposed)
        ∧ to_mid_step da proposer i iLtn = .some h_mid
        ∧ SingleMidStep ⟨ h_mid
                        , proposed ⟩ = Player.Proposer
    := sorry

----------------------------------------
-- DA + Proposer Algebra?

def da_sum {ℍ : Type}{n m : Nat}
  (da_l : ElemInTreeH n ℍ)
  (da_r : ElemInTreeH m ℍ)
  -- (_eq_bounds : da_l.mtree = da_r.data.1)
  : ElemInTreeH (n + m) ℍ
  := { data := ⟨ da_l.data.1 , concatSeq da_l.data.2 da_r.data.2 ⟩
     , mtree := da_r.mtree}

def proposer_sum {ℍ : Type}{n m : Nat}
  (proposer_l : Sequence n (Option (PMoves ℍ)))
  (proposer_r : Sequence m (Option (PMoves ℍ)))
  : Sequence (n+m) (Option (PMoves ℍ)) := concatSeq proposer_l proposer_r

theorem winning_reveler_sum {ℍ : Type}
    [BEq ℍ][LawfulBEq ℍ][HashMagma ℍ]
    {n m : Nat}
    -- Revelers
    (da_l : ElemInTreeH n ℍ)(proposer_l : Sequence n (Option (PMoves ℍ)))
    (good_left : elem_in_reveler_winning_condition da_l proposer_l)
    (da_r : ElemInTreeH m ℍ)(proposer_r : Sequence m (Option (PMoves ℍ)))
    (good_right : elem_in_reveler_winning_condition da_r proposer_r)
    -- Such that share a meeting point
    (eq_mid : da_l.mtree = da_r.data.1)
    : elem_in_reveler_winning_condition (da_sum da_l da_r)
                                        (proposer_sum proposer_l proposer_r)
    := by unfold elem_in_reveler_winning_condition
          revert m
          intro m
          induction m with
          | zero =>
            intros da_r proposer_r good_right eq_mid
            simp
            cases n with
            | zero =>
              simp [SingleLastStepH, condWProp,da_sum];
              unfold elem_in_reveler_winning_condition at good_right
              simp [SingleLastStepH, condWProp] at good_right
              unfold elem_in_reveler_winning_condition at good_left
              simp [SingleLastStepH, condWProp] at good_left;
              rwa [good_left,eq_mid]
            | succ pn =>
              simp [proposer_sum, da_sum]
              unfold elem_in_reveler_winning_condition at good_left
              cases H : headSeq proposer_l with
              | none => rw [H] at good_left; simp at good_left
              | some proposed =>
                rw [H] at good_left; simp at good_left
                replace (.Next proposed) := proposed
                simp at H; rw [H]; simp
                simp at good_left
                sorry
          | succ pm HInd =>
                 sorry

-- We can split das, but we need a ℍ to split it.
def split_da {ℍ}{n : Nat}
    (da : ElemInTreeH n ℍ)
    (cut_h : ℍ)
    (m : Nat)( mLtn : m ≤ n) -- 0 < n
    : (ElemInTreeH m ℍ × ElemInTreeH (n - m) ℍ)
    := let ⟨ left_skl , right_skl ⟩ := splitSeq da.data.2 m mLtn
      ⟨ {data := ⟨ da.data.1 , left_skl⟩ , mtree := cut_h}
      , {data := ⟨ cut_h , right_skl⟩ , mtree := da.mtree} ⟩

----------------------------------------

theorem linear_to_log_winning_proposer {ℍ : Type}
    [BEq ℍ][LawfulBEq ℍ][mag : HashMagma ℍ]
    -- DA
    {lgn : Nat}(da : ElemInTreeH (2^lgn.succ - 1) ℍ)
    -- Reveler
    (lin_reveler : Sequence (2^lgn.succ - 1) (Option (PMoves ℍ)))
    (win_lin : elem_in_reveler_winning_condition da lin_reveler)
    : reveler_winning_condition
        leaf_condition_transformation
        mid_condition_transformation
        { data := perfectSeq da.data.2
        , res  := ⟨ da.data.1 , da.mtree ⟩}
        (@logarithmic_proposer _ mag _ da.data.2 lin_reveler)
    := by revert lgn
          intro lgn
          induction lgn with
          | zero =>
            intros da lin_reveler HGood
            replace ⟨ data , res ⟩ := da
            replace ⟨ bot, skl ⟩ := data
            simp at *
            simp [logarithmic_proposer, reveler_winning_condition]
            cases H : headSeq lin_reveler with
            | none => simp at H; rw [H] at HGood; simp at HGood
            | some proposed =>
              replace .Next proposed := proposed
              simp at H;  rw [H] at HGood; simp at HGood
              rw [H]; simp
              unfold reveler_winning_condition; simp [perfectSeq]
              simp [leaf_condition_transformation]
              simp [condWProp]
              replace ⟨ current, bounds ⟩ := HGood
              simp [SingleLastStepH, condWProp] at bounds
              simp [SingleMidStep, condWProp] at current
              cases HSkl : headSeq skl with
              | inl _ => simp at HSkl; rw [HSkl]; rw [HSkl] at bounds; simp at *; rwa [bounds]
              | inr _ => simp at HSkl; rw [HSkl]; rw [HSkl] at bounds; simp at *; rwa [bounds] -- TODO Think about this.
          | succ pn HInd =>
            intros da lin_reveler HGood
            replace ⟨ data, res ⟩ := da
            replace ⟨ hlast , skeleton ⟩ := data
            simp [logarithmic_proposer]

            let ⟨ left_reveler , mid_reveler, right_reveler ⟩  := seqPerfectSplit lin_reveler
            let ⟨ left_skl , mid_skl, right_skl ⟩ := seqPerfectSplit skeleton
            simp
            -- cases HMid : mid_reveler with
            -- | none => sorry
            -- | some proposed =>
            --   replace (.Next proposed) := proposed
            --   unfold reveler_winning_condition
            --   simp
            -- match mid_reveler with
            have all_mid_steps := forall_mid_step _ _ HGood
            replace all_mid_steps := all_mid_steps ((2 ^ pn) + 1) (by sorry) (by sorry)
            -- unfold seqPerfectSplit
            unfold logarithmic_proposer

            sorry -- TODO we need some crazy theorems here.
