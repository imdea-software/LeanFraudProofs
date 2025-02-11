import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.Base.GenericTree -- Generic Game trees
import FraudProof.Games.Base.ElemInTree -- Linear basic game definition
import FraudProof.Games.Base.RangeDAConditions -- Range DAs

import FraudProof.DataStructures.Sequence

--------------------------------------------------------------------------------
-- * Transformation from a Sequence to the /same/ game played over Trees arenas.
--------------------------------------------------------------------------------

-- Building a Tree out of skelentons.
-- This function keeps size.
-- ABTree.size is height
@[simp]
def skl_to_tree {n : Nat}
  (sk : ISkeleton n) : ABTree Unit Unit
  := match n with
    | .zero => .leaf ()
    | .succ _pn =>
      match headSeq sk with
        | .inl _ => .node () (skl_to_tree $ Fin.tail sk) (.leaf ())
        | .inr _ => .node () (.leaf ()) (skl_to_tree $ Fin.tail sk)
@[simp]
def skl_to_maybe_elem {α : Type} {n : Nat}
  (a : α) (sk : ISkeleton n) : ABTree (Option α) Unit
    := match n with
    | .zero => .leaf a
    | .succ _pn =>
      match headSeq sk with
        | .inl _ =>
          .node () (skl_to_maybe_elem a (Fin.tail sk)) (.leaf none)
        | .inr _ =>
          .node () (.leaf none) (skl_to_maybe_elem a (Fin.tail sk))


@[simp]
def build_proposer' {ℍ : Type}{n : Nat}
    (bot_hash : ℍ)
    (skl : ISkeleton n)
    (rev : Sequence n (Option (PMoves ℍ)))
    : ABTree (Option ℍ) (Option (Range ℍ × Range ℍ))
    := match n with
    | .zero => .leaf $ .some bot_hash
    | .succ _ =>
      match headSeq rev with
      | .none => .node .none (.leaf none) (.leaf none)
      | .some (.Next proposed) =>
        match headSeq skl with
        | .inl _ =>
               .node (.some ( ⟨ ⟨ bot_hash , proposed.1⟩ , proposed  ⟩ ))
                     (build_proposer' bot_hash (Fin.tail skl) (Fin.tail rev))
                     (.leaf $ .some proposed.2)
        | .inr _ =>
               .node (.some ( ⟨ proposed   , ⟨ bot_hash , proposed.2 ⟩ ⟩ ))
                     (build_proposer' bot_hash (Fin.tail skl) (Fin.tail rev))
                     (.leaf $ .some proposed.1)

@[simp]
def build_proposer {ℍ : Type}{n : Nat}
  (data : ℍ × ISkeleton n) (rev : Sequence n (Option (PMoves ℍ)))
  : ABTree (Option ℍ) (Option (Unit × ℍ × ℍ))
  := match n with
  | .zero => .leaf $ .some data.1
  | .succ _pn =>
    let rest_tree := build_proposer ⟨ data.1 , Fin.tail data.2⟩ (Fin.tail rev)
    match headSeq rev with
      | .none => .node .none (.leaf none) (.leaf .none)
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
      let side_choose (s : Chooser.Side) (arg : ℍ × Unit × ℍ × ℍ)
          : Option ChooserMoves :=
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

@[simp]
def build_chooser' {ℍ : Type}{n : Nat}
  (skl : ISkeleton n)
  (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
  : ABTree Unit (Range ℍ × SkElem  × Range ℍ × Range ℍ -> Option ChooserMoves)
  := match n with
    | .zero => .leaf ()
    | .succ _ =>
      let curr_check (args : Range ℍ × SkElem  × Range ℍ × Range ℍ)
                     : Option ChooserMoves
        := -- Should I check Range consistency? Not necesseary during transformations
          have ⟨ top_range, side, _next_range, decomp ⟩ := args
          -- top_range.1 == next_range.1 && next_range.2 == decomp.side
          match side with
          | .inl _ => match headSeq chooser ⟨ top_range.2, decomp.1, decomp.2 ⟩ with
                      | .some .Now => .some .Now
                      | .some (.Continue _) => .some $ .Continue .Left
                      | .none => .none
          | .inr _ => match headSeq chooser ⟨ top_range.2, decomp.2, decomp.1 ⟩ with
                      | .some .Now => .some .Now
                      | .some (.Continue _) => .some $ .Continue .Right
                      | .none => .none
      match headSeq skl with
      | .inl _ => .node curr_check (build_chooser' (Fin.tail skl) (Fin.tail chooser)) (.leaf ())
      | .inr _ => .node curr_check (.leaf ()) (build_chooser' (Fin.tail skl) (Fin.tail chooser))


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
    let da_tree : CompTree (Option ℍ) Unit ℍ
      := {data := skl_to_maybe_elem da.mtree.1 da.data , res := da.mtree.2}
    let tree_revealer : ABTree (Option ℍ) (Option (Unit × ℍ × ℍ))
      := build_proposer ⟨ da.mtree.1 , da.data⟩ proposer
    let tree_chooser : ABTree Unit (ℍ × Unit × ℍ × ℍ -> Option ChooserMoves)
      := build_chooser ⟨ da.mtree.1 , da.data⟩ chooser
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

def elem_in_tree_forward_gentree {ℍ : Type}
    [BEq ℍ][mag : HashMagma ℍ]
    -- DA
    {n : Nat}(da : ElemInTreeH n ℍ)
    -- Players
    (proposer : Sequence n (Option (PMoves ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    :=
    treeCompArbGame
      -- conditionsb
      leaf_condition_range
      mid_condition_range_one_step_forward
      -- DA
      {data := skl_to_tree da.data, res:= da.mtree}
      (build_proposer' da.mtree.1 da.data proposer)
      (build_chooser' da.data⟩ chooser)
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
  : elem_in_tree_backward da proposer chooser = elem_in_tree_gen_tree da proposer chooser
  := by revert n
        intro n
        induction n with
        | zero =>
          intros da prop cho
          simp [elem_in_tree_backward, elem_in_tree_gen_tree, SingleLastStepH, treeCompArbGame]
        | succ pn HInd =>
          intros da prop cho
          simp [elem_in_tree_backward, elem_in_tree_gen_tree ]
          cases prop 0 with
          | none =>
            simp [treeCompArbGame]
          | some proposed =>
            cases proposed with
            | End v => contradiction
            | Next e =>
              simp
              match HCho : cho 0 (da.mtree.2, e) with
              | none =>
                simp [treeCompArbGame]
                match da.data 0 with
                | .inl _ => simp [treeCompArbGame]; rw [HCho]; simp
                | .inr _ => simp [treeCompArbGame]; rw [HCho]; simp
              | some choosed =>
                match choosed with
                | .Now =>
                  simp [SingleMidStep]
                  cases da.data 0 with
                    | inl _ => simp [treeCompArbGame]; rw [HCho]; simp
                    | inr _ => simp [treeCompArbGame]; rw [HCho]; simp
                | .Continue _ =>
                  simp
                  cases da.data 0 with
                    | inl _ =>
                      simp [treeCompArbGame]
                      rw [HCho]; simp
                      apply HInd
                    | inr _ =>
                      simp [treeCompArbGame]
                      rw [HCho]; simp
                      apply HInd

----------------------------------------
