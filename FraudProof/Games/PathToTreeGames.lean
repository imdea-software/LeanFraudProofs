import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.GenericTree -- Generic Game trees
import FraudProof.Games.ElemInTree -- Linear basic game definition
-- import FraudProof.Games.RangeDAConditions -- Range DAs

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
      match sk.head with
        | .Left => .node () (skl_to_tree sk.tail) (.leaf ())
        | .Right => .node () (.leaf ()) (skl_to_tree sk.tail)
@[simp]
def skl_to_maybe_elem {α : Type} {n : Nat}
  (a : α) (sk : ISkeleton n) : ABTree (Option α) Unit
    := match n with
    | .zero => .leaf a
    | .succ _pn =>
      match sk.head with
        | .Left =>
          .node () (skl_to_maybe_elem a sk.tail) (.leaf none)
        | .Right =>
          .node () (.leaf none) (skl_to_maybe_elem a sk.tail)

@[simp]
def build_proposer' {ℍ : Type}{n : Nat}
    (bot_hash : ℍ)
    (skl : ISkeleton n)
    (rev : Sequence n (Option (PMoves ℍ)))
    : ABTree (Option ℍ) (Option (Range ℍ × Range ℍ))
    := match n with
    | .zero => .leaf $ .some bot_hash
    | .succ _ =>
      match rev.head with
      | .none => .node .none (.leaf none) (.leaf none)
      | .some proposed =>
        match skl.head with
        | .Left =>
               .node (.some ( ⟨ ⟨ bot_hash , proposed.1⟩ , proposed  ⟩ ))
                     (build_proposer' bot_hash skl.tail rev.tail)
                     (.leaf $ .some proposed.2)
        | .Right =>
               .node (.some ( ⟨ proposed   , ⟨ bot_hash , proposed.2 ⟩ ⟩ ))
                     (build_proposer' bot_hash skl.tail rev.tail)
                     (.leaf $ .some proposed.1)

@[simp]
def build_proposer {ℍ : Type}{n : Nat}
  (data : ℍ × ISkeleton n) (rev : Sequence n (Option (PMoves ℍ)))
  : ABTree (Option ℍ) (Option (ℍ × ℍ))
  := match n with
  | .zero => .leaf $ .some data.1
  | .succ _pn =>
    let rest_tree := build_proposer ⟨ data.1 , data.2.tail⟩ rev.tail
    match rev.head with
      | .none => .node .none (.leaf none) (.leaf .none)
      | .some (hl , hr)=>
       match data.2.head with
         | .Left =>
           .node (.some ⟨ hl, hr ⟩)
                 rest_tree
                 (.leaf (.some hr))
         | .Right =>
           .node (.some ⟨  hl, hr ⟩)
                 (.leaf (.some hl))
                 rest_tree
@[simp]
def build_chooser {ℍ : Type}{n : Nat}
  (data : ℍ × ISkeleton n)
  (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
  : ABTree Unit (ℍ × ℍ × ℍ -> Option ChooserMoves)
  := match n with
    | .zero => .leaf ()
    | .succ _pn =>
      let side_choose (s : Side) (arg : ℍ × ℍ × ℍ)
          : Option ChooserMoves :=
          have ⟨ ht ,  hl , hr ⟩ := arg
          (chooser.head ⟨ ht, hl , hr ⟩).map
            (fun ch => match ch with
                       | .Now => .Now
                       | .Continue _ => .Continue s)
      match data.2.head with
      | .Left =>
        .node
          (side_choose .Left)
          (build_chooser ⟨data.1 , data.2.tail⟩ chooser.tail)
          (.leaf ())
      | .Right =>
        .node
          (side_choose .Right)
          (.leaf ())
          (build_chooser ⟨data.1 , data.2.tail⟩ chooser.tail)

@[simp]
def build_chooser' {ℍ : Type}{n : Nat}
  (skl : ISkeleton n)
  (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
  : ABTree Unit ((ℍ × ℍ) × (ℍ × ℍ) × (ℍ × ℍ) -> Option ChooserMoves)
  := match n with
    | .zero => .leaf ()
    | .succ _ =>
      let curr_check (side : SkElem) (args : Range ℍ  × Range ℍ × Range ℍ)
                     : Option ChooserMoves
        := -- Should I check Range consistency? Not necesseary during transformations
          have ⟨ top_range, _next_range, decomp ⟩ := args
          -- top_range.1 == next_range.1 && next_range.2 == decomp.side
          match side with
          | .Left => match chooser.head ⟨ top_range.2, decomp.1, decomp.2 ⟩ with
                      | .some .Now => .some .Now
                      | .some (.Continue _) => .some $ .Continue .Left
                      | .none => .none
          | .Right => match chooser.head ⟨ top_range.2, decomp.2, decomp.1 ⟩ with
                      | .some .Now => .some .Now
                      | .some (.Continue _) => .some $ .Continue .Right
                      | .none => .none
      match skl.head with
      | .Left => .node (curr_check .Left) (build_chooser' skl.tail chooser.tail) (.leaf ())
      | .Right => .node (curr_check .Right) (.leaf ()) (build_chooser' skl.tail chooser.tail)


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
    let tree_revealer : ABTree (Option ℍ) (Option (ℍ × ℍ))
      := build_proposer ⟨ da.mtree.1 , da.data⟩ proposer
    let tree_chooser : ABTree Unit (ℍ × ℍ × ℍ -> Option ChooserMoves)
      := build_chooser ⟨ da.mtree.1 , da.data⟩ chooser
    treeCompArbGame
      (fun opth _h1 h2 =>
        match opth with
        | .none => -- this case is a bit artificial
        -- chooser should challenge previous step.
          true
          -- Player.Proposer
        | .some hp => (hp == h2)
      )
      (fun _ hres pl pr =>
        -- _nodeh and hres should be the same.
           mag.comb pl pr == hres)
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
      (build_chooser' da.data chooser)

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
  : elem_in_tree_backward da proposer chooser
  = elem_in_tree_gen_tree da proposer chooser
  := by revert n
        intro n
        induction n with
        | zero =>
          intros da prop cho
          simp [elem_in_tree_backward, elem_in_tree_gen_tree, SingleLastStepH, treeCompArbGame]
        | succ pn HInd =>
          intros da prop cho
          simp [elem_in_tree_backward, elem_in_tree_gen_tree ]
          have ⟨ propls, propln ⟩ := prop
          cases propls.head _ with
          | none =>
            simp [treeCompArbGame]
          | some e =>
              simp
              have ⟨ chols, chop ⟩ := cho
              match HCho : chols.head _ (da.mtree.2, e) with
              | none =>
                simp [treeCompArbGame]
                have ⟨datals, datap ⟩ := da.data
                cases datals.head _ with
                | Left => simp [treeCompArbGame]; rw [HCho]; simp
                | Right => simp [treeCompArbGame]; rw [HCho]; simp
              | some choosed =>
                match choosed with
                | .Now =>
                  simp [SingleMidStep]
                  have ⟨datals, datap ⟩ := da.data
                  cases datals.head _ with
                    | Left => simp [treeCompArbGame]; rw [HCho]; simp
                    | Right => simp [treeCompArbGame]; rw [HCho]; simp
                | .Continue _ =>
                  simp
                  -- simp [SingleMidStep]
                  have ⟨datals, datap ⟩ := da.data
                  cases datals.head _ with
                    | Left =>
                      simp [treeCompArbGame]
                      rw [HCho]; simp
                      apply HInd
                    | Right =>
                      simp [treeCompArbGame]
                      rw [HCho]; simp
                      apply HInd
----------------------------------------
