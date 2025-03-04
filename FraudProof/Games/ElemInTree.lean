import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.GenericTree -- Generic Game trees

import FraudProof.DataStructures.Sequence
import FraudProof.DataStructures.MTree -- SkElem dsetrtuct

import Mathlib.Data.Fin.Tuple.Basic

import FraudProof.DataStructures.Hash -- Hash Stuff

----------------------------------------
-- * Element in Tree basic game definitions Linear game and simple games playing
-- with the idea of needing to have the element in question or not. If we do not
-- have the element, we play games only with hashes.

-- DA: element is in Tree
structure ElemInMTree (α ℍ : Type) where
  elem : α
  path : Skeleton
  mtree : ℍ
  -- Prop: foldl hash_Path (hash elem) path = mtree

def implicit_element_in_tree {α ℍ : Type}[m : Hash α ℍ][mag : HashMagma ℍ]
   (computation : ElemInMTree α ℍ)
   (missing_data : List ℍ)
   : Prop
   := List.foldr
       (fun (side, h) acc => op_side side h acc)
       (m.mhash computation.elem) (List.zip computation.path missing_data)
      = computation.mtree

-- Here we do not need to know the whole tree.
-- maybe we need to define some notion of DA promotion.
-- Whatever game we define over Skeletons we can play over trees?

def leaf_condition {α ℍ : Type}[BEq ℍ][o : Hash α ℍ]
    (a : α)(h : ℍ) : Winner
    := winning_proposer $ o.mhash a == h

def mid_condition {ℍ : Type}[BEq ℍ][mag : HashMagma ℍ]
    ( p :  PMoves ℍ ) (h : ℍ) : Winner
    := winning_proposer $ mag.comb p.1 p.2 == h

-- Element in Tree arbitration game! Intermediate steps
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
                                | .Left => proposed.left
                                | .Right => proposed.right
                arbElem (pos ++ [sibside]) ⟨ da.elem , rest, nextHash⟩
                        proposer chooser
    termination_by da.path
    decreasing_by {simp_wf; rw [_HC]; simp; omega}

-- Element in Tree arbitration game!
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

def SingleLastStep {α ℍ : Type}[BEq ℍ][h : Hash α ℍ] (data : ElemInTreeN 0 α ℍ) : Winner
  := winning_proposer $ h.mhash (data.data.1) == data.mtree

def SingleMidStep {ℍ : Type}[BEq ℍ][m : HashMagma ℍ ](data : ℍ × ℍ × ℍ) : Winner
  := winning_proposer $ m.comb data.2.1 data.2.2 == data.1

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
         match proposer.head with
         | .none => Player.Chooser -- Proposer forfeits the game
         | .some proposed =>
           match chooser.head ⟨ da.mtree , proposed ⟩ with
           | .none => Player.Proposer -- Chooser forfeits the game
           | .some .Now =>
             SingleMidStep  ⟨ da.mtree , proposed ⟩
           | .some (.Continue _) =>
             have nextHash := match da.data.2.head with
                    | .Left => proposed.1
                    | .Right => proposed.2
             elemInHGame
               -- Next step DA
               ⟨⟨ da.data.1, da.data.2.tail⟩ , nextHash ⟩
               -- Next step players
               proposer.tail
               chooser.tail

structure ElemInTreeH (n : Nat)(ℍ : Type) where
  data : ISkeleton n -- This is the 'skeleton proof'
  mtree : ℍ × ℍ
  -- Same as above but only using hashes
  -- |dt ! data| leads to | mtree.2.2 | where |mtree.2.1| is the hash of the element
  -- in a tree [see the above DA].

-- Here we can have some troubles. We do not know if we really are talking about
-- the same element.
-- If path is of length 0, then elements should be the same. Although, hashes
-- are the same, elements maybe not be.
def SingleLastStepH {ℍ : Type}[BEq ℍ] (data : ElemInTreeH 0 ℍ) : Winner
  := winning_proposer $ data.mtree.1 == data.mtree.2

def elem_in_tree_backward {ℍ : Type}
    [BEq ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (Option (PMoves ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : Winner
    := match n with
       | 0 => SingleLastStepH da
       | .succ _pn =>
         match proposer.head with
         | .none => Player.Chooser -- Proposer forfeits the game
         | .some proposed =>
           match chooser.head ⟨ da.mtree.2 , proposed ⟩ with
           | .none => Player.Proposer -- Chooser forfeits the game
           | .some .Now => SingleMidStep  ⟨ da.mtree.2 , proposed ⟩
           | .some (.Continue _) =>
             have nextHash := match da.data.head with
                    | .Left => proposed.1
                    | .Right => proposed.2
             elem_in_tree_backward
               -- Next step DA
               { data := da.data.tail, mtree := ⟨ da.mtree.1 , nextHash⟩  }
               -- Next step players
               proposer.tail
               chooser.tail

@[simp]
def forward_mid_step_condition {ℍ : Type}[BEq ℍ][m : HashMagma ℍ ]
  (side : SkElem) (data : ℍ × ℍ) (res : ℍ) : Winner
  := winning_proposer $ op_side side data.1 data.2 == res

-- Reverse game -- It is not (*JUST*) the reverse game.
-- Proposer proposes different hashes that the previos linear game.
--
def elem_in_tree_forward {ℍ : Type}[BEq ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (Option (PMoves ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : Winner
    := match n with
      | 0 => SingleLastStepH da
      | .succ _pn =>
        match proposer.head with
        | .none => Player.Chooser
        | .some proposed =>
            match chooser.head ⟨ da.mtree.1, proposed ⟩ with
            | .none  => Player.Proposer
            | .some .Now =>
              forward_mid_step_condition
                da.data.head ⟨ da.mtree.1 , proposed.2⟩ proposed.1
            | .some (.Continue _) =>
              elem_in_tree_forward
                {data := da.data.tail, mtree := ⟨ proposed.1 , da.mtree.2⟩}
                proposer.tail
                chooser.tail

def elem_in_forward {α ℍ : Type}{n : Nat}
    [BEq ℍ]
    [o : Hash α ℍ][m : HashMagma ℍ]
    (path : ISkeleton n)
    (elem : α)(top : ℍ)
    (proposer : Sequence n (Option (ℍ × ℍ)))
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : Winner
    := elem_in_tree_forward ⟨ path, (o.mhash elem, top)⟩ proposer chooser

-- From MkTree to element (backward), element is a maybe provided by proposer.
def elem_in_backward_rev {α ℍ : Type}{n : Nat}
    [BEq ℍ]
    [o : Hash α ℍ][m : HashMagma ℍ]
    (path : ISkeleton n)
    (top : ℍ)
    (proposer : Sequence n (Option (ℍ × ℍ)) × Option α)
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : Winner × Option α
    := match n with
      | .zero => match proposer.snd with
                | .none => (Player.Chooser , .none)
                | .some v =>
                  if o.mhash v == top
                  then (Player.Proposer, .some v)
                  else (Player.Chooser, .none)
      | .succ _ =>
        match proposer.fst.head with
        | .none => (Player.Chooser, .none)
        | .some proposed => match chooser.head ⟨ top , proposed ⟩ with
          | .none => (Player.Proposer, .none)
          | .some .Now =>
            if  m.comb proposed.1 proposed.2 == top
            then (Player.Proposer , .none)
            else (Player.Chooser, .none)
            -- forward_mid_step_condition path.head (top, proposed.2) proposed.1
          | .some (.Continue _) =>
            @elem_in_backward_rev _ _ _ _ o m
              path.tail (path.head.destruct proposed.1 proposed.2)
              -- Players
              ( proposer.fst.tail , proposer.snd ) chooser.tail

-- * Naive Honest Player Two
-- Linear
def naive_lin_forward_test {ℍ : Type}[m : HashMagma ℍ][BEq ℍ]
  : ℍ × ℍ × ℍ -> Option ChooserSmp
  := fun (top, hl , hr) => .some $ if m.comb hl hr == top then .Continue () else .Now

def naive_lin_forward {ℍ : Type}{n : Nat}[ HashMagma ℍ][BEq ℍ]
  : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp)
  := .constant naive_lin_forward_test

-- * Winning Lemmas
--
lemma elem_back_rev_honest_two {α ℍ : Type}{n : Nat}
  [DecidableEq α] [BEq ℍ][LawfulBEq ℍ][H : Hash α ℍ][Mag : HashMagma ℍ]
  [ injH : @InjectiveHash α ℍ H][injM : @InjectiveMagma ℍ Mag]
  {ph : ISkeleton n}{mk : ℍ}{e : α}
  {proposer : Sequence n (Option (ℍ × ℍ)) × Option α}
  --
  {data : BTree α}
  (HMkTree : data.hash_BTree = mk)
  (HElem : data.iaccess ph = .some (.inl e))
  -- Proposer plays to the end and wins showing that element |e| is in the tree
  : elem_in_backward_rev ph mk proposer naive_lin_forward = (Player.Proposer , .some e)
  -- Proposer abandons and Chooser wins.
  ∨ elem_in_backward_rev ph mk proposer naive_lin_forward = (Player.Chooser , .none)
 := by
    revert mk proposer data HElem HMkTree e
    induction n with
    | zero =>
      intros mk e prop
      intros data HMkTree HElem
      unfold elem_in_backward_rev
      cases HProp : prop.2 with
      | none => simp
      | some v =>
        have ph_nil := @nil_equiv _ ph
        rw [ph_nil, nil_access data] at HElem
        subst_eqs
        simp
        split
        case isTrue h =>
          simp at *
          apply injH.inject at h
          left; assumption
        case isFalse h =>
          simp at *; assumption
    | succ _pn HInd =>
      intros mk e prop
      intros data HMkTree HElem
      simp [elem_in_backward_rev]
      have ⟨ propSeq, propV ⟩ := prop
      cases HHead : propSeq.head with
      | none => simp at HHead; simp; rw [HHead]; simp
      | some proposed =>
        simp at HHead; simp; rw [HHead];simp
        simp [naive_lin_forward, naive_lin_forward_test]
        cases HComb : Mag.comb proposed.1 proposed.2 == mk
        case false => simp
        case true =>
           simp
           have ⟨ seqLs, seqLen ⟩ := ph
           cases data with
           | leaf _ =>
             simp [ABTree.iaccess, sequence_forget] at HElem
             cases seqLs with
             | nil => simp at seqLen
             | cons head tail => simp [ABTree.access] at HElem
           | node iunit bL bR =>
            -- have Hind := @HInd ph.tail (ph.head.destruct proposed.1 proposed.2) e (prop.1.tail, prop.2) (ph.head.destruct bL bR)
            simp at HMkTree
            simp at HComb; rw [<- HComb] at HMkTree
            -- simp at Hind
            cases HSide : seqLs.head _ with
            | Left =>
              simp [SkElem.destruct]
              apply injM.injectL at HMkTree
              apply HInd
              simp; exact HMkTree
              apply ABTree.iaccess_head_left at HElem; assumption
              simp; assumption
            | Right =>
              simp [SkElem.destruct]
              apply injM.injectR at HMkTree
              apply HInd
              simp; exact HMkTree
              apply ABTree.iaccess_head_right at HElem; assumption
              simp; assumption

----
-- * Winning conditions
-- We did this on first poc.
--
-- Proposer wins all possible games.
-- leaf and mid winning conditions
-- @[simp]
def elem_in_reveler_winning_condition_backward {ℍ : Type}
    [BEq ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (PMoves ℍ))
    : Prop
    := match n with
       | .zero => SingleLastStepH da = Player.Proposer
       | .succ _pn =>
         -- match proposer.head with
         -- | .Next proposed =>
           SingleMidStep  ⟨ da.mtree.2 , proposer.head ⟩ = Player.Proposer
           ∧ elem_in_reveler_winning_condition_backward
               { data := da.data.tail
                , mtree := ⟨ da.mtree.1 , (match da.data.head with
                                            | .Left => proposer.head.1
                                            | .Right => proposer.head.2
                                            )⟩
               }
               proposer.tail

def elem_in_reveler_winning_condition_forward {ℍ : Type}
    [BEq ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (ℍ × ℍ))
    -- Proposer proposes parent and sibling.
    : Prop
    := match n with
       | .zero => SingleLastStepH da = Player.Proposer
       | .succ _pn =>
           (winning_proposer ((op_side da.data.head da.mtree.1 proposer.head.2) == proposer.head.1) = Player.Proposer)
           ∧ elem_in_reveler_winning_condition_forward
               { data := da.data.tail
                , mtree := ⟨ proposer.head.1
                           , da.mtree.2⟩
               }
               proposer.tail

def spine_forward {ℍ : Type}{n : Nat}
  : Sequence n (PMoves ℍ) -> Sequence n ℍ
  := Sequence.map (fun p => p.1)

def sibling_forward {ℍ : Type}{n : Nat}
  : Sequence n (PMoves ℍ) -> Sequence n ℍ
  := Sequence.map (fun p => p.2)

-- @check foldr
-- Winning proposer prop is a winning sufficient condition.
theorem winning_reveler_wins {ℍ : Type}
    [BEq ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (PMoves ℍ))
    (winning_prop : elem_in_reveler_winning_condition_backward da proposer)
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : elem_in_tree_backward da (proposer.map .some) chooser = Player.Proposer
    := by revert n
          intro n
          induction n with
          | zero =>
            intros da prop Hwin cho
            simp [elem_in_tree_backward]
            simp [elem_in_reveler_winning_condition_backward] at Hwin
            assumption
          | succ pn HInd =>
            intros da prop Hwin cho
            simp [elem_in_tree_backward]
            simp [elem_in_reveler_winning_condition_backward] at Hwin
            sorry
            -- cases HP : prop.head with
            -- | End v => contradiction
            -- | Next p =>
            --   simp; rw [HP] at Hwin; simp at Hwin
            --   cases HC : cho 0 (da.mtree.2, p) with
            --   | none => simp
            --   | some chod =>
            --     cases chod with
            --     | Now => simp; exact Hwin.1
            --     | Continue _ =>
            --       simp
            --       apply HInd
            --       exact Hwin.2

-- Winning proposer prop is a winning sufficient condition.
theorem winning_reveler_wins_forward {ℍ : Type}
    [BEq ℍ][HashMagma ℍ]
    {n : Nat}
    (da : ElemInTreeH n ℍ)
    (proposer : Sequence n (PMoves ℍ))
    (winning_prop : elem_in_reveler_winning_condition_forward da proposer)
    (chooser : Sequence n (ℍ × ℍ × ℍ -> Option ChooserSmp))
    : elem_in_tree_forward da (proposer.map .some) chooser = Player.Proposer
    := by
 revert n; intro n; induction n with
 | zero =>
   intros da proposer wProp cho
   simp [elem_in_reveler_winning_condition_forward] at wProp
   simp [elem_in_tree_forward]
   assumption
 | succ pn Hind =>
   intros da prop wProp ch
   simp [elem_in_tree_forward]
   simp [elem_in_reveler_winning_condition_forward] at wProp
   sorry
   -- cases HP : prop 0 with
   -- | End v => contradiction
   -- | Next p =>
   --  simp
   --  cases HC : ch 0 (da.mtree.1 , p) with
   --  | none => simp
   --  | some ched =>
   --    cases HCd : ched with
   --    | Now =>
   --      simp
   --      rw [HP] at wProp; simp at wProp
   --      exact wProp.1
   --    | Continue s =>
   --     simp; rw [HP] at wProp; simp at wProp
   --     exact Hind ⟨ Fin.tail da.data, (p.1 , da.mtree.2)⟩ (Fin.tail prop) wProp.2 (Fin.tail ch)

--
--
-- * Chooser Conditions

-- I am sure I defined this somewhere else
def last_step {ℍ : Type}[BEq ℍ][m : HashMagma ℍ ]
  (side : SkElem)(res : ℍ) (data : ℍ × ℍ)  : Winner
  := winning_proposer $ op_side side data.1 res == data.2

def knowing {ℍ : Type}[BEq ℍ][HashMagma ℍ]
  ( skl : ABTree SkElem Unit )( know : ABTree ℍ ℍ ) (i o : ℍ) : Prop
  := match skl, know with
     -- Cases
     | .leaf sk, .leaf h => op_side sk i h = o
     | .node _ al ar , .node mid kl kr =>
       knowing al kl i mid ∧ knowing ar kr mid o
     -- Same structure
     | _ , _ => False

def input_prop {ℍ : Type} (data : ABTree (Option ℍ) (Option ℍ))(i : ℍ)
  : Prop
  := match data with
    | .node _ bl _ => input_prop bl i
    | .leaf (.some h) => h = i
    | .leaf none => False

theorem range_chooser_wins {ℍ : Type}
    [BEq ℍ][LawfulBEq ℍ]
    [HashMagma ℍ][hash_props : SLawFulHash ℍ]
    (comp_skeleton : ABTree SkElem Unit)
    (input_rev input_ch: ℍ)(output : ℍ)
    -- current da is {comp_skeleton , (input_rev , output) }
    (hneq : ¬ input_rev = input_ch)
    -- Reveler
    (reveler : ABTree (Option ℍ) (Option ℍ))
    -- Chooser
    (chooser : ABTree ℍ ℍ)
    -- Computation is fold plus invariants.
    (chooser_wise : knowing comp_skeleton chooser input_ch output)
    : spl_game
      { data:= comp_skeleton , res := (input_rev , output) }
      reveler
      (gen_to_fun_chooser (ABTree.map .some .some chooser))
      = Player.Chooser
    := by
  revert chooser_wise chooser reveler hneq input_rev input_ch output
  induction comp_skeleton with
  | leaf sk =>
    intros in_rev in_ch out hneq rev cho kcho
    cases HRev : rev with
    | node _ _ _ => simp [spl_game, simp_tree]
    | leaf p =>
      cases HP : p with
      | none => simp [spl_game, simp_tree]
      | some proposed =>
        simp [gen_to_fun_chooser, spl_game, simp_tree]
        -- unfold knowing at kcho
        cases cho with
        | node _ _ _ =>
          simp [knowing] at kcho
        | leaf ch =>
          simp [knowing] at kcho
          -- simp [last_step]
          rw [<- kcho]
          cases sk with
          | Left =>
            simp at *
            apply hash_props.neqLeft
            assumption
          | Right =>
            simp at *
            apply hash_props.neqRight
            assumption
  | node _ game_left game_right HIndL HIndR =>
    intros in_rev in_ch out hneq rev cho kcho
    simp [spl_game, simp_tree]
    cases rev with
    | leaf _ => simp [simp_tree]
    | node may_mid rev_l rev_r =>
      cases may_mid with
      | none => simp [simp_tree]
      | some mid =>
        simp [simp_tree]
        cases cho with
        | leaf _ => simp [knowing] at kcho
        | node cho_mid ch_l ch_r =>
          simp [gen_to_fun_chooser]
          split
          case h_1 x heq =>
            rw [ite_eq_iff] at heq
            simp at heq
          case h_2 x heq =>
           simp at heq
           apply HIndL
           --
           exact hneq
           --
           simp [knowing] at kcho
           rw [<- heq]
           exact kcho.1
          case h_3 x heq =>
           simp at heq
           have hind := HIndR mid cho_mid out (by intro ha; apply heq; rw [ha])
           -- apply HIndR
           apply hind
           --
           simp [knowing] at kcho
           exact kcho.2
          case h_4 x heq =>
            rw [ite_eq_iff] at heq
            simp at heq
