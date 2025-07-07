import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.MTree
import FraudProof.DataStructures.Sequence

import FraudProof.L2

----------------------------------------
-- ## Stateful Protocol.
--
-- Now we have a history of all previous accepted batches.

def historical_valid
  {α ℍ : Type} [DecidableEq α][Hash α ℍ][HashMagma ℍ]
  -- History of commited blocks and their hashes.
  (Hist : List (BTree α × ℍ))
  -- Validity Function
  (val_fun : α -> Bool)
  : Prop
  :=
  -- Each epoch is `local_valid`
  (∀ e ∈ Hist, local_valid e val_fun)
  ∧ -- Plus there are no duplicated elements. This one subsumes nodup in local_valid.
  (List.Nodup (Hist.map (BTree.toList $ ·.fst)).flatten)

-- Fundamental lemma to compose with `local_valid`.
lemma historical_concat
  {α ℍ : Type} [DecidableEq α][Hash α ℍ][HashMagma ℍ]
  --
  (hist : List (BTree α × ℍ))
  (new : BTree α × ℍ)
  (val_fun : α -> Bool)
  : historical_valid (hist ++ [new]) val_fun
    = (historical_valid hist val_fun
    ∧ List.Nodup ((hist.map (BTree.toList $ ·.fst)).flatten ++ new.fst.toList)
    ∧ local_valid new val_fun)
  := by simp
        apply Iff.intro
        · intro HHist
          apply And.intro
          · simp [historical_valid] at *
            apply And.intro
            · intros a b abIn
              apply HHist.1
              left; assumption
            · have H := HHist.2
              apply List.Nodup.of_append_left at H; assumption
          · apply And.intro
            · unfold historical_valid at HHist
              have HHist := HHist.2
              simp at HHist; assumption
            · unfold historical_valid at HHist
              have HHist := HHist.1
              apply HHist
              simp
        · intro Hyp
          have ⟨ old_hist, nodup , new_valid⟩ := Hyp
          simp [historical_valid]
          apply And.intro
          · intros a b mem
            cases mem with
            | inl h => apply old_hist.1; assumption
            | inr h => rw [h]; assumption
          · assumption

--
inductive P2_History_Actions (α ℍ : Type) : Type where
 | Local (ll : P2_Actions α ℍ) : P2_History_Actions α ℍ
 | DupHistory_Actions
      -- Here is an element in epoch
      (epoch : Nat)
      -- This is dependent on the history.
      (n : Nat)(path_p: ISkeleton n)(str_p : Sequence n ((ℍ × ℍ × ℍ) -> Option ChooserSmp))
      -- Element in current
      (m : Nat)(path_q: ISkeleton m)(str_q : Sequence m ((ℍ × ℍ × ℍ) -> Option ChooserSmp))
      --
      : P2_History_Actions α ℍ

structure P1_History_Actions (α ℍ : Type) : Type where
 local_str : P1_Actions α ℍ
 global_str : List (BTree α × ℍ) -> Nat -> {n : Nat} -> ISkeleton n -> (Sequence n (Option (ℍ × ℍ)) × Option α)

def find_first_dup_in_history
   {α ℍ : Type}[DecidableEq α]
   -- We have a list of elements in a tree
   (elems : List (Skeleton × α))
   --
   (hist : List (BTree α × ℍ))
   --
   : Option ( (List (BTree α × ℍ) × (BTree α × ℍ) × List (BTree α × ℍ))
            ×
            (  (List (Skeleton × α) × (Skeleton × α) × List (Skeleton × α))
             × (List (Skeleton × α) × (Skeleton × α) × List (Skeleton × α))
            ))
   := split_at_first_pred
      (fun (e : (BTree α × ℍ)) => find_intersect (·.snd) e.fst.toPaths_elems elems) hist

lemma no_dups_find_first_none {α ℍ : Type}[DecidableEq α]
   -- We have a list of elements in a tree
   (elems : List (Skeleton × α))
   --
   (hist : List (BTree α × ℍ))
   (HDis : List.Disjoint ((hist.map (BTree.toList $ ·.fst)).flatten) (elems.map (·.snd)))
   : find_first_dup_in_history elems hist = .none
   := by simp [find_first_dup_in_history]
         apply splitAtFirstNone'
         intros a aIn
         apply find_intersect_none'
         intro ⟨ skl , e ⟩
         intros sklE
         have hdis := @HDis e (by simp; exists a.1
                                  apply And.intro
                                  exists a.2; rw [<- toPath_elems]; simp; exists skl)
         intros r rIn
         intro Eq ; simp at Eq
         apply hdis
         simp; exists r.1; rw [Eq]; simp; assumption

lemma find_first_dup_in_history_none
   {α ℍ : Type}[DecidableEq α]
   -- We have a list of elements in a tree
   (elems : List (Skeleton × α))
   --
   (hist : List (BTree α × ℍ))
   (HNoFind : find_first_dup_in_history elems hist = .none)
   : List.Disjoint ((hist.map (BTree.toList $ ·.fst)).flatten) (elems.map (·.snd))
   := by apply splitAtFirstNone at HNoFind
         intros a aIn
         simp at aIn
         have ⟨ aBTree , ar , bIn ⟩ := aIn
         have ⟨ x , inHIst ⟩ := ar
         apply HNoFind at inHIst
         apply find_intersect_none at inHIst
         simp at *
         intros Sk inElems
         rw [<- toPath_elems] at bIn
         apply toPaths_elems_skeletons at bIn
         have ⟨ ska , bIn ⟩ := bIn
         have fal := inHIst ska a bIn Sk a inElems
         contradiction

-- lemma find_first_dup_in_history_law {α ℍ : Type}[DecidableEq α]
--    {t : BTree α}
--    {hist : List (BTree α × ℍ)}
--    { pre post : List (BTree α × ℍ) }
--    { oldDA : (BTree α × ℍ) }
--    { oldE currE : Skeleton × α }
--    { preOld posOld preCurr posCurr : List (Skeleton × α) }
--    (H : find_first_dup_in_history t.toPaths_elems hist = .some
--        ( (pre , oldDA,post)
--        , ((preOld, oldE , posOld)
--        , (preCurr , currE ,posCurr)))
--       )
--    : oldDA.1.access oldE.1 = .some (.inl oldE.2)
--    ∧ t.access currE.1 = .some (.inl currE.2)
--    ∧ oldE.2 = currE.2
--    := sorry

def historical_honest_algorith {α ℍ : Type}
  [DecidableEq α]
  [BEq ℍ][Hash α ℍ][m : HashMagma ℍ]
  --
  (val_fun : α -> Bool)
  --
  (history : List (BTree α × ℍ))
  --
  (public_data : BTree α)
  (da_mtree : ℍ)
  --
  : P2_History_Actions α ℍ
  := match find_first_dup_in_history public_data.toPaths_elems history with
    | .some ((pred, _e , _) , ( (_, e1, _) , (_ , e2 , _)) ) =>
      .DupHistory_Actions pred.length
          -- Same as before, we need to choose strategies before playing,
          -- depending on which arbitration games we are playing.
          -- Naive lin forward does not need extra info, but logarithmic
          -- requires more.
          e1.fst.length ⟨ e1.fst , rfl ⟩ naive_lin_forward
          e2.fst.length ⟨ e2.fst , rfl ⟩ naive_lin_forward
    | .none => .Local $ honest_chooser val_fun public_data da_mtree

lemma Nodups_no_dups_in_history {α ℍ}
  [DecidableEq α] [BEq ℍ][Hash α ℍ][m : HashMagma ℍ]
  --
  (val_fun : α -> Bool)
  --
  (history : List (BTree α × ℍ))
  --
  (public_data : BTree α)
  (da_mtree : ℍ)
  --
  -- (HNodup : List.Nodup ((List.map (fun x ↦ x.1.toList) history).flatten ++ public_data.toList))
  (HDis : List.Disjoint ((history.map (BTree.toList $ ·.fst)).flatten) public_data.toList)
  : historical_honest_algorith val_fun history public_data da_mtree
    = .Local (honest_chooser val_fun public_data da_mtree)
  := by simp [historical_honest_algorith]
        rw [no_dups_find_first_none]
        rw [toPath_elems public_data]
        assumption

-- This is the step in our blockchain evolution.
--
def linear_l2_historical_protocol{α ℍ : Type}
  [BEq α] -- Checking dup
  [BEq ℍ][o : Hash α ℍ][HashMagma ℍ]
   (val_fun : α -> Bool)
   (hist : List (BTree α × ℍ))
   --
   (playerOne : P1_History_Actions α ℍ)
   (playerTwo : List (BTree α × ℍ) -> (BTree α × ℍ) -> P2_History_Actions α ℍ)
   --
   : Bool
   := match playerTwo hist playerOne.local_str.da with
   | .DupHistory_Actions
       epoch _fpLen fpSkl fpStr _spLen spSkl spStr
       => match hist[epoch]? with
       -- Get epoch from history
       | .none => true -- Wins POne
       | .some p =>
         -- We play two consecutive membership games
         match elem_in_backward_rev
                  fpSkl
                  p.snd
                  -- Strategies
                  (playerOne.global_str hist epoch fpSkl)  -- Missing Player One Strategy
                  fpStr
             , elem_in_backward_rev
                  spSkl
                  playerOne.local_str.da.snd -- Current Da
                  -- Strategies
                  (playerOne.local_str.gen_elem_str spSkl)
                  spStr
             with
          -- Both games reach values
          | (.Proposer, .some v1) , (.Proposer, .some v2) => v1 != v2
          -- Proposer wins
          | (.Proposer, .none) , _ => true
          | _ , (.Proposer, .none) => true
          -- Chooser wins
          | (.Chooser , _ ) , _ => false
          | _ , (.Chooser, _)   => false

   | .Local act => inner_l2_actions val_fun playerOne.local_str act

-- Historical Honest Valid
theorem history_honest_chooser_no_intersect_hist {α ℍ}
   [BEq ℍ][LawfulBEq ℍ][DecidableEq α]
   [o : Hash α ℍ][m : HashMagma ℍ][InjectiveHash α ℍ][InjectiveMagma ℍ]
   (val_fun : α -> Bool)
   (p1 : P1_History_Actions α ℍ)
   --
   (hist : List (BTree α × ℍ))
   (HHist : List.Nodup (hist.map (BTree.toList $ ·.fst)).flatten)
   --
   : linear_l2_historical_protocol val_fun hist p1
        ( fun h (t, mt) => historical_honest_algorith val_fun h t mt)
   -> List.Nodup ((hist.map (BTree.toList $ ·.fst)).flatten ++ p1.local_str.da.1.toList)
   := by simp [linear_l2_historical_protocol]
         cases HC : historical_honest_algorith val_fun hist p1.local_str.1.1 p1.local_str.1.2 with
         | DupHistory_Actions e n path_n str_n m path_m str_m =>
           _
         | Local ll =>
           simp at *; intro LocalH
           apply List.Nodup.append
           assumption
           sorry -- comes from local valid
           sorry -- comes from find_first_dup_in_history = .none

theorem history_honest_chooser_local_valid {α ℍ}
   [BEq ℍ][LawfulBEq ℍ][DecidableEq α]
   [o : Hash α ℍ][m : HashMagma ℍ][InjectiveHash α ℍ][InjectiveMagma ℍ]
   (val_fun : α -> Bool)
   (p1 : P1_History_Actions α ℍ)
   --
   (hist : List (BTree α × ℍ))
   (HNodups : List.Nodup ((List.map (fun x ↦ x.1.toList) hist).flatten ++ p1.local_str.da.1.toList))
   --
   : linear_l2_historical_protocol val_fun hist p1
        ( fun h (t, mt) => historical_honest_algorith val_fun h t mt)
   -> local_valid p1.local_str.da val_fun
   := by simp [linear_l2_historical_protocol]
         rw [Nodups_no_dups_in_history]
         simp
         rw [<- honest_chooser_valid]
         simp; unfold linear_l2_protocol; unfold inner_l2_actions
         simp
         apply List.disjoint_of_nodup_append
         assumption

theorem history_honest_chooser_valid {α ℍ}
   [BEq ℍ][LawfulBEq ℍ][DecidableEq α]
   [o : Hash α ℍ][m : HashMagma ℍ][InjectiveHash α ℍ][InjectiveMagma ℍ]
   (val_fun : α -> Bool)
   (p1 : P1_History_Actions α ℍ)
   --
   (hist : List (BTree α × ℍ))
   (hist_valid : historical_valid hist val_fun)
   --
   : linear_l2_historical_protocol val_fun hist p1
        (fun h (t, mt) => historical_honest_algorith val_fun h t mt)
   -> historical_valid (hist ++ [p1.local_str.da]) val_fun
   := by
   simp; intro HP; have HP_NoInter := HP; apply history_honest_chooser_no_intersect_hist at HP_NoInter
   rw [historical_concat]
   apply And.intro
   assumption
   apply And.intro
   assumption
   apply history_honest_chooser_local_valid
   assumption; assumption
   have HNodup := hist_valid.2
   assumption
