import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.MTree
import FraudProof.DataStructures.Sequence

import FraudProof.L2

----------------------------------------
-- ## Stateful Protocol. -- WIP
-- Now we have a history of all previous accepted batches.

def historical_valid
  {α ℍ : Type} [DecidableEq α][Hash α ℍ][HashMagma ℍ]
  --
  (Hist : List (BTree α × ℍ))
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
    ∧ find_intersect id (hist.map (BTree.toList $ ·.fst)).flatten new.fst.toList = .none
    ∧ local_valid new val_fun)
  := sorry

inductive P2_History_Actions (α ℍ : Type) : Type where
 | Local (ll : P2_Actions α ℍ) : P2_History_Actions α ℍ
 | DupHistory_Actions
      -- Here is an element in epoch
      (epoch : Nat) -- This is depentent on the history.
      ( n : Nat )(path_p: ISkeleton n) (str_p : Sequence n ((ℍ × ℍ × ℍ) -> Option ChooserSmp))
      --
      (m : Nat)(path_q: ISkeleton m)(str_q : Sequence m ((ℍ × ℍ × ℍ) -> Option ChooserSmp))
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

lemma find_first_dup_in_history_law {α ℍ : Type}[DecidableEq α]
   {t : BTree α}
   {hist : List (BTree α × ℍ)}
   { pre post : List (BTree α × ℍ) }
   { oldDA : (BTree α × ℍ) }
   { oldE currE : Skeleton × α }
   { preOld posOld preCurr posCurr : List (Skeleton × α) }
   (H : find_first_dup_in_history t.toPaths_elems hist = .some
       ((pre , oldDA,post)
       , ((preOld, oldE , posOld) , (preCurr , currE ,posCurr)))
      )
   : oldDA.1.access oldE.1 = .some (.inl oldE.2)
   ∧ t.access currE.1 = .some (.inl currE.2)
   ∧ oldE.2 = currE.2
   := sorry

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
        ( fun h (t, mt) => historical_honest_algorith val_fun h t mt)
     ↔ historical_valid (hist ++ [p1.local_str.da]) val_fun
   := by
   apply Iff.intro
   · simp at *
     intro HProtocol
     rw [historical_concat]
     apply And.intro
     · assumption
     · apply And.intro
       · unfold linear_l2_historical_protocol at HProtocol
         simp at HProtocol
         split at HProtocol

         case h_1 x epoc _fpLen fpSkl fpStr _spLen spSkl spStr heq =>
          simp [historical_honest_algorith] at heq
          cases ffind : find_first_dup_in_history p1.local_str.da.1.toPaths_elems hist with
          | none => rw [ffind] at heq; simp at heq
          | some ps =>
            rw [ffind] at heq; simp at heq
            have dup_hist_law := find_first_dup_in_history_law ffind
            unfold find_first_dup_in_history at ffind
            apply splitAtFirstLaw at ffind
            have histDef := ffind.1
            have histLength := heq.1
            rw [<- histLength, histDef] at HProtocol

            have getLemma :
               (ps.1.1 ++ [ps.1.2.1] ++ ps.1.2.2)[ps.1.1.length]?
               = ps.1.2.1 := by sorry
            rw [getLemma] at HProtocol; simp at HProtocol
            -- have pastDA := ps.1.2.1
            -- have pastElem := ps.2.1.2.1
            have accesed := dup_hist_law.1; rw [access_iaccess] at accesed
            have HWinning := @elem_back_rev_honest_two α ℍ _ _ _ _ _ _ _ _
                                                _ -- (wit.pathInfo.map (fun p => p.side))
                                                ps.1.2.1.2 ps.2.1.2.1.2 (p1.global_str hist epoc (sequence_lift ps.2.1.2.1.1) )
                                                ps.1.2.1.1 (by
                                                          sorry -- this is correct we need to apply hist_valid
                                                          ) accesed -- dup_hist_law.left

            subst_eqs; simp at *
            cases HWinning

         case h_2 x act heq =>
          _
       · _

   · _
