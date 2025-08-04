import FraudProof.Games.GameDef -- Players, Winner

import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

import FraudProof.Games.GenericTree -- Generic Game

----------------------------------------
-- * BTree as hashes.
-- We know the structure of the data plus the hashes of their leaves.
structure ComputationTree (α ℍ : Type) where
  computation : BTree α -- Btree in this case, in can be generalized
  res : ℍ
  -- {𝔸}, fold 𝔸_hash computation = res
  -- one binary operation and leafs (In this case, that's why BTree)
----------------------------------------

def dac_leaf_winning_condition {α ℍ : Type} [BEq ℍ]
  [o : Hash α ℍ](hc : ℍ) (a : α)(h : ℍ) : Bool := o.mhash a == hc ∧ h == hc

def dac_node_winning_condition {ℍ : Type} [BEq ℍ]
  [m : HashMagma ℍ] (top hl hr : ℍ) : Bool := m.comb hl hr == top
@[simp]
def data_challenge_game{α ℍ : Type}
    [BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
    (da : ComputationTree ℍ ℍ)
    --
    (reveler : ABTree (Option α) (Option (ℍ × ℍ)) )
    (chooser : ABTree Unit (ℍ × ℍ × ℍ -> Option ChooserMoves))
    --
    : Winner :=
    @treeCompArbGame ℍ α Unit ℍ
      -- Leaf winning condition
      dac_leaf_winning_condition
      -- Node winning condition
      (fun _  =>  dac_node_winning_condition)
      -- DA
      ⟨ da.computation , da.res ⟩
      -- Revelear Strategy
      reveler
      -- Chooser Strategy
      (ABTree.map
        (fun _ => ())
        (fun fhs ⟨hrs , hl , hr ⟩ => fhs ⟨ hrs, hl , hr ⟩)
        chooser)

theorem dac_winning_gen_chooser {α ℍ : Type}
    [hash : Hash α ℍ][HashMagma ℍ]
    -- Hash equality depends on collision free hashes.
    [BEq ℍ][LawfulBEq ℍ]
    --
    -- Public Information
    (pub_data : ABTree ℍ Unit)
    -- Players
    (revealer : ABTree (Option α) (Option (ℍ × ℍ)))(rev_res : ℍ)
    (chooser : ABTree (Option α) (Option (ℍ × ℍ)))(ch_res : ℍ)
    -- Chooser knows the data and hashes do not match
    (good_chooser: winning_condition_player
                    (fun hc a h => dac_leaf_winning_condition hc a h)
                    (fun _ (l,r) res => dac_node_winning_condition res l r)
                    (fun _ => id) ⟨ pub_data , ch_res ⟩ chooser)
    (hneq : ¬ rev_res = ch_res)
    : data_challenge_game ⟨ pub_data , rev_res ⟩
         revealer (chooser.map (fun _ => ()) gen_chooser_opt)
         = Player.Chooser
    := by
    revert hneq good_chooser ch_res chooser rev_res revealer
    induction pub_data with
    | leaf v =>
      intros revealer rev_res chooser ch_res good_chooser hneq
      simp
      cases revealer with
      | node _ _ _ => simp [treeCompArbGame]
      | leaf rv =>
        cases rv with
        | none => simp [treeCompArbGame]
        | some rv =>
          simp [treeCompArbGame]
          simp at good_chooser
          cases chooser with
          | node _ _ _ => simp [winning_condition_player] at good_chooser
          | leaf mcv =>
            cases mcv with
            | none => simp [winning_condition_player] at good_chooser
            | some cv =>
              simp [winning_condition_player] at good_chooser
              unfold dac_leaf_winning_condition at *
              -- Here, we do not need collision resistant, because we use logic.
              -- I won't challenge a hash that it seems correct. Maybe the other
              -- player only knows a collisition but not the real value.
              simp at good_chooser
              conv => lhs; simp; rw [Bool.and_comm]
              simp
              intro hrev_v
              subst_eqs
              tauto
    | node v bl br HL HR =>
      intros revealer rev_res chooser ch_res good_chooser hneq
      simp
      cases revealer with
      | leaf _ => simp [treeCompArbGame]
      | node mrev rev_left rev_right =>
        cases mrev with
        | none => simp [treeCompArbGame]
        | some rev =>
         simp [treeCompArbGame]
         cases chooser with
         | leaf _ =>
           clear HL HR
           simp [winning_condition_player] at good_chooser
         | node mch ch_left ch_right =>
           simp
           cases mch with
           | none =>
             clear HL HR
             simp [winning_condition_player] at good_chooser
           | some ch =>
             simp [winning_condition_player] at good_chooser
             have gdac := good_chooser.1; simp [dac_node_winning_condition] at gdac
             simp [gen_chooser_opt]
             split
             case h_1 x heq =>
               apply Option.some.inj at heq
               rw [ite_eq_iff] at heq
               simp at heq
               cases heq
               case inl h =>
                 simp [dac_node_winning_condition]
                 subst_eqs
                 rw [h.1,h.2] at hneq
                 tauto
               case inr h =>
                 replace h := h.2
                 rw [ite_eq_iff] at h
                 simp at h

             case h_2 x heq =>
               apply Option.some.inj at heq
               rw [ite_eq_iff] at heq
               simp at heq
               simp [data_challenge_game] at HL
               apply HL
               -- Proof obligations.
               exact good_chooser.2.1
               tauto

             case h_3 x heq =>
               apply Option.some.inj at heq
               rw [ite_eq_iff] at heq
               simp at heq
               simp [data_challenge_game] at HR
               apply HR
               -- Proof obligations.
               exact good_chooser.2.2
               tauto

             case h_4 x heq =>
               clear HL HR
               simp at heq

@[simp]
def treeArbitrationGame {α ℍ : Type}
    [BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
    (da : ComputationTree ℍ ℍ)
    --
    (reveler : ABTree (Option α) (Option (ℍ × ℍ)) )
    (chooser : ABTree Unit (ℍ × ℍ × ℍ -> Option ChooserMoves))
    --
    : Winner :=
    @treeCompArbGame ℍ α Unit ℍ
      -- Leaf winning condition
      (fun ha data res => (o.mhash data == ha) ∧ (ha == res))
      -- Node winning condition
      (fun _ r hl hr =>  m.comb hl hr == r)
      -- DA
      ⟨ da.computation , da.res ⟩
      -- Revelear Strategy
      reveler
      -- Chooser Strategy
      (ABTree.map
        (fun _ => ())
        (fun fhs ⟨hrs , hl , hr ⟩ => fhs ⟨ hrs, hl , hr ⟩)
        chooser)
----------------------------------------

@[simp]
def arbitrationTree {α ℍ : Type}
    [BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
    (arena : ABTree Unit Unit)
    (res : ℍ)
    --
    (reveler : ABTree (Option α) (Option (ℍ×ℍ)) )
    (chooser : ABTree Unit (ℍ × ℍ × ℍ -> Option ChooserMoves))
    --
    : Winner :=
    @treeCompArbGame Unit α Unit ℍ
      -- Leaf winning condition
      (fun _ a hres => o.mhash a == hres)
      -- Node winning condition
      (fun _ r hl hr =>  m.comb hl hr == r)
      -- DA
      ⟨ arena , res ⟩
      -- Revelear Strategy
      reveler
      -- Chooser Strategy
      (ABTree.map (fun _ => ()) (fun fhs ⟨hrs , hl , hr ⟩ => fhs ⟨ hrs, hl , hr ⟩) chooser)

