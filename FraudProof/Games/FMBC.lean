import FraudProof.Games.GenericTree -- Complex Strategies

def cond_hash_elem {α ℍ : Type}[BEq ℍ][LawfulBEq ℍ][h : Hash α ℍ]
  (leaf: ℍ ) (rev : α) (res : ℍ)
   : Bool :=  h.mhash rev == res && leaf == res

def cond_hash { ℍ : Type }[BEq ℍ][mag : HashMagma ℍ] (res l r : ℍ) : Bool
  := mag.comb l r == res

-- Hash Game
abbrev dac_game {ℍ α : Type}[BEq ℍ][LawfulBEq ℍ][Hash α ℍ][HashMagma ℍ]
  (da : CompTree ℍ Unit ℍ)
  (revealer : ABTree (Option α) (Option (ℍ × ℍ)))
  (chooser : ABTree Unit ((ℍ × ℍ × ℍ) -> Option ChooserMoves))
  :=
  treeCompArbGame cond_hash_elem (fun _ => cond_hash) da revealer chooser

theorem winning_prop_hashes {ℍ α : Type}
    [DecidableEq ℍ]
    [Hash α ℍ][HashMagma ℍ]
    -- Public Information
    (da : CompTree ℍ Unit ℍ)
    -- Players
    (revealer : ABTree (Option α) (Option (ℍ × ℍ)))
    (good_revealer : reveler_winning_condition cond_hash_elem (fun _ => cond_hash)
                    da revealer)
    : forall (chooser : ABTree Unit ((ℍ × ℍ × ℍ) -> Option ChooserMoves)),
      treeCompArbGame
         cond_hash_elem (fun _ => cond_hash)
         da revealer chooser
         = Player.Proposer
    := winning_proposer_wins _ _ da revealer good_revealer

def gen_chooser_opt {ℍ : Type}
   -- [DecidableEq ℍ]
   [BEq ℍ]
   (data : Option (ℍ × ℍ) )
   (proposed : ℍ × ℍ × ℍ)
   : Option ChooserMoves
   := data.map ( fun (l , r) =>
     if l == proposed.2.1 ∧ r == proposed.2.2
     then .Now
     else if ¬ l == proposed.2.1
          then .Continue .Left
          else .Continue .Right
   )


theorem winning_gen_chooser {ℍ α : Type}
    [hash : Hash α ℍ][HashMagma ℍ]
    [DecidableEq ℍ]
    -- Public Information
    (pub_data : ABTree ℍ Unit)
    -- Players
    (revealer : ABTree (Option α) (Option (ℍ × ℍ)))(rev_res : ℍ)
    (chooser : ABTree (Option α) (Option (ℍ × ℍ)))(ch_res : ℍ)
    -- Chooser knows the data and hashes do not match
    -- (same_data : @same_hash_leaves _ _ _ h revealer chooser)
    (good_chooser: winning_condition_player
                    (fun c a h => cond_hash_elem c a h)
                    (fun _ (l,r) res => cond_hash res l r)
                    (fun _ => id) ⟨ pub_data , ch_res ⟩ chooser)
    (hneq : ¬ rev_res = ch_res)
    : treeCompArbGame cond_hash_elem (fun _ => cond_hash)
         ⟨ pub_data, rev_res ⟩ revealer (chooser.map (fun _ => ()) gen_chooser_opt)
         = Player.Chooser
    := by
  revert hneq good_chooser ch_res chooser rev_res revealer
  induction pub_data with
  | leaf v =>
    intros revealer rev_res chooser ch_res good_ch hneq
    -- intros revealer rev_res chooser ch_res same_data good_ch hneq
    cases revealer with
    | node _ _ _ => simp [treeCompArbGame]
    | leaf mrev =>
      cases mrev with
      | none => simp [treeCompArbGame]
      | some rev =>
        simp [treeCompArbGame]
        cases chooser with
        | node _ _ _ => simp [winning_condition_player] at good_ch
        | leaf ch =>
        cases ch with
        | none => simp [winning_condition_player] at good_ch
        | some ched =>
          simp [winning_condition_player] at good_ch
          unfold cond_hash_elem at *
          simp at *; intro hrev
          subst_eqs
          rw [good_ch.2]
          intro pp; apply hneq; symm; assumption
  | node _ gl gr HIndL HIndR =>
    intros revealer rev_res chooser ch_res good_ch hneq
    cases revealer with
    | leaf _ => simp [treeCompArbGame]
    | node mp revl revr =>
      cases mp with
      | none =>  simp [treeCompArbGame]
      | some prop =>
        simp [treeCompArbGame]
        cases chooser with
        | leaf _ => simp [winning_condition_player] at good_ch
        | node mch chl chr =>
          cases mch with
          | none => simp [winning_condition_player] at good_ch
          | some ch =>
            simp [winning_condition_player] at good_ch
            simp [gen_chooser_opt]
            split
            case h_1 x heq =>
              injections; rename_i val_eq heq
              rw [ite_eq_iff] at heq
              simp at heq
              cases heq with
              | inl h =>
                simp; unfold cond_hash at *
                have ⟨eq_l ,eq_r⟩ := h
                rw [<- eq_l, <- eq_r]
                simp at good_ch
                rw [good_ch.1]
                simp
                intro a; apply hneq; rw [a]
              | inr h =>
                have ⟨h_some , h_nonsense ⟩ := h
                rw [ite_eq_iff] at h_nonsense
                simp at h_nonsense
            case h_2 x heq =>
              apply HIndL
              -- unfold same_hash_leaves at hsame; exact hsame.1
              exact good_ch.2.1
              simp at heq
              rw [ite_eq_iff] at heq
              simp at heq
              intro a; apply heq.2; rw [a]
            case h_3 x heq =>
              apply HIndR
              -- unfold same_hash_leaves at hsame; exact hsame.2
              exact good_ch.2.2
              simp at heq
              rw [ite_eq_iff] at heq
              simp at heq
              have ⟨ f , a ⟩ := heq
              have fa := f a
              intro b; apply fa; rw [b]
            case h_4 x heq => simp at heq
