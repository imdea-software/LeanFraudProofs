import FraudProof.Games.Base.GenericTree -- Complex Strategies

def cond_hash_elem {ℍ α : Type}[BEq ℍ][LawfulBEq ℍ][h : Hash α ℍ] (leaf: ℍ) (rev : α) (res : ℍ)
   : Bool :=  h.mhash rev == leaf && leaf == res

def cond_hash { ℍ : Type }[BEq ℍ][mag : HashMagma ℍ] (res l r : ℍ) : Bool
  := mag.comb l r == res

-- Hash Game
abbrev dac_game {ℍ α : Type}[BEq ℍ][LawfulBEq ℍ][Hash α ℍ][HashMagma ℍ]
  (da : CompTree ℍ Unit ℍ)
  (reveler : ABTree (Option α) (Option (ℍ × ℍ)))
  (chooser : ABTree Unit ((ℍ × ℍ × ℍ) -> Option ChooserMoves))
  :=
  treeCompArbGame cond_hash_elem (fun _ => cond_hash) da reveler chooser

theorem winning_prop_hashes {ℍ α : Type}
    [BEq ℍ][LawfulBEq ℍ]
    [Hash α ℍ][HashMagma ℍ]
    -- Public Information
    (da : CompTree ℍ Unit ℍ)
    -- Players
    (reveler : ABTree (Option α) (Option (ℍ × ℍ)))
    (good_reveler : reveler_winning_condition cond_hash_elem (fun _ => cond_hash) da reveler)
    : forall (chooser : ABTree Unit ((ℍ × ℍ × ℍ) -> Option ChooserMoves)),
      treeCompArbGame
         cond_hash_elem (fun _ => cond_hash)
         da reveler chooser
         = Player.Proposer
    := winning_proposer_wins _ _ da reveler good_reveler

def gen_chooser_opt {ℍ : Type}
   [BEq ℍ]
   ( data : Option (ℍ × ℍ) )
   (proposed : ℍ × ℍ × ℍ)
   : Option ChooserMoves
   := data.map ( fun (l , r) =>
     if l == proposed.2.1 && r == proposed.2.2
     then .Now
     else if l != proposed.2.1 then .Continue .Left
     else .Continue .Right
   )

theorem winning_gen_chooser {ℍ α : Type}
    [BEq ℍ][LawfulBEq ℍ]
    [h : Hash α ℍ][HashMagma ℍ]
    --
    [collres : CollResistant α ℍ]
    [hash_props : SLawFulHash ℍ]
    -- Public Information
    (pub_data : ABTree ℍ Unit)
    -- Players
    (reveler : ABTree (Option α) (Option (ℍ × ℍ)))
    (rev_res : ℍ)
    --
    (chooser : ABTree (Option α) (Option (ℍ × ℍ)))
    (ch_res : ℍ)
    (good_chooser: reveler_winning_condition cond_hash_elem (fun _ => cond_hash) ⟨ pub_data , ch_res ⟩ chooser)
    (hneq : ¬ rev_res = ch_res)
    : treeCompArbGame
         cond_hash_elem (fun _ => cond_hash)
         ⟨ pub_data, rev_res ⟩ reveler (chooser.map (fun _ => ()) gen_chooser_opt)
         = Player.Chooser
    := by
  revert hneq good_chooser ch_res chooser rev_res reveler
  induction pub_data with
  | leaf v =>
    intros reveler rev_res chooser ch_res good_ch hneq
    cases reveler with
    | node _ _ _ => simp [treeCompArbGame]
    | leaf mrev =>
      cases mrev with
      | none => simp [treeCompArbGame]
      | some rev =>
        simp [treeCompArbGame]
        cases chooser with
        | node _ _ _ => simp [reveler_winning_condition] at good_ch
        | leaf ch =>
        cases ch with
        | none => simp [reveler_winning_condition] at good_ch
        | some ched =>
          simp [reveler_winning_condition] at good_ch
          unfold cond_hash_elem at *
          simp at good_ch
          simp
          intro h
          have ⟨ hchev , hvres ⟩ := good_ch
          rw [hvres]
          intro a; apply hneq; rw [a]
  | node _ gl gr HIndL HIndR =>
    intros reveler rev_res chooser ch_res good_ch hneq
    cases reveler with
    | leaf _ => simp [treeCompArbGame]
    | node mp revl revr =>
      cases mp with
      | none =>  simp [treeCompArbGame]
      | some prop =>
        simp [treeCompArbGame]
        cases chooser with
        | leaf _ => simp [reveler_winning_condition] at good_ch
        | node mch chl chr =>
          cases mch with
          | none => simp [reveler_winning_condition] at good_ch
          | some ch =>
            simp [reveler_winning_condition] at good_ch
            simp [gen_chooser_opt]
            split
            case h_1 x heq => sorry
            case h_2 x heq => apply HIndL; exact good_ch.2.1; sorry
            case h_3 x heq => apply HIndR; exact good_ch.2.2; sorry
            case h_4 x heq => simp at heq
