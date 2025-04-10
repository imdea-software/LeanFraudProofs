import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.GenericTree -- Generic Games
import FraudProof.Games.FromBtoMTree -- Tree Arb Game Game trees

inductive SimWinner where
 | Left | Right

@[simp]
def leaf_game{α ℍ : Type}[DecidableEq ℍ][o : Hash α ℍ]
  (a : α)(p commit : ℍ)
  : SimWinner
 := if o.mhash a = p ∧ commit = p then .Left else .Right

@[simp]
def node_game {ℍ : Type}[DecidableEq ℍ]
  [mag : HashMagma ℍ]
  (lp rp : ℍ × ℍ)
  (commit : ℍ)
  (recl recr : SimWinner)
  : SimWinner
 := if lp = rp
    then -- Now challenge
      if mag.comb lp.1 lp.2 = commit then .Left else .Right
    else
      if ¬ lp.1 = rp.1 then recl else recr

-- Merkle Tree Arbitration Game!
def simultaneous_game {α ℍ : Type}
  [o : Hash α ℍ][mag : HashMagma ℍ]
  [DecidableEq ℍ] -- This is BEq ℍ and LawfulBEq
  (public_data : ABTree ℍ Unit)
  -- Player 1
  (lplayer : ABTree (Option α) (Option (ℍ × ℍ)))
  (lplayer_commit : ℍ)
  -- Player 2 -- not symmetric game.
  (rplayer : ABTree Unit (Option (ℍ × ℍ)))
  --
  : SimWinner
  := match public_data, lplayer , rplayer with
     | .leaf p , .leaf lp , _ =>
       match lp with
         | .none => .Right
         | .some llp =>
         -- Leaf condition
         leaf_game llp p lplayer_commit
     | .node _ gl gr, .node lp ll lr, .node rp rl rr =>
       match lp , rp with
       | .none , _ => .Right
       | _ , .none => .Left
       | .some lp, .some rp =>
        node_game lp rp lplayer_commit
           (simultaneous_game gl ll lp.1 rl)
           (simultaneous_game gr lr lp.2 rr)
     -------
     | .leaf _ , .node _ _ _, _ => .Right
     -- | .leaf _ , .leaf .none , _ => .Right
     -- | .leaf _ , .leaf (.some _) , .node _ _ _ => .Left
     | .node _ _ _, .leaf _ , _ => .Right
     | .node _ _ _, .node (.some _) _ _ , .leaf _ => .Left
     | .node _ _ _, .node .none _ _ , .leaf  _ => .Right

def gen_to_chooser {ℍ : Type}[DecidableEq ℍ]
  (md : Option (ℍ × ℍ)) (a : ℍ × ℍ × ℍ) : Option ChooserMoves
  := md.map (fun d =>
     if d = a.2 then .Now
     else if ¬ d.1 = a.2.1
          then .Continue .Left
          else .Continue .Right
      )
theorem eq_sim_games {α ℍ : Type}
  [o : Hash α ℍ][mag : HashMagma ℍ]
  [DecidableEq ℍ] -- This is BEq ℍ and LawfulBEq
   (pub : ABTree ℍ Unit)
   -- Player 1
   (lplayer : ABTree (Option α) (Option (ℍ × ℍ)))
   (lplayer_commit : ℍ)
   -- Player 2 -- not symmetric game.
   (rplayer : ABTree Unit (Option (ℍ × ℍ)))
  : ( treeArbitrationGame
         ⟨ pub , lplayer_commit⟩ lplayer
         (rplayer.map id gen_to_chooser) = Player.Proposer
    ↔
    simultaneous_game pub lplayer lplayer_commit rplayer = .Left )
    -- ∧
    -- (treeArbitrationGame ⟨ pub.toB , lplayer_commit⟩ lplayer
    --     (rplayer.map id gen_to_chooser) = Player.Chooser
    --     ↔
    -- simultaneous_game pub lplayer lplayer_commit rplayer = .Right)
    := by
    apply Iff.intro
    -- Tree imples simultaneous
    · revert rplayer lplayer_commit lplayer
      induction pub with
      | leaf v =>
        intros lplayer cmt rplayer treeComp
        cases lplayer with
        | node _ _ _ =>
          simp [treeCompArbGame] at treeComp
        | leaf p =>
          cases p with
          | none => simp [treeCompArbGame] at treeComp
          | some p =>
            cases rplayer with
            | node _ _ _ =>
            simp [simultaneous_game]
            simp [treeArbitrationGame, treeCompArbGame] at treeComp
            apply And.intro
            · exact treeComp.1
            · symm; exact treeComp.2
            | leaf _ =>
                simp [treeCompArbGame] at treeComp
                simp [simultaneous_game]
                apply And.intro; exact treeComp.1;symm;exact treeComp.2
      | node _ gl gr HIndL HIndR =>
        intros lplayer cmt rplayer treeComp
        cases lplayer with
        | leaf _ => simp [treeCompArbGame] at treeComp
        | node mprop lpl lpr =>
          cases mprop with
          | none =>  simp [treeCompArbGame] at treeComp
          | some prop =>
            cases rplayer with
            | leaf _ => simp [simultaneous_game]
            | node rp rpl rpr =>
              match rp with
              | none =>  simp [simultaneous_game]
              | some rpv =>
              simp [simultaneous_game]
              simp [treeCompArbGame, gen_to_chooser] at treeComp
              split
              case isTrue eq => subst_eqs; simp at *; assumption
              case isFalse neq =>
                split
                case isTrue eq1 =>
                 -- subst_eqs; simp at *
                 simp at *
                 apply HIndR
                 have comp : some (if rpv = prop then ChooserPrimMoves.Now else if rpv.1 = prop.1 then ChooserPrimMoves.Continue Side.Right else ChooserPrimMoves.Continue Side.Left) = ChooserPrimMoves.Continue Side.Right
                   := by {
                   clear HIndR HIndL; simp; rw [ite_eq_iff]
                   right
                   apply And.intro
                   · intro pp; apply neq; rw [pp]
                   · rw [eq1]; simp
                   }
                 rw [comp] at treeComp ; simp at treeComp
                 assumption
                case isFalse neq2 =>
                 apply HIndL
                 have comp :some (if rpv = prop then ChooserPrimMoves.Now else if rpv.1 = prop.1 then ChooserPrimMoves.Continue Side.Right else ChooserPrimMoves.Continue Side.Left) = ChooserPrimMoves.Continue Side.Left
                   := by {
                     simp; rw [ite_eq_iff]
                     right
                     apply And.intro
                     · intro pp; apply neq; rw [pp]
                     · simp; intro pp; apply neq2; rw [pp]
                   }
                 rw [comp] at treeComp; simp at treeComp
                 simp
                 assumption
    · revert rplayer lplayer_commit lplayer
      induction pub with
      | leaf b =>
        intros lplayer cmt rplayer simG
        cases lplayer with
        | node _ _ _ => simp [simultaneous_game] at simG
        | leaf mp =>
         cases mp with
         | none =>
           unfold simultaneous_game at simG
           cases rplayer
           all_goals { simp at simG }
         | some p =>
           simp [simultaneous_game] at simG
           simp [treeCompArbGame]
           apply And.intro
           · exact simG.1
           · symm; exact simG.2
      | node _ gl gr HIndL HIndR =>
        intros lplayer cmt rplayer simG
        cases lplayer with
        | leaf _ => simp [simultaneous_game] at simG
        | node mp lpl lpr =>
          cases mp with
          | none =>
            unfold simultaneous_game at simG;simp at simG
            cases rplayer
            all_goals { simp at simG }
          | some p =>
            cases rplayer with
            | leaf _ => simp [treeCompArbGame]
            | node mrp rpl rpr =>
              cases mrp with
              | none => simp [treeCompArbGame, gen_to_chooser]
              | some rp =>
              simp [simultaneous_game] at simG
              simp [treeCompArbGame, gen_to_chooser]
              split
              case h_1 x heq =>
                simp; injections; rename_i val_eq
                rw [ite_eq_iff] at val_eq; simp at val_eq
                cases val_eq with
                | inl eq =>
                  subst_eqs; simp at simG; assumption
                | inr rest =>
                  have nonsense := rest.2
                  rw [ite_eq_iff] at nonsense
                  simp at nonsense
              case h_2 x heq =>
                simp at heq
                rw [ite_eq_iff] at heq
                cases heq with
                | inl ff => simp at ff
                | inr hyp =>
                  simp at HIndL
                  apply HIndL
                  clear HIndL HIndR
                  -- have cf : (p = rp) = False := sorry
                  rw [ite_cond_eq_false] at simG
                  have ⟨ neq , neq1 ⟩ := hyp
                  simp at neq1
                  rw [ite_cond_eq_false] at simG
                  assumption
                  simp; intro pp; apply neq1; rw [pp]
                  simp; intro pp; apply hyp.1; rw [pp]
              case h_3 x heq =>
                simp at heq
                rw [ite_eq_iff] at heq
                simp at heq
                simp at HIndR
                apply HIndR
                clear HIndR HIndL
                rw [ite_eq_iff] at simG; simp at simG
                cases simG
                case a.inl h => tauto
                case a.inr h => replace h := h.2; rw [heq.2] at h; simp at h; assumption
              case h_4 x heq => simp at heq

-- Elemen In Tree
def simultaneous_elemenin_game {α ℍ : Type}
  [o : Hash α ℍ][mag : HashMagma ℍ]
  [DecidableEq ℍ] -- This is BEq ℍ and LawfulBEq
  (public_data : ABTree SkElem Unit)
  -- Player 1
  (lplayer : ABTree (Option α) (Option ℍ))
  (lplayer_commit : (ℍ × ℍ))
  -- Player 2 -- not symmetric game.
  (rplayer : ABTree Unit (Option ℍ))
  --
  : SimWinner
  := match public_data, lplayer , rplayer with
     | .leaf side , .leaf lp , .leaf _rp =>
       match lp with
       | .none => .Right
       | .some lp =>
         if op_side side lplayer_commit.1 (o.mhash lp) = lplayer_commit.2
         then .Left else .Right
     | .node _ gl gr, .node lp ll lr, .node rp rl rr =>
       match lp, rp with
       | .none , _ => .Right
       | _ , .none => .Left
       | .some lp, .some rp =>
        if lp = rp
        then simultaneous_elemenin_game gl ll (lplayer_commit.1 , lp) rl
        else simultaneous_elemenin_game gr lr (lp,lplayer_commit.2) rr
     -------
     | .leaf _ , .node _ _ _, _ => .Right
     | .leaf _ ,  _ , .node _ _ _ => .Left
     | .node _ _ _, .leaf _ , _ => .Right
     | .node _ _ _,  _ , .leaf _ => .Left

-- * Data Rev
-- def simultaneous_data_rev_game {α ℍ : Type}
--   [o : Hash α ℍ][mag : HashMagma ℍ]
--   [DecidableEq ℍ] -- This is BEq ℍ and LawfulBEq
--   (len : Nat)
--   -- Player 1
--   (lplayer : ABTree (Option α) (Option (ℍ × ℍ)))
--   (lplayer_commit : ℍ)
--   -- Player 2 -- not symmetric game.
--   (rplayer : ABTree (Option α) (Option (ℍ × ℍ)))
--   (rplayer_commit : ℍ)
--   --
--   (hneq : ¬ lplayer_commit = rplayer_commit)
--   --
--   : Option SimWinner :=
--   match len with
--   | .zero =>
--     match lplayer , rplayer with
--     | .leaf lv ,.leaf lr => sorry
--     | .leaf _ , _ => .some .Left
--     | _ , .leaf _ => .some .Right
--     | _ , _ => .none
--   | .succ plen with
--     match lplayer , rplayer with
--     | .node ln ll lr, .node rn rl rr => sorry
--     | .leaf _ , .node _ _ _ => .some .Rigth
--     | .node _ _ _ , .leaf _ => .some .Left
--     | _ , _ => .none
