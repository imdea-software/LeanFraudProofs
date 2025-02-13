import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Games.Base.GenericTree -- Generic Games
import FraudProof.Games.Base.FromBtoMTree -- Tree Arb Game Game trees

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
     | .leaf p , .leaf lp , .leaf _rp =>
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
     | .leaf _ ,  _ , .node _ _ _ => .Left
     | .node _ _ _, .leaf _ , _ => .Right
     | .node _ _ _,  _ , .leaf _ => .Left

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
         ⟨ pub.toB , lplayer_commit⟩ lplayer
         (rplayer.map id gen_to_chooser) = Player.Proposer
    ↔
    simultaneous_game pub lplayer lplayer_commit rplayer = .Left )
    ∧
    (treeArbitrationGame ⟨ pub.toB , lplayer_commit⟩ lplayer
        (rplayer.map id gen_to_chooser) = Player.Chooser
        ↔
    simultaneous_game pub lplayer lplayer_commit rplayer = .Right)
    := sorry

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
         if op_side side lplayer_commit.1 lp = lplayer_commit.2
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
