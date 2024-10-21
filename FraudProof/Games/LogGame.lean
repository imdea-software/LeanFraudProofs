import FraudProof.Players

import FraudProof.Games.GameDef
import FraudProof.Games.OneStepGame

-- Utils and definitions
import FraudProof.DataStructures.MTree
  import FraudProof.DataStructures.Hash

-- I am sure there is a Lean way to do this.
-- Instead of using axioms, I use 'sorry lemmas' so we can prove them later.
lemma midLtTop { a b : Nat } ( H : a < b ) : (a + b) / 2 < b := by omega
lemma midLtBot {a b : Nat} : a + 1 < b -> a < (a + b) / 2 := by omega
lemma eq_of_lt {a b : Nat} : a < b -> ¬ ( a + 1 < b ) -> a + 1 = b := by omega

-- Game description that works, second stage.
def MembershipGame_2STG {ℍ : Type}
    [BEq ℍ][HashMagma ℍ]
    (pathLen : Nat) (A : Proposer.HC ℍ pathLen) (D : Chooser.Player ℍ)
    (pNZ : 0 < pathLen)
    -- → ( H_bot : p_bot < p_top )
    -- → ( H_top : p_top < n + 1 )
    -- →
    (h_bot h_top : ℍ) : Winner
    :=
    match pathLen with
    -- Impossible case
    | Nat.zero => by simp at pNZ
    | Nat.succ Nat.zero =>
      GameOneStep A h_bot h_top
    | Nat.succ (Nat.succ g) =>
      let mid := (g / 2) + 1
      have midLtGL : mid < g.succ.succ := by omega
      let h_mid := A.pathNode ⟨ mid , by apply Nat.lt_succ_of_lt; assumption ⟩
      let left_Proposer := Proposer.takeHC ℍ mid (by omega) A
      let right_Proposer := Proposer.dropHC ℍ mid (by omega) A
        match D.strategy h_bot h_mid h_top with
            | Chooser.Side.Left =>
                MembershipGame_2STG mid left_Proposer D (by simp) h_bot h_mid
            | Chooser.Side.Right =>
                MembershipGame_2STG (g.succ.succ - mid) right_Proposer D (by simp; assumption) h_mid h_top
     -- if hC : (p_bot + 1 < p_top)
     -- then -- Following the path
     --    have midLtTopP := by trans p_top; exact midLtTop HBot; assumption
     --    let p_mid := (p_bot + p_top) / 2 -- middle position
     --    let h_mid := A.pathNode ⟨ p_mid , midLtTopP ⟩
     --    match D.strategy h_bot h_mid h_top with
     --        | Chooser.Side.Left => MembershipGame_2STG A D p_bot p_mid (midLtBot hC)  midLtTopP h_bot h_mid
     --        | Chooser.Side.Right => MembershipGame_2STG A D p_mid p_top (midLtTop HBot) HTop h_mid h_top
     -- else -- Final one-step game
     -- -- From Hyps, p_bot + 1 = p_top
     --   have BotTopEq : p_bot + 1 = p_top := eq_of_lt HBot hC
     --   MembershipGame_OneStep n A ⟨ p_bot , by rw [ <- BotTopEq ] at HTop; simp at HTop; assumption ⟩ h_bot h_top

-- Protocol
-- Note Cesar add value to the interface or change the name?
def MembershipGame {ℍ : Type}
    [BEq ℍ][HashMagma ℍ]
    (n : Nat) (nNZ : 0 < n) (A : Proposer.HC ℍ n) (D : Chooser.Player ℍ) (bHash tHash : ℍ) : Winner
  := MembershipGame_2STG n A D nNZ bHash tHash
