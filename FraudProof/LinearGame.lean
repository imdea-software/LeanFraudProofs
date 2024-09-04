import FraudProof.Challenger
import FraudProof.Challenged
import FraudProof.GameDef
import FraudProof.OneStepGame
-- Utils and definitions
import FraudProof.MTree
import FraudProof.Hash

import Mathlib.Order.Basic

/-! # Linear Membership Challenge Games
  The idea here is to simplify proofs.-/
/-
  Linear challenges are not part of Marga's original ideas, but I think that
Log games are just optimizations.-/
/-
  However, instead of jumping to prove optimizations, I'll try first to prove
the stupid versions and then form bridges between games.
-/

def LinMembershipGame
  -- Length
  {len : Nat}
  -- Players
  (A : Challenger len) ( D : Challenged )
  -- two hashes
  (h_head h_last : Hash)
  --
  (pos : Nat) { pos ≤ len }
  : Winner
:= match len with
  | Nat.zero =>
    MembershipGame_OneStep A 0 _ h_last h_head
  | Nat.succ p =>
    let pLtAInit : p < A.init.pL := by
      { simp at rangeH
        transitivity (Nat.succ p)
        simp
        exact rangeH
      }
    let nH := A.strategy { val := p , isLt := pLtAInit }
    match D.strategy h_last nH h_head with
    | Side.Left =>
        MembershipGame_OneStep A p pLtAInit h_last nH
    | Side.Right =>
        LinMembershipGame A D h_head nH p pLtAInit

/- We can focus on proving that a /Good Challenger/, the one we defined, wins
  all small games. -/
