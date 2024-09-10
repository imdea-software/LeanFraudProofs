import FraudProof.Players

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

namespace BotUpLin

  open Challenger
  open Challenged

  -- The following game checks that a the Challenger knows a path from |hashInit| to |hashLast|
  def HashPathCheck
    -- Length
    (len : Nat)
    (hashLast : Hash )
    -- Players
    (A : HC len) ( D : Challenged )
    -- two hashes
    (h_head h_last : Hash)
    --
    (pos : Nat) ( posLt : pos < len )
    : Winner
  :=
    if posCheck : pos < len - 1
    then
        let nHash := A.pathNode ⟨ pos + 1 , by apply Nat.succ_lt_succ; assumption ⟩ -- trans len-1;assumption; exact Nat.sub_lt_succ _ _⟩
        match D.strategy h_head nHash h_last with
        | .Left => -- OneStep Game
            if opHash h_head (A.pathSib ⟨ pos , posLt ⟩) = nHash
            then Winner.Challenger
            else Winner.Challenged
        | .Right => HashPathCheck _  hashLast A D nHash h_last (pos + 1) (by exact Nat.succ_lt_of_lt_pred posCheck)
    else
        if h_last = hashLast
        then Winner.Challenger
        else Winner.Challenged

  def InitHashPathGame
    -- Length
    (len : Nat) (lenNZ : 0 < len)
    (hashInit hashLast : Hash )
    -- Players
    (A : HC len) ( D : Challenged )
    : Winner
    := HashPathCheck len hashLast A D hashInit hashLast 0 lenNZ

end BotUpLin

-- match len with
--   | Nat.zero => -- Impossible case
--     by simp at posLt
--     -- MembershipGame_OneStep A 0 _ h_last h_head
--   | Nat.succ p =>
--     let pLtAInit : p < L := by
--       { simp at rangeH
--         transitivity (Nat.succ p)
--         simp
--         exact rangeH
--       }
--     let nH := A.hashStr.node _ -- { val := p , isLt := pLtAInit }
--     match D.strategy h_last nH h_head with
--     | Side.Left =>
--         MembershipGame_OneStep A p pLtAInit h_last nH
--     | Side.Right =>
--         _ -- LinMembershipGame A D h_head nH p pLtAInit

-- /- We can focus on proving that a /Good Challenger/, the one we defined, wins
--   all small games. -/
