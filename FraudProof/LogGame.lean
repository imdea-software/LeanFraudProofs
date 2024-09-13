import FraudProof.Players

import FraudProof.GameDef
import FraudProof.OneStepGame
-- Utils and definitions
import FraudProof.MTree
import FraudProof.Hash

-- I am sure there is a Lean way to do this.
axiom midLt { a b : Nat } ( H : b < a ) : (a + b) / 2 < a
axiom midLess { a b M : Nat }
  : a < M → b < a → ( a + b ) / 2 < M
axiom midLessEqLt { a b M : Nat }
  : a ≤ M → b < a → ( a + b ) / 2 < M
axiom midLessEqLeq { a b M : Nat }
  : a ≤ M → b < a → ( a + b ) / 2 ≤ M
axiom midGt { a b : Nat }
  : a < b → a < (  b + a ) / 2


-- Game description that works, second stage.
def MembershipGame_2STG { n : Nat }(A : Proposer.HC n) (D : Chooser.Player)
    : (p_bot p_top : Nat)
    → ( H_bot : p_bot < n )
    → ( H_top : p_top < p_bot )
    → (h_bot h_top : Hash)
    → Winner
     := fun p_bot p_top HBot HTop h_bot h_top =>
     if (p_bot > (p_top + 1))
     then -- Following the path
           let p_mid := (p_bot + p_top) / 2 -- middle position
           let h_mid := A.pathNode sorry -- A.hashStr.node { val := p_mid , isLt := by exact midLess HBot HTop}
           match D.strategy h_bot h_mid h_top with
             | Chooser.Side.Left => MembershipGame_2STG A D p_bot p_mid  HBot ( midLt HTop ) h_bot h_mid
             | Chooser.Side.Right => MembershipGame_2STG A D p_mid p_top ( midLess HBot HTop ) (midGt HTop) h_mid h_top
     else -- Final one-step game
       MembershipGame_OneStep n sorry { val := p_bot, isLt := HBot } h_bot h_top

-- Protocol
-- Note Cesar add value to the interface or change the name?
def MembershipGame (n : Nat) (A : Proposer.Player n) (D : Chooser.Player) (tHash : Hash) : Winner
  :=
  -- A inits the game.
  match InitC : n with
  -- Zero means that there is no path, so A is providing the root.
  | Nat.zero =>
    if H A.value == tHash
    then Winner.Challenger
    else Winner.Challenged
  -- If we have a longer path, we go to the second stage of the game.
  | Nat.succ Nat.zero =>
    sorry
    -- MembershipGame_OneStep A 0 ( by rw [ InitC ]; simp ) (H A.init.val) tHash
  | Nat.succ (Nat.succ x) =>
    sorry
    -- MembershipGame_2STG A D
    --   -- Game range [0 ... |path| - 1 ]
    --   (A.init.pL-1) 0
    --   -- Range restrictions
    --   ( by { rw [ InitC ] ; simp } )
    --   ( by { rw [ InitC ] ; simp } )
    --   -- Hash ranges
    --   (A.init.valH) tHash
