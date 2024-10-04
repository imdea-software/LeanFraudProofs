import FraudProof.Players

import FraudProof.Games.GameDef
import FraudProof.Games.OneStepGame

-- Utils and definitions
import FraudProof.DataStructures.MTree
import FraudProof.DataStructures.Hash

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

  open Proposer
  open Chooser

  def HashPathDrop
    (len : Nat) (lNZ : 0 < len)
    -- Players
    (A : HC len) ( D : Chooser.LinPlayer len )
    -- two hashes
    (h_head h_last : Hash)
    : Winner
    :=
    match len with
    -- Len = 0
    | Nat.zero => by simp at lNZ
    | Nat.succ pn =>
      match pn with
      -- Len = 1
      | Nat.zero => GameOneStep A h_head h_last
      -- Len > 1
      | Nat.succ ppn =>
        let hnext := A.pathNode ⟨ 1 , by simp ⟩
        match D.chooseNow (by simp) h_head hnext with
        | .Left =>
            if opHash h_head (A.pathSib ⟨ 0 , by simp ⟩) = hnext
            then Winner.Proposer
            else Winner.Chooser
        | .Right => HashPathDrop ppn.succ (by simp) (DropHeadHC A) (D.nextChooser) hnext h_last

  -- The following game checks that a the Challenger knows a path from |hashInit| to |hashLast|
  def HashPathCheck
    -- Length
    (len : Nat)
    -- Players
    (A : HC len) ( D : Chooser.Player )
    -- two hashes
    (h_head h_last : Hash)
    --
    (pos : Nat) ( posLt : pos < len )
    : Winner
  :=
    if posCheck : pos < len - 1
    then -- Game [h_head, ... , h_last] = D_chose( Game(nHash, ... , h_last), One(h_head,nHash) )
        let nHash := A.pathNode ⟨ pos + 1 , by apply Nat.succ_lt_succ; assumption ⟩ -- trans len-1;assumption; exact Nat.sub_lt_succ _ _⟩
        match D.strategy h_head nHash h_last with
        | .Left => -- OneStep Game
            if opHash h_head (A.pathSib ⟨ pos , posLt ⟩) = nHash
            then Winner.Proposer
            else Winner.Chooser
        | .Right => HashPathCheck _  A D nHash h_last (pos + 1) (by exact Nat.succ_lt_of_lt_pred posCheck)
    else -- pos = len - 1, Game([h_head, h_last])
        if opHash h_head (A.pathSib ⟨ len - 1 , by simp; exact Nat.zero_lt_of_lt posLt ⟩ ) = h_last
        then Winner.Proposer
        else Winner.Chooser

  -- The following game goes from |hashLast| to |hashInit|
  def HashPathCheckBack
    -- Length
    {len : Nat}
    -- Players
    (A : HC len) ( D : Chooser.Player )
    -- two hashes
    (h_head h_last : Hash)
    --
    (pos : Nat) (posNZ: 0 < pos) ( posLt : pos < len + 1)
    : Winner
    := match pos with
    | .zero => -- Impossible
        by simp at posNZ
    | .succ .zero => -- Game [h_head, h_last]
        if opHash h_head (A.pathSib ⟨ 0 , by simp at posLt; assumption ⟩) = h_last
        then Winner.Proposer
        else Winner.Chooser
    | .succ (.succ pn) => -- Game  [h_head, ... , h_last] = D_chose( Game(h_head, ... , nHash), One(nHash,h_last) )
        let nHash := A.pathNode ⟨ pn.succ , by trans pn.succ.succ;simp;assumption ⟩
        match D.strategy h_head nHash h_last with
        | .Left => -- OneStep Game
          HashPathCheckBack A D h_head nHash pn.succ (by simp) ( by trans pn.succ.succ; simp; assumption )
        | .Right =>
          if opHash nHash (A.pathSib ⟨ pn.succ , ( by simp at posLt; assumption ) ⟩) = h_last
          then Winner.Proposer
          else Winner.Chooser

  @[simp]
  def InjFin { n m : Nat }(nLtm : n < m)( x : Fin n ) : Fin m
      := match x with
        | Fin.mk xval xLt => ⟨ xval , by trans n; exact xLt; assumption ⟩

  theorem HashPathFunInj { n m : Nat }
          ( nLtm : n < m )( k : Nat )(kNZ : 0 < k)(kLtn : k < n + 1)
          (str1 : HC n)(str2 : HC m)
          (eqNode : forall (x : Fin (n + 1)), str1.pathNode x = str2.pathNode ( InjFin (by simp; assumption) x))
          (eqSib : forall (x : Fin n), str1.pathSib x = str2.pathSib ( InjFin nLtm x ))
          ( D : Chooser.Player ) :
          forall ( hv hr : Hash ) ,
           @HashPathCheckBack n str1 D hv hr k kNZ kLtn
          = @HashPathCheckBack m str2 D hv hr k kNZ ( by trans n + 1; assumption; simp; assumption )
          := by
          induction k with
          | zero =>
            unfold HashPathCheckBack
            simp
          | succ pk HI =>
            unfold HashPathCheckBack
            simp
            cases pk with
            | zero =>
              simp
              have eqSib0 := eqSib ⟨ 0 , by simp at kLtn; assumption ⟩
              rw [ eqSib0 ]
              simp
            | succ ppk =>
              simp
              have eqPathK := eqNode ⟨ ppk + 1 , by simp at kLtn; trans n; assumption; simp ⟩
              rw [ eqPathK ]
              simp
              intros hv hr
              cases D.strategy hv (str2.pathNode ⟨ ppk + 1, _ ⟩) hr with
              | Left =>
                simp
                exact HI _ _ hv (str2.pathNode ⟨ ppk + 1 , _ ⟩)
              | Right =>
                simp
                have eqSibPPK := eqSib ⟨ ppk + 1 , by simp at kLtn; assumption ⟩
                rw [ eqSibPPK ]
                simp

  def InitHashPathGameLastToHead
    -- Length
    (len : Nat) (lenNZ : 0 < len)
    (hashInit hashLast : Hash )
    -- Players
    (A : HC len) ( D : Chooser.Player )
    : Winner
    := HashPathCheck len A D hashInit hashLast 0 lenNZ

  def InitHashPathGameHeadToLast
    -- Length
    (len : Nat) (lenNZ : 0 < len)
    (hashInit hashLast : Hash )
    -- Players
    (A : HC len) ( D : Chooser.Player )
    : Winner
    := HashPathCheckBack A D hashInit hashLast len lenNZ ( by simp )
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

namespace Lemmas

  -- open Proposer -- ( HC )

  -- -- If a player (always) wins a Linear Game, also wins the other.
  -- -- Going down and up.
  -- lemma UpImplDown (len : Nat) (lenNZ : 0 < len) ( A : HC len ) (h_head h_last : Hash) :
  --   (forall (D : Chooser.Player), BotUpLin.InitHashPathGameLastToHead len lenNZ h_head h_last A D  = Winner.Proposer)
  --   ->
  --   (forall (D : Chooser.Player) , BotUpLin.InitHashPathGameHeadToLast len lenNZ h_head h_last A D = Winner.Proposer)
  --   := sorry

  -- lemma DownImplUp (len : Nat) (lenNZ : 0 < len) ( A : HC len ) (h_head h_last : Hash) :
  --   (forall (D : Chooser.Player) , BotUpLin.InitHashPathGameHeadToLast len lenNZ h_head h_last A D = Winner.Proposer)
  --   ->
  --   (forall (D : Chooser.Player), BotUpLin.InitHashPathGameLastToHead len lenNZ h_head h_last A D  = Winner.Proposer)
  --   := sorry

end Lemmas
