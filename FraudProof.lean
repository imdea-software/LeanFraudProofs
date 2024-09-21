-- This module serves as the root of the `FraudProof` library.
-- Import modules here that should be built as part of the library.

-- Data Structures
import FraudProof.Value
import FraudProof.Hash
import FraudProof.BTree
import FraudProof.MTree

-- Players Def
import FraudProof.Players
import FraudProof.WinningProposer -- ( Winning Strategy for the proposer. )

-- Games Definitions
import FraudProof.GameDef -- ( Winner )

-- Games
import FraudProof.OneStepGame
import FraudProof.LinearGame
import FraudProof.LogGame


namespace LinearGame
-- * Linear Game

open Proposer
open WinningProposer
open BotUpLin

-- ** /Good
theorem GChalWinsHtoLHashes (gameLength : Nat) :
    forall
    (headH lastH : Hash)
    (proposer : PropHash gameLength headH lastH)
    (chooser : Chooser.Player),
    InitHashPathGameHeadToLast gameLength proposer.pathLenNZ headH lastH proposer.strategies chooser = Winner.Challenger
    := by
    induction gameLength with
    | zero => -- Impossible
      intros _ _ proposer _
      cases proposer with
      | mk pathLen _ _ _ _ => simp at pathLen
    | succ pn HN =>
      intros hv hr A D
      unfold InitHashPathGameHeadToLast
      unfold HashPathCheckBack
      simp
      cases pn with
      | zero => simp; exact GCLemmas.GChalOneH _
      | succ n =>
        simp
        cases D.strategy hv (A.strategies.pathNode ⟨ (n + 1), _ ⟩) hr with
        | Left =>
          simp
          unfold InitHashPathGameHeadToLast at HN
          have HI := HN hv ((A.strategies.pathNode ⟨n + 1, by simp⟩)) (GCShifts.DropLast _ hv hr A) D
          unfold GCShifts.DropLast at HI
          simp at HI
          have eqDropNode := DropLastNodeEq A.strategies
          have eqDropSib := DropLastSibEq A.strategies
          have eqInj := HashPathFunInj (by simp) (n + 1) (by simp) (by simp) (DropLastHC A.strategies) A.strategies ( by rw [Fin.forall_iff]; exact eqDropNode ) ( by rw [Fin.forall_iff] ; exact eqDropSib ) D hv (A.strategies.pathNode ⟨ n+1 , by simp ⟩ )
          rw [ <- eqInj ]
          assumption
        | Right =>
          simp
          have aroot := A.nodeRoot
          simp at aroot
          have agames := A.allGames
          simp at agames
          have lastGame := agames (n + 1) ( by simp )
          clear agames
          rw [ aroot ] at lastGame
          rw [ <- lastGame ]

theorem GChalWinsHtoL (gameLength : Nat)
      (v : Value) (mt : MTree)
      (proposer : WinningProposer.WinningProp gameLength v mt)
      (chooser : Chooser.Player)
      : InitHashPathGameHeadToLast gameLength proposer.pathLenNZ (H v) mt.hash proposer.strategies chooser = Winner.Challenger
      := GChalWinsHtoLHashes gameLength (H v) mt.hash proposer chooser

  -- We cannot recover witnesses, because Lean has proof irrelevance hardcoded.
  -- theorem KWinsHtoL ( v : Value ) ( tree : BTree Value ) (vInTree : valueIn v tree)
  --   : let ⟨ path , pPath ⟩ := valueInToProof v tree vInTree
  --   exists (proposer : WinningProposer.WinningProp path.length v _),
  --     _Game = Winner.Challenger

theorem WinningProposer
    ( v : Value ) ( btree : BTree Value )
    (path : TreePath Value) (pathNNil : 0 < path.length)
    ( vInBTree : valueInProof v btree = some path)
: forall (chooser : Chooser.Player),
  have winprop := Build.WProposerCreate v btree path pathNNil vInBTree
  InitHashPathGameHeadToLast path.length pathNNil (H v) (hash_BTree btree).hash winprop.strategies chooser = Winner.Challenger
:=  by
  intros ch wp
  exact GChalWinsHtoL path.length v _ _ _


end LinearGame


namespace LogGame
-- * Logarithmic Game

open Proposer
open WinningProposer

-- Distance induction predicate so we can perform strong induction.
-- Remember we need ind hypotheses over smaller ranges.
-- In LogGames, we only split the range in two. But in K-Games, we split them in
-- k segments.
@[simp]
def LogWinningProp' (gL : Nat) : Prop :=
    forall
    (headH lastH : Hash)
    (proposer : PropHash gL headH lastH)
    (chooser : Chooser.Player),
    MembershipGame_2STG gL
    proposer.strategies chooser
    proposer.pathLenNZ -- path is not Zero
    headH lastH = Winner.Challenger

-- @[simp]
-- def LogWinningProp ( gL : Nat ) : Prop :=
--     forall
--     (headH lastH : Hash)
--     (proposer : PropHash gL headH lastH)
--     (chooser : Chooser.Player),
--     MembershipGame gL proposer.pathLenNZ proposer.strategies chooser headH lastH = Winner.Challenger


theorem PropHashWins (gL : Nat) : LogWinningProp' gL
  := @Nat.case_strong_induction_on LogWinningProp' gL
     ( -- Base case
     by simp
        intros _ _ P _
        have NZ := P.pathLenNZ
        simp at NZ
     )
     ( -- Ind Case
     by intros n SInd
        simp at *
        intros hashB hashT
        intros proposer chooser
        unfold MembershipGame_2STG
        simp
        cases n with
        | zero =>
               simp
               exact WinningOne proposer
        | succ pn =>
          simp
          cases chooser.strategy hashB (proposer.strategies.pathNode ⟨pn / 2 + 1, _ ⟩) hashT with
          | Left => simp
                    let leftWinning := GCOps.take_proposer (pn / 2 + 1) pn.succ.succ (by simp) (by omega) proposer
                    exact SInd (pn / 2 + 1) (by simp; exact Nat.div_le_self pn 2 ) hashB (proposer.strategies.pathNode ⟨pn / 2 + 1, by omega⟩) leftWinning chooser
          | Right => simp
                     let rightWinning := GCOps.drop_proposer (pn / 2 + 1)  pn.succ.succ (by omega) proposer
                     exact SInd (pn + 1 + 1 - (pn / 2 + 1)) (by omega) (proposer.strategies.pathNode ⟨pn / 2 + 1, by omega⟩) hashT rightWinning chooser
     )
-- theorem PropHashWins (gameLength : Nat) : LogWinningProp' gameLength
--     := @Nat.case_strong_induction_on LogWinningProp' gameLength
--       -- Base Case, its impossible
--       (by simp [ MembershipGame ]; intros rl rr lLtr rLtGL hB hT A C; have nNZ := A.pathLenNZ; simp at nNZ )
--       -- Stong inductive case.
--       (by intros n SHInd -- SHInd says winning strategy wins all intermediate cases.
--           simp [ MembershipGame ] at *
--           intros l r lLtr rLtGL hB hT A C
--           unfold MembershipGame_2STG
--           simp
          -- cases? |l + 1 < r|
          -- | zero => simp
          --           have ARoot := A.nodeRoot
          --           have AZero := A.nodeZero
          --           have AMid := A.allGames 0
          --           simp at *
          --           rw [ ARoot , AZero] at AMid
          --           rw [ <- AMid ]
          -- | succ pn => simp
          --              cases C.strategy hB (A.strategies.pathNode ⟨ (pn + 1 + 1 ) / 2 , _ ⟩) hT with
          --              | Left => simp
          --                        -- We need to transform A into A pn+1+1 / 2.
          --                        have pmidLtpn : (pn + 1 + 1) / 2 ≤ pn + 1 := sorry
          --                        have SApp := SHInd ((pn + 1 + 1 ) / 2) pmidLtpn hB _ (GCOps.first_half_proposer pn hB hT A) C
          --                        -- exact SHInd ((pn + 1 + 1 ) / 2) _ hB _ (GCOps.first_half_proposer pn hB hT A) C
          --                        -- Range manipulation functions, similar to HashPathFunInj
          --                        sorry
          --              | Right => simp -- Wrong Inductive Hyp!!!
          --                         -- We need a stronger one, it is about range!!
          --                         have pmidLtpn : (pn + 1 + 1) / 2 ≤ pn + 1 := sorry
          --                         have SApp := SHInd ((pn + 1 + 1 ) / 2) pmidLtpn _ hT (GCOps.snd_half_proposer pn hB hT A) C


      -- )
end LogGame
