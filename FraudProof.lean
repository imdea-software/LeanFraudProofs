-- This module serves as the root of the `FraudProof` library.
-- Import modules here that should be built as part of the library.

-- Data Structures
import FraudProof.DataStructures.Value
import FraudProof.DataStructures.Hash
import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.MTree

-- Players Def
import FraudProof.Players
import FraudProof.Winning.Proposer -- ( Winning Strategy for the proposer. )

-- Games Definitions
import FraudProof.Games.GameDef -- ( Winner )

-- Games
import FraudProof.Games.OneStepGame
import FraudProof.Games.LinearGame
import FraudProof.Games.LogGame


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
    InitHashPathGameHeadToLast gameLength proposer.pathLenNZ headH lastH proposer.strategies chooser = Winner.Proposer
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
      : InitHashPathGameHeadToLast gameLength proposer.pathLenNZ (H v) mt.hash proposer.strategies chooser = Winner.Proposer
      := GChalWinsHtoLHashes gameLength (H v) mt.hash proposer chooser

  -- We cannot recover witnesses, because Lean has proof irrelevance hardcoded.
  -- theorem KWinsHtoL ( v : Value ) ( tree : BTree Value ) (vInTree : valueIn v tree)
  --   : let ⟨ path , pPath ⟩ := valueInToProof v tree vInTree
  --   exists (proposer : WinningProposer.WinningProp path.length v _),
  --     _Game = Winner.Proposer

theorem WinningProposer
    ( v : Value ) ( btree : BTree Value )
    (path : TreePath Value) (pathNNil : 0 < path.length)
    ( vInBTree : valueInProof v btree = some path)
: forall (chooser : Chooser.Player),
  have winprop := Build.WProposerCreate v btree path pathNNil vInBTree
  InitHashPathGameHeadToLast path.length pathNNil (H v) (hash_BTree btree).hash winprop.strategies chooser = Winner.Proposer
:=  by
  intros ch wp
  exact GChalWinsHtoL path.length v _ _ _


end LinearGame


namespace LogGame
-- * Logarithmic Game

open Proposer
open WinningProposer

-- Predicate to do induction over.
@[simp]
def LogWinningProp' (gL : Nat) : Prop :=
    forall
    (headH lastH : Hash)
    (proposer : PropHash gL headH lastH)
    (chooser : Chooser.Player),
    MembershipGame_2STG gL
    proposer.strategies chooser
    proposer.pathLenNZ -- path is not Zero
    headH lastH = Winner.Proposer

theorem PropHashWins (gL : Nat) : LogWinningProp' gL
  := @Nat.case_strong_induction_on LogWinningProp' gL
     ( -- Empty base case
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
        -- One Step Game, game length = 1.
        | zero =>
               simp
               exact WinningOne proposer
        -- Game length > 1, generating hash and choosing.
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
end LogGame
