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
-- import FraudProof.LogGame


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
