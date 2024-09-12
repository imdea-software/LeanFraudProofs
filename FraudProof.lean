-- This module serves as the root of the `FraudProof` library.
-- Import modules here that should be built as part of the library.

-- Data Structures
import FraudProof.Value
import FraudProof.Hash
import FraudProof.BTree
import FraudProof.MTree

-- Players Def
import FraudProof.Players
import FraudProof.GoodChallenger

-- Games Definitions
import FraudProof.GameDef -- ( Winner )

-- Games
import FraudProof.OneStepGame
import FraudProof.LinearGame
import FraudProof.LogGame


namespace LinearGame
-- * Linear Game

open Challenged
open GoodChallenger
open BotUpLin

theorem GChalWinsHtoLHashes (gameLength : Nat) :
    forall
    (headH lastH : Hash)
    (challenger : ChalHash gameLength headH lastH)
    (challenged : Challenged),
    InitHashPathGameHeadToLast gameLength challenger.pathLenNZ headH lastH challenger.strategies challenged = Winner.Challenger
    := by
    induction gameLength with
    | zero => -- Impossible
      intros _ _ challenger _
      cases challenger with
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

-- theorem GChalWins
--     (v : Value)  (mt : MTree)
--     (challenger : GoodChal v mt)
--     (challenged : Challenged) :
--     InitHashPathGameLastToHead challenger.pathLen challenger.pathLenNZ (H v) mt.hash challenger.strategies challenged = Winner.Challenger
--     := sorry

end LinearGame
