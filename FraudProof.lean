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

theorem GChalWins
    (v : Value)  (mt : MTree)
    (challenger : GoodChal v mt)
    (challenged : Challenged) :
    InitHashPathGame challenger.pathLen challenger.pathLenNZ (H v) mt.hash challenger.strategies challenged = Winner.Challenger
    := by
    unfold InitHashPathGame
    unfold HashPathCheck
    simp
    intro pathLen
    match challenged.strategy (H v) (challenger.strategies.pathNode _ ) mt.hash with
    | .Left =>
      simp
      rw [ <- challenger.nodeZero ]
      have zChall := challenger.allGames 0 ( by simp; assumption)
      simp at zChall
      rw [ <- zChall ]
    | .Right =>
      sorry -- missing Inductive pred?

end LinearGame
