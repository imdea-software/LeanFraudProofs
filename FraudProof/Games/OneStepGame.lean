-- Definitions
import FraudProof.DataStructures.Hash
import FraudProof.DataStructures.MTree
import FraudProof.DataStructures.Value

-- Utilities.
import FraudProof.Extras.List -- ( TakeAppend )
import FraudProof.Extras.BToMTree

import FraudProof.Players
import FraudProof.Winning.Proposer

import FraudProof.Games.GameDef

-- Math
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring

----------------------------------------
/- Smallest Game. A plays a game to see if it is right or not. -/

-- Given two hashes, the player provides the sibling hash.
-- One Step Def
@[simp]
def MembershipGame_OneStep
     ( n : Nat )
     ( P : Proposer.HC n)
     ( p_bot : Fin n )
     ( h_bot h_top : Hash )
    : Winner
:=
  if opHash h_bot (P.pathSib p_bot) == h_top
  then Winner.Proposer
  else Winner.Chooser

@[simp]
def GameOneStep
  (P : Proposer.HC 1)
  (hL hT : Hash) : Winner
  := if opHash hL (P.pathSib ⟨ 0 , by simp ⟩) == hT then Winner.Proposer else Winner.Chooser


----------------------------------------

----------------------------------------
-- Winning along a path
-- This is a chain!
def AllwaysWinnig (p p' : _ ) ( path' : List Hash ) :=
  let path := p :: p' :: path'
  forall (A : Proposer.HC path.length)
         ( n : Nat ) ( nLt : n <  path.length - 2),
         MembershipGame_OneStep path.length A ⟨ n , by trans path.length - 2; assumption; simp ; rw [ List.length ]; simp ⟩
                                              path[n] path[n+1] = Winner.Proposer
----------------------------------------

----------------------------------------
-- Good Challenger always win.
--
def rootHash ( v : Value ) ( path' : TreePath Value ) : Hash :=
  listPathHashes (H v) (treeTohashPath path')

theorem irootHash ( v : Value ) ( e : BTree Value ⊕ BTree Value) ( path : TreePath Value ):
        rootHash v (e :: path) = listPathHashes ( opHash (H v) (hashElem e) ) (treeTohashPath path)
        := by {
          match path with
          | List.nil =>
                     rw [ treeTohashPath , rootHash ]
                     simp
          | List.cons q qs  =>
                rw [ rootHash ]
                simp
        }
