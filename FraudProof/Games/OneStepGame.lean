-- Definitions
import FraudProof.DataStructures.Hash
import FraudProof.DataStructures.MTree
-- import FraudProof.DataStructures.Value

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
    {ℍ : Type}[BEq ℍ][HashMagma ℍ]
     ( n : Nat )
     ( P : Proposer.HC ℍ n)
     ( p_bot : Fin n )
     ( h_bot h_top : ℍ )
    : Winner
:=
  if opHash h_bot (P.pathSib p_bot) == h_top
  then Winner.Proposer
  else Winner.Chooser

@[simp]
def GameOneStep
  {ℍ : Type}[BEq ℍ][HashMagma ℍ]
  (P : Proposer.HC ℍ 1)
  (hL hT : ℍ) : Winner
  := if opHash hL (P.pathSib ⟨ 0 , by simp ⟩) == hT then Winner.Proposer else Winner.Chooser


----------------------------------------

----------------------------------------
-- Winning along a path
-- This is a chain!
def AllwaysWinnig {ℍ : Type}[BEq ℍ][HashMagma ℍ]
  (p p' : ℍ ) ( path' : List ℍ) :=
  let path := p :: p' :: path'
  forall (A : Proposer.HC ℍ path.length)
         ( n : Nat ) ( nLt : n <  path.length - 2),
         MembershipGame_OneStep path.length A ⟨ n , by trans path.length - 2; assumption; simp ; rw [ List.length ]; simp ⟩
                                              path[n] path[n+1] = Winner.Proposer
----------------------------------------

----------------------------------------
-- Good Challenger always win.
--
def rootHash {α ℍ : Type}[m : Hash α ℍ][HashMagma ℍ]( v : α ) ( path' : TreePath α ) : ℍ :=
  listPathHashes (m.mhash v) (treeTohashPath path')

theorem irootHash {α ℍ : Type}[m : Hash α ℍ][HashMagma ℍ]( v : α ) ( e : BTree α ⊕ BTree α) ( path : TreePath α ):
        rootHash v (e :: path) = listPathHashes ( opHash (m.mhash v) (hashElem e) ) (treeTohashPath path)
        := by {
          match path with
          | List.nil =>
                     rw [ treeTohashPath , rootHash ]
                     simp
          | List.cons q qs  =>
                rw [ rootHash ]
                simp
        }
