import FraudProof.Hash
import FraudProof.MTree
import FraudProof.Value
import FraudProof.List -- ( TakeAppend )
import FraudProof.BToMTree

import FraudProof.Players
import FraudProof.GoodChallenger

import FraudProof.GameDef

-- Math
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring

----------------------------------------
/- Smallest Game. A plays a game to see if it is right or not. -/

-- Given two hashes, the player provides the sibling hash.
-- One Step Def
def MembershipGame_OneStep
     ( n : Nat )
     ( A : HashChallenger n)
     ( p_bot : Fin n )
     ( h_bot h_top : Hash )
    : Winner
:=
  if opHash h_bot (A.sibling p_bot) == h_top
  then Winner.Challenger
  else Winner.Challenged

----------------------------------------

----------------------------------------
-- Winning along a path
-- This is a chain!
def AllwaysWinnig (p p' : _ ) ( path' : List Hash ) :=
  let path := p :: p' :: path'
  forall (A : HashChallenger path.length)
         ( n : Nat ) ( nLt : n <  path.length - 2),
         MembershipGame_OneStep path.length A ⟨ n , by trans path.length - 2; assumption; simp ; rw [ List.length ]; simp ⟩
                                              path[n] path[n+1] = Winner.Challenger
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
                -- repeat ( rw [listPathHashes] )
        }

-- @[simp]
-- def intermediateHash (v : Value) ( path : Path ) ( m : Fin (List.length path) ) : Hash :=
--     (RevStr $ Drop0 $ NodeHashPathF (H v) path) m
