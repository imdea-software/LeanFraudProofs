import FraudProof.Challenger
import FraudProof.GameDef
import FraudProof.Hash
import FraudProof.MTree
import FraudProof.Value

import FraudProof.GoodChallenger

import Mathlib.Data.List.Lemmas
import Mathlib.Data.Fin.Basic
-- import Mathlib.Algebra.Ring.Basic
-- import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Ring

----------------------------------------
/- Smallest Game. A plays a game to see if it is right or not. -/

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
-- Good Challenger always win.
--
def rootHash ( v : Value ) ( path : TreePath Value ) : Hash :=
  let path := treeTohashPath path
  listPathHashes (H v) path

theorem irootHash ( v : Value ) ( e : BTree Value ⊕ BTree Value) ( path : TreePath Value ):
        rootHash v (e :: path) = listPathHashes ( opHash (H v) (hashElem e) ) (treeTohashPath path)
        := by {
          match path with
          | List.nil =>
                     rw [ treeTohashPath , rootHash ]
                     simp
                     rw [ treeTohashPath , listPathHashes, hashElem]
                     simp
                     repeat (rw [ listPathHashes ])
          | List.cons q qs  =>
                rw [ rootHash ]
                simp
                rw [ treeTohashPath ]
                simp
                repeat ( rw [listPathHashes] )
        }

def intermediateHash (v : Value) ( path : Path ) ( m : Fin (List.length path) ) : Hash :=
    let pathHash := List.reverse $ List.drop 1 $ ScanPath (H v) path
    List.get pathHash { val:= m.val , isLt := by {
             have LenEq : pathHash.length = path.length := by {
              rw [ List.length_reverse ]
              simp
              rw [ ScanPath , List.length_scanl ]
              simp
              }
             rw [ LenEq ]
             simp} }


theorem GoodWins ( path : TreePath Value )
  : forall ( v : Value ) ( n : Fin (List.length path)),
    let pathHash := treeTohashPath path
    let nPath : Fin pathHash.length :=
      { val := n.val , isLt :=
               by {have eqLen : pathHash.length = path.length :=
                        by { exact  List.length_map _ _  }
                   rw [ eqLen ]
                   simp
                     }}
    MembershipGame_OneStep path.length
      ( CGoodPlayer v path ).hashStr n
      (intermediateHash v pathHash nPath)
      (rootHash v path) = Winner.Challenger
:= by {
  induction path with
  | nil => simp
  | cons p ps HInd => {
    -- intros v n pHash pLen
    -- -- apply (opHash (H v) (hashElem p)) at HInd
    -- rw [ MembershipGame_OneStep ]
    -- -- simp at *
    -- simp
    -- rw [ irootHash ]
    -- rw [ siblingGP ]
    -- simp
    -- unfold intermediateHash
    -- simp
    -- rw [ <- List.getElem_reverse (ScanPath (H v) pHash).tail.reverse ]
    -- simp
    -- rw [ <- List.getElem_reverse (treeTohashPath (p :: ps)).reverse ]
    -- simp
    -- rw [ List.getElem_tail ]
    -- have EqLen : (ScanPath ( H v ) pHash).length = pHash.length + 1
    --   := by exact List.length_scanl _ pHash
    -- have EqGet : (ScanPath (H v) pHash).length - 1 - 1 - ↑n + 1 = pHash.length - 1 - ↑n + 1
    --   := by {rw [ EqLen ]; simp }
    sorry





    -- have HTreeH : treeTohashPath ( p :: ps )  = ( hashElem p ) :: treeTohashPath ps :=
    --   by
    --     unfold treeTohashPath
    --     simp
    -- rw [ HTreeH ]
}
}
