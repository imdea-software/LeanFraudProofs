import FraudProof.DataStructures.Hash
import FraudProof.DataStructures.Value
import FraudProof.DataStructures.MTree

import Init.Data.Nat.Basic
import Mathlib.Tactic.Ring

import Batteries.Data.Fin.Lemmas

namespace Proposer
----------------------------------------------------------------------
-- ** Proposers play two roles.
-- They initialize the game and also play it.
-- structure Proposer where
--     -- To begin the game, proposers propose a position, an element and it's hash.
--     init : Nat × Value × Hash
--     -- To play the game, at each turn, proposers, given the current hashes,
--     -- propose a new hash in the middle.
--     strategy : Hash → Hash → ( Nat × Hash)
--     -- Final step, given bot and top such that pos(bot) + 1 == pos(top), produces
--     -- the missing hash.
--     final : Hash → Hash → Hash

-- *** Hash Strategies structure
structure HC (n : Nat) where
  -- Hashes along the way
  pathNode : Fin ( n + 1 ) -> Hash
  -- Path elem knows how to hash.
  pathSib : Fin n -> PathElem

def DropHeadHC {n : Nat}(hc : HC (n+1)) : HC n :=
  { pathNode := fun fn => match fn with
                | Fin.mk nV nLt => hc.pathNode ⟨ nV + 1, by simp; assumption ⟩
  , pathSib := fun fn => match fn with
                | Fin.mk nV nLt => hc.pathSib ⟨ nV + 1, by simp; assumption ⟩
  }

lemma DropHeadEq {n : Nat}( hc : HC n.succ )
     : forall (m : Nat) (mLt : m < n + 1)
     , hc.pathNode ⟨ m.succ , by simpa ⟩ = (DropHeadHC hc).pathNode ⟨ m , mLt ⟩
     := by intros m mLt
           unfold DropHeadHC
           simp

def DropLastHC {n : Nat} ( hc : HC (n+1) ) : HC n :=
 { pathNode := fun fn => match fn with
                         | Fin.mk nV nLt => hc.pathNode ⟨ nV , by exact Nat.lt_succ_of_lt nLt⟩
 , pathSib := fun fn => match fn with
                         | Fin.mk nV nLt => hc.pathSib ⟨ nV , by exact Nat.lt_succ_of_lt nLt ⟩
 }

-- Take m out of n from strategies arrays.
def takeHC {n : Nat}(m : Nat) (mLtn : m < n + 1) (hc : HC n) : HC m :=
{ pathNode :=
  fun p => match p with
           | ⟨ pVal, pLt ⟩ => hc.pathNode ⟨ pVal, by omega⟩
, pathSib :=
  fun p => match p with
           | ⟨ pVal, pLt ⟩ => hc.pathSib ⟨ pVal, by omega ⟩
}

-- Drop
def dropHC {n : Nat} (m : Nat) (mLtn : m < n + 1) (hc : HC n) : HC (n - m) :=
{ pathNode :=
  fun p => match p with
           | ⟨ pVal, pLt ⟩ => hc.pathNode ⟨ m + pVal, by omega⟩
, pathSib :=
  fun p => match p with
           | ⟨ pVal, pLt ⟩ => hc.pathSib ⟨ m + pVal, by omega ⟩
}

-- checking I am doing the right math
lemma LastFirst (m n : Nat) (mLtn : m < n + 1) (hc : HC n)
      : (takeHC m mLtn hc).pathNode ⟨ m , by omega ⟩ = (dropHC m mLtn hc).pathNode ⟨ 0 , by omega ⟩
      := by simp [takeHC , dropHC]

lemma DropLastNodeEq { n : Nat }( hc : HC (n+1))
      : forall (m : Nat) ( mLt : m < n+1 ),
      hc.pathNode ⟨ m , by apply Nat.lt_succ_of_lt; assumption⟩
      = (DropLastHC hc).pathNode ⟨ m , mLt ⟩
      := by
      intros m mLt
      unfold DropLastHC
      simp

lemma DropLastSibEq { n : Nat }( hc : HC (n+1))
      : forall (m : Nat) ( mLt : m < n), hc.pathSib ⟨ m , by trans n ; assumption; simp⟩
      = (DropLastHC hc).pathSib ⟨ m , mLt ⟩
      := by
      unfold DropLastHC
      intros m mLt
      simp

--
structure  Player ( gameLength : Nat) where
    -- Leaf value
    value : Value
    -- Hash Strategies
    hashStr : HC gameLength

-- Generic Proposer structure
structure IPlayer (cut len : Nat)(hb ht : Hash) where
  str : Fin len -> Hash

----------------------------------------------------------------------
end Proposer

namespace Chooser
----------------------------------------------------------------------
-- ** Choosers choose between two different ranges.
-- So we define the two possible moves as
inductive Side : Type :=
    | Left
    | Right

-- Chooser players chose between hashes at each moment.
structure Player where
    -- Strategy, given two ranges of hashes chosses one.
    -- [Hbot, Hmid] , [Hmid, Htop] -> Left/Right
    strategy : Hash → Hash → Hash → Side

-- Generic Chooser structure
structure IPlayer (cut len : Nat)(hb ht : Hash) where
  str : Hash -> Side

-- Lin Player is a family of straties, one for each step!
-- it is an array of functions choosing sides!
structure LinPlayer (len : Nat) where
  strategy : Fin len -> Hash → Hash → Side

@[simp]
def LinPlayer.chooseNow {len : Nat} (lNZ : 0 < len) : LinPlayer len -> Hash -> Hash -> Side
 := fun p => p.strategy ⟨ 0 , lNZ ⟩

-- Next chooser definition. Notice that I did the same with the Proposer.
-- @[simp]
def LinPlayer.nextChooser {len : Nat} (C : LinPlayer (len + 1)) : LinPlayer len
  := { strategy := fun p => match p with
                        | ⟨ val , lt ⟩ => C.strategy ⟨ val + 1 , by simpa ⟩}

end Chooser

--

namespace Knowing
-- Knowing a path means to provide all required hashes such that we can build a
-- path in the merkle tree
structure PathProof (len : Nat) (hhd htl : Hash) where
  pathWit : Fin len -> PathElem -- array of positioned hashes of length |len|
  goodPath : Fin.foldl len (fun acc p => opHash acc ( pathWit p )) hhd = htl

-- structure PathToProof (len : Nat) (hend : Hash) where
--  lenNZ : 0 < len
--  pathWit : Fin len -> PathElem
--  goodPath : Fin.foldl (len - 1)  ( fun acc p => opHash acc ( pathWit ⟨ p.val + 1 , by omega  ⟩  ) ) (pathWit ⟨ 0 , lenNZ ⟩ ) = hend

-- PathNode
def inPathProof { len : Nat }  (p : Nat) ( pLt : p < len + 1) { hl ht : Hash } ( pProof : PathProof len hl ht )
  : Hash
  := Fin.foldl p ( fun acc i => opHash acc ( pProof.pathWit ⟨ i.val , by omega ⟩)) hl

def DropHCKnowing {l : Nat} { hd ht : Hash }
  (p : PathProof (l + 1) hd ht)
  : PathProof l (inPathProof 1 (by simp ) p) ht
  := { pathWit := fun w => match w with
                           | ⟨ pVal , pLt ⟩ => p.pathWit ⟨ pVal + 1, by omega ⟩
     , goodPath := by
                have pG := p.goodPath
                rw [ Fin.foldl_succ ] at pG
                unfold inPathProof
                simp
                rw [ Fin.foldl_succ, Fin.foldl_zero ]
                assumption
       }

-- abbrev PathSch := List (Unit ⊕ Unit)

-- structure PathSchProof (p : PathSch) (ht : Hash) where
--   pNNil : 0 < p.length
--   pathWit : Fin p.length -> Hash
--   goodP : Fin.foldl p.length _ ( pathWit ⟨ 0 , pNNil ⟩ ) = ht

end Knowing
