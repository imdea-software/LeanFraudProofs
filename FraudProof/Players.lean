import FraudProof.DataStructures.Hash
import FraudProof.DataStructures.Value
import FraudProof.DataStructures.MTree

import Init.Data.Nat.Basic
import Mathlib.Tactic.Ring

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

end Chooser
