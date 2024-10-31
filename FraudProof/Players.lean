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

--  Hash Type
variable (ℍ : Type)

-- *** Hash Strategies structure
structure HC (n : Nat) where
  -- Hashes along the way
  pathNode : Fin ( n + 1 ) -> ℍ
  -- Path elem knows how to hash.
  pathSib : Fin n -> PathElem ℍ

def DropHeadHC {n : Nat}(hc : HC ℍ (n+1)) : HC ℍ n :=
  { pathNode := fun fn => match fn with
                | Fin.mk nV nLt => hc.pathNode ⟨ nV + 1, by simp; assumption ⟩
  , pathSib := fun fn => match fn with
                | Fin.mk nV nLt => hc.pathSib ⟨ nV + 1, by simp; assumption ⟩
  }

lemma DropHeadEq {n : Nat}( hc : HC ℍ n.succ )
     : forall (m : Nat) (mLt : m < n + 1)
     , hc.pathNode ⟨ m.succ , by simpa ⟩ = (DropHeadHC ℍ hc).pathNode ⟨ m , mLt ⟩
     := by intros m mLt; simp [DropHeadHC]


lemma DropHeadEqSib {n : Nat} ( hc : HC ℍ n.succ.succ )
      : forall (m : Nat) (mLt : m < n+1)
      , hc.pathSib ⟨ m.succ , by simpa ⟩ = (DropHeadHC ℍ hc).pathSib ⟨ m , mLt ⟩
      := by intros m mLt; simp [DropHeadHC]

def DropLastHC {n : Nat} ( hc : HC ℍ (n+1) ) : HC ℍ n :=
 { pathNode := fun fn => match fn with
                         | Fin.mk nV nLt => hc.pathNode ⟨ nV , by exact Nat.lt_succ_of_lt nLt⟩
 , pathSib := fun fn => match fn with
                         | Fin.mk nV nLt => hc.pathSib ⟨ nV , by exact Nat.lt_succ_of_lt nLt ⟩
 }

-- Take m out of n from strategies arrays.
def takeHC {n : Nat}(m : Nat) (mLtn : m < n + 1) (hc : HC ℍ n) : HC ℍ m :=
{ pathNode :=
  fun p => match p with
           | ⟨ pVal, pLt ⟩ => hc.pathNode ⟨ pVal, by omega⟩
, pathSib :=
  fun p => match p with
           | ⟨ pVal, pLt ⟩ => hc.pathSib ⟨ pVal, by omega ⟩
}

-- Drop
def dropHC {n : Nat} (m : Nat) (mLtn : m < n + 1) (hc : HC ℍ n) : HC ℍ (n - m) :=
{ pathNode :=
  fun p => match p with
           | ⟨ pVal, pLt ⟩ => hc.pathNode ⟨ m + pVal, by omega⟩
, pathSib :=
  fun p => match p with
           | ⟨ pVal, pLt ⟩ => hc.pathSib ⟨ m + pVal, by omega ⟩
}

-- checking I am doing the right math
lemma LastFirst (m n : Nat) (mLtn : m < n + 1) (hc : HC ℍ n)
      : (takeHC ℍ m mLtn hc).pathNode ⟨ m , by omega ⟩ = (dropHC ℍ m mLtn hc).pathNode ⟨ 0 , by omega ⟩
      := by simp [takeHC , dropHC]

lemma DropLastNodeEq { n : Nat }( hc : HC ℍ (n+1))
      : forall (m : Nat) ( mLt : m < n+1 ),
      hc.pathNode ⟨ m , by apply Nat.lt_succ_of_lt; assumption⟩
      = (DropLastHC ℍ hc).pathNode ⟨ m , mLt ⟩
      := by
      intros m mLt
      unfold DropLastHC
      simp

lemma DropLastSibEq { n : Nat }( hc : HC ℍ (n+1))
      : forall (m : Nat) ( mLt : m < n), hc.pathSib ⟨ m , by trans n ; assumption; simp⟩
      = (DropLastHC ℍ hc).pathSib ⟨ m , mLt ⟩
      := by
      unfold DropLastHC
      intros m mLt
      simp

-- Generic Proposer structure
structure IPlayer (cut len : Nat)(hb ht : ℍ) where
  str : Fin len -> ℍ

structure  Player (α :Type) ( gameLength : Nat) where
    -- Leaf value
    value : α
    -- Hash Strategies
    hashStr : HC ℍ gameLength

end Proposer
----------------------------------------------------------------------
-- ** Correct Hash Proposer

namespace IProposer
-- Higher level name.
abbrev proposeFromTree {α ℍ : Type}[Hash α ℍ][HashMagma ℍ]
    : BTree α -> MTree ℍ := hash_BTree

def proposeFromList {α ℍ : Type}[Hash α ℍ][HashMagma ℍ]
    : List α -> Option (MTree ℍ) := Option.map hash_BTree ∘ List.fromList

-- We can also have some type information.
def validPropose {α ℍ : Type}[Hash α ℍ][HashMagma ℍ]
    (valid : α -> Bool) (ls : List α) : Option (MTree ℍ)
    := if List.all ls valid
       then proposeFromList ls
       else none

end IProposer

----------------------------------------------------------------------

----------------------------------------------------------------------
-- ** Choosers choose between two different ranges.
-- So we define the two possible moves as
namespace Chooser

inductive Side : Type :=
    | Left
    | Right


variable (ℍ : Type)
-- Chooser players chose between hashes at each moment.
structure Player where
    -- Strategy, given two ranges of hashes chosses one.
    -- [Hbot, Hmid] , [Hmid, Htop] -> Left/Right
    strategy : ℍ → ℍ → ℍ → Side

-- Generic Chooser structure
structure IPlayer (cut len : Nat)(hb ht : ℍ) where
  str : ℍ -> Side

-- Lin Player is a family of straties, one for each step!
-- it is an array of functions choosing sides!
structure LinPlayer (len : Nat) where
  strategy : Fin len -> ℍ → ℍ → Side

@[simp]
def LinPlayer.chooseNow {len : Nat} (lNZ : 0 < len) : LinPlayer ℍ len -> ℍ -> ℍ -> Side
 := fun p => p.strategy ⟨ 0 , lNZ ⟩

-- Next chooser definition. Notice that I did the same with the Proposer.
-- @[simp]
def LinPlayer.nextChooser {len : Nat} (C : LinPlayer ℍ (len + 1)) : LinPlayer ℍ len
  := { strategy := fun p => match p with
                        | ⟨ val , lt ⟩ => C.strategy ⟨ val + 1 , by simpa ⟩}

end Chooser

--

namespace Knowing
-- Knowing a path means to provide all required hashes such that we can build a
-- path in the merkle tree

  variable {ℍ : Type}
  structure PathProof [HashMagma ℍ](len : Nat) (hhd htl : ℍ) where
    pathWit : Fin len -> PathElem ℍ -- array of positioned hashes of length |len|
    goodPath : Fin.foldl len (fun acc p => opHash acc ( pathWit p )) hhd = htl

  structure PathProofSeq [HashMagma ℍ](len : Nat) (skl : Fin len -> Unit ⊕ Unit ) (hhd htl : ℍ) where
    pathWit : Fin len -> ℍ -- array of positioned hashes of length |len|
    goodPath : Fin.foldl len
              (fun acc p => opHash acc ( match skl p with -- map
                                          | Sum.inl _ => Sum.inl (pathWit p)
                                          | Sum.inr _ => Sum.inr (pathWit p)
                                        )) hhd
              = htl

  def inPathSeq { len : Nat } [HashMagma ℍ](p : Nat) ( pLt : p < len + 1)
      {skl : Fin len -> SkElem}{ hl ht : ℍ } ( pProof : PathProofSeq len skl hl ht )
    : ℍ
    := Fin.foldl p ( fun acc i => opHash acc ( (skl ⟨ i.val , by omega⟩).fill $ pProof.pathWit ⟨ i.val , by omega ⟩)) hl

  -- PathNode
  def inPathProof { len : Nat } [HashMagma ℍ]  (p : Nat) ( pLt : p < len + 1) { hl ht : ℍ } ( pProof : PathProof len hl ht )
    : ℍ
    := Fin.foldl p ( fun acc i => opHash acc ( pProof.pathWit ⟨ i.val , by omega ⟩)) hl

  def DropHCKnowingSeq {l : Nat} {skl : Fin (l + 1) -> SkElem} { hd ht : ℍ }[HashMagma ℍ]
    (p : PathProofSeq (l + 1) skl hd ht)
    : PathProofSeq l (fun p => match p with
                              | ⟨ val , Lt ⟩ => skl ⟨ val + 1, by omega ⟩) (inPathSeq 1 (by simp ) p) ht
    := {
    pathWit := fun w => match w with
                        | ⟨ pVal, Lt ⟩ => p.pathWit ⟨ pVal + 1 , by omega ⟩
    , goodPath := by
      have pG := p.goodPath
      rw [ Fin.foldl_succ ] at pG
      unfold inPathSeq
      simp
      rw [ Fin.foldl_succ, Fin.foldl_zero ]
      simp at *
      assumption
  }
  def DropHCKnowing {l : Nat} { hd ht : ℍ }[HashMagma ℍ]
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


----------------------------------------
-- * Strategy generation.
-- Given a list of elements, this is public information known by all, this
-- module generates everything for the correct agent.
namespace StrategyGeneration

structure CorrectAgent {α : Type}(ℍ : Type) (ls : List α) where
  -- Data
  tree : BTree α
  rootHash : ℍ --
  -- Structures


-- def build {α ℍ : Type}
--   -- Validity def
--   (valid : α -> Bool)
--   -- Knowledge
--   (es : List α)
--   --
--   : CorrectAgent ℍ es
--   := sorry


end StrategyGeneration
----------------------------------------
