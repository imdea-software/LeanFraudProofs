-- import FraudProof.DataStructures.Value
import FraudProof.DataStructures.MTree
import FraudProof.DataStructures.Hash

-- Players
import FraudProof.Players

-- Knowlege players have.
open Knowing

-- Fraud-proof games have a nice additional hypothesis: one of the bounds is
-- right! When the game begins, the upper bound hash in the path, |lastH :
-- Hash|, is the root of the Merkle Tree.
--
-- Assuming that, the following chooser, |KChooser| keeps the bound that belongs
-- to the membership proof witness |pathP|.
--------------------------------------------------------------------------------
-- Knowing Chooser.
--
def KChooser {ℍ : Type}[HashMagma ℍ][BEq ℍ](gl : Nat) ( hd lt : ℍ )
    -- Knowing a path of length |gl| from |hd| to |lt|
    (pathP : Knowing.PathProof gl hd lt)
    -- Cut in position
    ( p : Nat ) ( pLt : p < gl + 1 )
    --
    ( bot int top : ℍ)
    -- One bound is knowledge valid.
    : Chooser.Side
    :=
    if int == Knowing.inPathProof p pLt pathP -- int = pathNode[p]
    then if bot == Knowing.inPathProof 0 (by omega) pathP
         then Chooser.Side.Right
         -- If | H : bot = hd ∨ top = lt |, then this is right.
         else Chooser.Side.Left
    else if top == Knowing.inPathProof gl (by omega) pathP
         then Chooser.Side.Right
         -- If | H : bot = hd ∨ top = lt |, then this is right.
         else Chooser.Side.Left

-- cut here is where is the cut, in Linear games is one, but in Log games is floor (gl/2)
def KnowingChooser {ℍ : Type}{gl : Nat}{hb ht : ℍ}[BEq ℍ][HashMagma ℍ]
  ( k : Knowing.PathProof gl hb ht ) (cut : Nat) (cR : cut < gl + 1)
  : Chooser.Player ℍ
  := {
  strategy := KChooser gl hb ht k cut cR
  }

-- -- For example, if we are choosing between whatever range, we can choose
-- -- whatever that it is the same.
-- --------------------------------------------------------------------------------

-- --------------------------------------------------------------------------------
-- -- Linear Chooser.
-- -- Linear chooser start from something that may be wrong, but has as end point
-- -- the root of the tree.
-- Assuming we are walking trhough a path towards |lt|.
-- @[simp]
def LinChooser {ℍ : Type}[BEq ℍ]
    -- Knowing elements
    (hd : ℍ) ( nextInPath : ℍ)
    --
    (head next : ℍ )
    : Chooser.Side
    :=
    if head != hd
    then if next == nextInPath
         then Chooser.Side.Left
         else Chooser.Side.Right
    else -- Head is hd
      if next != nextInPath
      then Chooser.Side.Left
      else Chooser.Side.Right

def KnowingLinChooserSkl {ℍ : Type}[BEq ℍ][HashMagma ℍ]
   ( len : Nat ) {skl : Fin len -> Unit ⊕ Unit} {hb ht : ℍ}
   ( path : Knowing.PathProofSeq len skl hb ht )
   : Chooser.LinPlayer ℍ len
   := {
   strategy := fun p phead pnext =>
   LinChooser
     -- First the ones that really are
     (Knowing.inPathSeq p.val (by omega) path )
     (Knowing.inPathSeq p.val.succ (by omega) path)
     -- Then the ones proposed by the proposer
     phead pnext
}
-- @[simp]
def KnowingLinChooser
   {ℍ : Type}[BEq ℍ] [HashMagma ℍ]
   ( len : Nat ) (hb ht : ℍ)
   ( path : Knowing.PathProof len hb ht )
   : Chooser.LinPlayer ℍ len
   := {
   strategy := fun p phead pnext =>
   LinChooser
     -- First the ones that really are
     (Knowing.inPathProof p.val (by omega) path )
     (Knowing.inPathProof p.val.succ (by omega) path)
     -- Then the ones proposed by the proposer
     phead pnext
}

-- --------------------------------------------------------------------------------

-- --------------------------------------------------------------------------------
-- -- def BadWiseChooser (PH PL: Hash -> Bool) (hd lt : Hash)
-- --  -- There is one bound that holding proporety PH PL
-- --  (boundH : PH hd ∨ PL lt)
-- --  --
-- --  : Chooser.Side
-- --  := match hHD : PH hd , hLT : PL lt with
-- --    | _ , true => Chooser.Side.Right -- We prioritize upper bound when possible.
-- --    | true , _  => Chooser.Side.Left
-- --    | false  , false => by rw [ hHD , hLT ] at boundH; simp at boundH

-- -- The above chooser does not always choose properly. [low, mid] , [mid, high]
-- -- such that |low| is not correct but |mid, high| are.
-- --
-- --------------------------------------------------------------------------------
