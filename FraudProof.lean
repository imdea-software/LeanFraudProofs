-- This module serves as the root of the `FraudProof` library.
-- Import modules here that should be built as part of the library.
import FraudProof.Value
import FraudProof.Hash
import FraudProof.BTree
import FraudProof.MTree

-- Import Math lib?

-- import tactic
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Basic
-- import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Order.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic
import Init.Data.Nat.Div
-- import Mathlib.Topology.Basic
-- t

--------------------------------------------------
-- * Game definitions
--
-- ** Challengers play two roles.
-- They initialize the game and also play it.
structure Challenger where
    -- To begin the game, challengers propose a position, an element and it's hash.
    init : Nat × Value × Hash
    -- To play the game, at each turn, challengers, given the current hashes,
    -- propose a new hash in the middle.
    strategy : Hash → Hash → ( Nat × Hash)
    -- Final step, given bot and top such that pos(bot) + 1 == pos(top), produces
    -- the missing hash.
    final : Hash → Hash → Hash

structure InitialConf where
   pL : Nat
   val : Value
   valH : Hash

-- Simpler definition.
structure ChallengerReq where
    -- First, propposes a value at a given position with a given hash.
    init : InitialConf
    -- Then, at each step it provides a Hash.
    strategy : Fin init.pL → Hash
    -- Final strategy, is a sibling. This is actually a Hash along the way, isn't it?
    sibling : Fin init.pL → PathElem

-- ** Defender can choose between two different ranges.
-- So we define the two possible moves as
inductive Side : Type :=
    | Left
    | Right

-- Challenged players chose between hashes at each moment.
structure Challenged where
    -- Strategy, given two ranges of hashes chosses one.
    -- [Hbot, Hmid] , [Hmid, Htop] -> Left/Right
    strategy : Hash → Hash → Hash → Side

--------------------------------------------------

--------------------------------------------------------------------------------
-- Game Definition ------------------------------------------------------------
--
-- We move information using a Turns
inductive Turn : Type :=
  -- It is Challenger's turn and needs to provide two paths
  | Challenger ( b t : Nat × Hash )
  | Challenged ( b m t : Nat × Hash )

inductive Winner : Type := | Challenger | Challenged

-- I am sure there is a Lean way to do this.
axiom midLt { a b : Nat } ( H : b < a ) : (a + b) / 2 < a
axiom midLess { a b M : Nat }
  : a < M → b < a → ( a + b ) / 2 < M
axiom midLessEqLt { a b M : Nat }
  : a ≤ M → b < a → ( a + b ) / 2 < M
axiom midLessEqLeq { a b M : Nat }
  : a ≤ M → b < a → ( a + b ) / 2 ≤ M
axiom midGt { a b : Nat }
  : a < b → a < (  b + a ) / 2


-- Game description that works, second stage.
def MembershipGame_2STG (A :  ChallengerReq) (D : Challenged)
    : (p_bot p_top : Nat)
    → ( H_bot : p_bot < A.init.pL )
    → ( H_top : p_top < p_bot )
    → (h_bot h_top : Hash)
    → Winner
     := fun p_bot p_top HBot HTop h_bot h_top =>
     if (p_bot > (p_top + 1))
     then -- Following the path
           let p_mid := (p_bot + p_top) / 2 -- middle position
           let h_mid := A.strategy { val := p_mid , isLt := by exact midLess HBot HTop}
           match D.strategy h_bot h_mid h_top with
             | Side.Left => MembershipGame_2STG A D p_bot p_mid  HBot ( midLt HTop ) h_bot h_mid
             | Side.Right => MembershipGame_2STG A D p_mid p_top ( midLess HBot HTop ) (midGt HTop) h_mid h_top
     else -- Final one-step game
           let h_sib := A.sibling { val := p_bot , isLt := HBot }
           let hNode := opHash h_bot h_sib
           if hNode == h_top
           then Winner.Challenger
           else Winner.Challenged

-- Protocol
def MembershipGame (A : ChallengerReq) (D : Challenged) (tHash : Hash) : Winner
  :=
  -- A inits the game.
  match InitC : A.init.pL with
  -- Zero means that there is no path, so A is providing the root.
  | Nat.zero =>
    if H A.init.val == tHash
    then Winner.Challenger
    else Winner.Challenged
  -- If we have a longer path, we go to the second stage of the game.
  | Nat.succ Nat.zero =>
    let h_sib := A.sibling { val := 0 , isLt := by rw [ InitC ]; simp }
    let hNode := opHash (H A.init.val) h_sib
    if hNode == tHash
    then Winner.Challenger
    else Winner.Challenged
  | Nat.succ (Nat.succ x) =>
    MembershipGame_2STG A D
      -- Game range [0 ... |path| - 1 ]
      (A.init.pL-1) 0
      -- Range restrictions
      ( by { rw [ InitC ] ; simp } )
      ( by { rw [ InitC ] ; simp } )
      --
      (A.init.valH) tHash

----------------------------------------
-- * A GoodChallenger

def treeTohashPath ( p : TreePath Value ) : Path :=
  List.map (fun x =>
    match x with
     | Sum.inl l => Sum.inl ( match hash_BTree l with
                              | MTree.node h => h)
     | Sum.inr r => Sum.inr ( match hash_BTree r with
                              | MTree.node h => h)
  )  p

def sumP {α : Type} ( e : Sum α α ) : α :=
  match e with
  | Sum.inl a => a
  | Sum.inr a => a

-- We are going to define a good challenger.
-- Good challengers know the tree.
-- Forgetfull Challenger!
-- def createGoodChallenger
--     ( v : Value ) ( bt : BTree Value) ( path : TreePath Value) ( notRoot : 1 ≤ List.length path )
--     (pathProof : valueInProof v bt = some path )
--     :  ChallengerReq
--     :=
--     let hashPath := treeTohashPath path
--     let halfWay := List.length hashPath / 2
--     let halfFin : Fin (List.length hashPath) :=
--         { val := List.length hashPath / 2
--         , isLt := by {
--                have eqLen : List.length hashPath = List.length path
--                  := by { exact List.length_map path _ }
--                have GtZ : 0 < List.length hashPath
--                  := by { rw [ eqLen ]; apply notRoot }
--                exact Nat.div_lt_self GtZ ( by { simp } )
--           }
--         }
--     { init := ( halfWay , v , sumP (List.get hashPath halfFin) ) -- List.get! hashPath halfWay)
--     , strategy := _
--     , sibling := _
--     }

-- This is a scan computation. I'll write it down first and then Lean it.
def PathComputation ( v : Hash ) ( path : Path ) : List Hash
:= match path with
   | List.nil => List.nil
   | List.cons pS ps =>
     let nodeHash := opHash v pS
     nodeHash :: ( PathComputation nodeHash ps )

-- PathComputation v p = List.drop 1 (ScanPath v p)
def ScanPath ( v : Hash ) ( path : Path ) : List Hash
:= List.scanl opHash v path

def CGoodPlayer
  (v : Value) (path : TreePath Value)
  : ChallengerReq
  :=
    let hashPath := treeTohashPath path
    -- I don't know if the top hash is needed.
    let pathHash := List.reverse $ List.drop 1 $ ScanPath (H v) hashPath
  -- Good Challenger knows that | valH = H val |
  { init := { pL := List.length path
            , val := v
            , valH := H v }
  -- Since we play games in a range | 0 ... init.pL - 1|, we only need to
  -- provide an strategy on such range.
  -- This is equivalent to play finite games. Very finite, as soon as we start
  -- the game, we have a cap to the number of moves.
  , strategy := fun p
             => List.get pathHash { val := p.val
                                  , isLt := by
                                    { have LenEq : pathHash.length = path.length := by
                                      { rw [ List.length_reverse ]
                                        simp
                                        rw [ ScanPath , List.length_scanl]
                                        simp
                                        exact List.length_map _ _
                                      }
                                      rw [ LenEq ]
                                      simp
                                    }}
  , sibling := fun p => List.get (List.reverse hashPath)
                                 { val := p.val
                                 , isLt := by { have LenEq : List.length (List.reverse hashPath) = List.length path :=
                                                     by { rw [ List.length_reverse ]
                                                          exact List.length_map path _ }
                                                rw [ LenEq ]
                                                simp
                                              } }
  }
