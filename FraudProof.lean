-- This module serves as the root of the `FraudProof` library.
-- Import modules here that should be built as part of the library.
import FraudProof.Value
import FraudProof.Hash
import FraudProof.BTree
import FraudProof.MTree


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

-- Simpler definition.
    structure ChallengerReq where
    -- First, propposes a value at a given position with a given hash.
    init : Nat × Value × Hash
    -- Then, at each step it provides a Hash.
    strategy : Nat → Hash
    -- Final strategy, is a sibling.
    sibling : Nat → Hash

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

-- Game description that works.
def MembershipGame : ChallengerReq → Challenged → (p_bot p_top : Nat) → (h_bot h_top : Hash) → Winner
     := fun A D p_bot p_top h_bot h_top =>
     if (p_bot > (p_top + 1))
     then
           let p_mid := (p_bot + p_top) / 2 -- middle position
           let h_mid := A.strategy p_mid
           match D.strategy h_bot h_mid h_top with
             | Side.Left => MembershipGame A D p_bot p_mid  h_bot h_mid
             | Side.Right => MembershipGame A D p_mid p_top h_mid h_top
     else
           let h_sib := A.sibling p_bot
           if (h_bot ⊕ h_sib) == h_top
           then Winner.Challenger
           else Winner.Challenged

----------------------------------------
-- * A GoodChallenger

def treeTohashPath ( p : TreePath ) : Path :=
  List.map (fun x =>
    match x with
     | Sum.inl l => Sum.inl ( match hash_BTree l with
                              | MTree.node h => h)
     | Sum.inr r => Sum.inr ( match hash_BTree r with
                              | MTree.node h => h)
  )  p

-- We are going to define a good challenger.
-- Good challengers know the tree.
def createGoodChallenger ( v : Value ) ( bt : BTree) ( path : TreePath) (pathProof : valueInProof v bt = some path )
    :  ChallengerReq
    :=
    let hashPath := treeTohashPath path
    let halfWay := List.length hashPath / 2
    let halfFin : Fin (List.length hashPath) :=
      { val := List.length hashPath / 2
      , isLt := _
      }
    { init := ( halfWay , v , _ ) -- List.get! hashPath halfWay)
    , strategy := _
    , sibling := _
    }
