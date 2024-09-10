-- Definitions
import FraudProof.Value
import FraudProof.MTree
import FraudProof.Hash

import FraudProof.Players

-- Extra Props
import FraudProof.BToMTree -- ( hashElem, treeTohashPath, sumP, ScanPath )
import FraudProof.List -- Extra List lemmas showing properties between ScanL -- Get -- Foldl
import FraudProof.Nat -- ( Extra lemmas )

-- Math Lib
-- import Mathlib.Data.List.Basic
-- import Batteries.Data.List.Basic -- foldl
-- import Mathlib.Tactic.Ring -- (ring, ring-rf) tactics
-- import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

----------------------------------------------------------------------
-- Good Prop
open Challenger

namespace GoodChallenger
section GoodProp
  variable (n : Nat)
  variable (Player : HC n)

  def GoodValue (v : Value) := Player.pathNode 0 = ( H v )

  def GoodRoot ( mt : MTree ) := Player.pathNode (n - 1) = mt.hash

  def GoodMid  :=
    forall (m : Nat) (nLt : m < n - 1 ),
    have mLtn : m < n := by
      trans n - 1 ; assumption
      simp
      cases n with
      | zero => simp at nLt
      | succ _ => simp
    Player.pathNode ⟨ (m + 1) , by apply Nat.succ_lt_succ;assumption⟩ =
    opHash ( Player.pathNode ⟨ m , by apply Nat.lt_add_one_of_lt; assumption ⟩) ( Player.pathSib ⟨ m , mLtn ⟩ )
end GoodProp

-- Definition of a Good Challenger, i.e. a challenger that always wins.
-- GoodChallenger of value |v| in tree |mt|
structure GoodChal (v : Value) (mt : MTree) where
  pathLen : Nat
  pathLenNZ : 0 < pathLen
  strategies : HC pathLen
  nodeZero : GoodValue pathLen strategies v
  nodeRoot : GoodRoot pathLen strategies mt
  allGames : GoodMid pathLen strategies

end GoodChallenger


-- def getLasts {α : Type} {n : Nat} (m : Fin n) ( mp : Fin n → α ) : List α :=
--   match m with
--   | ⟨ m' , lmn ⟩ => match m' with
--                     | .zero => []
--                     | .succ pm => mp ⟨ n - pm , _⟩ :: getLasts ⟨ pm , _ ⟩ mp

-- def GoodChallengerProp ( n : Nat )
--     (gc : Challenger n)
--     ( bt  : MTree )
--     : Prop :=
--     bt.hash = gc.hashStr.node ⟨ 0 , _ ⟩
--     ∧
--     forall ( i : Fin n ), gc.hashStr.node i = List.foldl opHash (H gc.value) (getLasts i gc.hashStr.sibling )
--
--
----------------------------------------------------------------------

----------------------------------------------------------------------
-- Strategy definitions.

----------------------------------------
-- Definition of an array of hashes based on a path.
-- It defines hashes in a path.
-- @[simp]
def NodeHashPathF ( hv : Hash ) ( path : Path ) (n : Fin (path.length + 1)) : Hash
:= match n with
  | Fin.mk nval nproof =>
    (ScanPath hv path)[nval]'( by unfold ScanPath; rw [ List.length_scanl ]; assumption )

-- Same as before, but with out Fin.
def NodeHashPath ( hv : Hash ) ( path : Path ) ( n : Nat ) ( nLt : n < (path.length + 1) ) : Hash :=
  have nL : n < (ScanPath hv path).length := by unfold ScanPath; rw [ List.length_scanl ]; assumption
  (ScanPath hv path)[n]

-- Similar to the nodes, challengers may be required to provide sibling hashes.
@[simp]
def SibsF' { m : Nat} (path : Path) {eqLen : m = path.length} (n : Fin m) : PathElem
  := match n with
  | Fin.mk nVal nLt => List.get path ⟨ nVal , by rw [ <- eqLen ]; exact nLt ⟩
def Sibs ( path : Path ) ( n : Nat ) ( nLpath : n < path.length ) : PathElem :=
   path[n]
----------------------------------------

----------------------------------------
-- Lemmas
@[simp]
lemma SibsF0 ( p : PathElem ) (path : Path) : @SibsF' _ (p :: path) rfl ⟨ 0 , by simp ⟩ = p := by {
  unfold SibsF'
  simp
}

@[simp]
lemma Sibs0 ( p : PathElem ) (path : Path) {pl : 0 < (p::path).length}:
  Sibs (p :: path) 0 pl = p := by
  unfold Sibs
  simp

@[simp]
lemma hachChainF0 hv ps : NodeHashPathF hv ps 0 = hv := by
  unfold NodeHashPathF
  unfold ScanPath
  simp

@[simp]
lemma hachChain0 hv ps pLt : NodeHashPath hv ps 0 pLt = hv := by
  unfold NodeHashPath
  simp

lemma hashChainF ps ( n : Fin ps.length ) :
  ( hv : Hash ) ->
  NodeHashPathF hv ps { val := n.val + 1, isLt := by simp}
  = opHash ( NodeHashPathF hv ps n ) (@SibsF' _ ps (by simp) n) := by
  unfold NodeHashPathF
  unfold ScanPath
  induction ps with
  | nil => {simp at n; cases n with | mk _ isLt => simp at isLt}
  | cons pe pes HInd =>
    simp
    -- unfold SibsF'
    cases NDef : n with
    | mk nVal nLt =>
    --
    cases nVal with
    | zero => simp
    | succ pnVal =>
    simp at *
    intro hV
    have pnLt : pnVal < pes.length := by
      { simp at nLt; assumption }
    rw  [ Fin.forall_iff ] at HInd
    have appN := HInd pnVal pnLt (opHash hV pe)
    unfold SibsF' at appN
    simp at *
    assumption


lemma hashChain  ps :
  (n : Nat) ->
  -- Proof irrelevance ??
  (nLt : n < ps.length ) ->
  (NSuccLt : n + 1 < ps.length + 1 ) ->
  (NLtSucc : n < ps.length + 1 ) ->
  --
  ( hv : Hash ) ->
  NodeHashPath hv ps (n + 1) NSuccLt -- ( by simp; assumption )
  = opHash ( NodeHashPath hv ps n NLtSucc) -- ( by trans ps.length; assumption; simp) )
           (Sibs ps n nLt ) -- ( by assumption )
  := by
  unfold NodeHashPath
  simp
  unfold ScanPath
  induction ps with
  | nil =>
     intros n nAbs
     simp at nAbs
  | cons pe pes HInd =>
    intros n nInRange pLt ltSucc val
    unfold Sibs
    cases n with
    | zero => simp
    | succ pn =>
      simp
      apply HInd
      {simp at nInRange; assumption }
      { simp at ltSucc; assumption }

----------------------------------------------------------------------

----------------------------------------------------------------------
-- Auxiliary defs to build strategies
--
-- Fin n -> α are arrays of length n
-- The following function reverses it.
@[simp]
def RevStr {α : Type} { n : Nat  }( f : Fin n → α ) : Fin n → α :=
  fun a => match a with
  | Fin.mk val aLt => f ⟨ n - 1 - val , by exact Nat.sub_one_sub_lt aLt ⟩

-- Drop first
@[simp]
def Drop0 { α : Type } {n : Nat} ( f : Fin (n + 1) → α ) : Fin n → α :=
  fun an => match an with
  | Fin.mk nVal nLt => f ⟨ nVal + 1, by simp ; assumption⟩
----------------------------------------------------------------------

----------------------------------------------------------------------
-- Good (by definition) Player
-- Since we play games in a range | 0 ... init.pL - 1|, we only need to
-- provide an strategy on such range.
-- This is equivalent to play finite games. Very finite, as soon as we start
-- the game, we have a cap to the number of moves.
-- @[simp]
def CGoodPlayer (v : Value) (path : TreePath Value)
  : Challenger path.length
  :=
    let hashPath : Path := treeTohashPath path
    have EqLen : hashPath.length = path.length := by
      exact List.length_map _ _
    let strategies :=
      { node := fun p => match p with
             | Fin.mk pVal pLt =>
             (
             RevStr $ -- The game goes walking the path /backwards/
             Drop0  $ -- NodeHashPath0 = ( H v )
             NodeHashPathF (H v) hashPath
             ) ⟨ pVal ,  by rw [ EqLen ]; apply pLt⟩
      , sibling := RevStr (@SibsF' _ hashPath ( by rw [ EqLen ] ))
      }
  -- Good Challenger knows that | valH = H val |
  { value := v
  , hashStr := strategies
  }
----------------------------------------------------------------------

lemma GPlEmpty : (CGoodPlayer v []).hashStr.sibling n = nE
  := by
  unfold CGoodPlayer
  simp
  cases n
  contradiction
----------------------------------------------------------------------


----------------------------------------------------------------------
namespace CorrectHashPlayer
section VarE
-- Only Hash Player
--
-- given a Hash and a Path
variable (h : Hash)
variable (path : TreePath Value)

def HCPlayerBotUp : HC path.length
  :=
  let pathElem : Path := treeTohashPath path
  have eqLen : pathElem.length = path.length := by exact List.length_map _ _
  { pathNode := fun p =>
    match p with
    | Fin.mk pVal pLt =>
      (List.scanl opHash h pathElem)[pVal]'( by rw [List.length_scanl, eqLen] ; assumption )
  , pathSib := fun s => match s with
                        | Fin.mk sVal sLt => List.get pathElem ⟨ sVal  ,  by rw [ eqLen]; assumption⟩
  }

-- pathNode[n+1] = pathNode[n] ⊕ pathSib[n]
lemma midGameCorrect {lenGt : 0 < path.length}:
  forall (n : Nat) (nLt : n < path.length - 1),
    let HP := HCPlayerBotUp h path
    HP.pathNode ⟨ n+ 1 , by simp; exact Nat.lt_of_lt_pred nLt ⟩ = opHash (HP.pathNode n) (HP.pathSib ⟨ n , by trans path.length-1; assumption;simp; assumption⟩) := by
    intros n nLt
    unfold HCPlayerBotUp
    simp
    rw [ ScanlGetN ]
    rw [ ScanlGetN ]
    rw [ <- List.foldl_concat opHash ]
    have nEq : n % (List.length path + 1) = n := by { exact Nat.mod_eq_of_lt (by trans path.length - 1; assumption;trans path.length;simp; assumption; simp)}
    rw [ nEq ]
    rw [ <- List.map_take ]
    rw [ <- List.map_take ]
    rw [ <- List.concat_nil ]
    rw [ List.append_concat]
    rw [ List.append_nil ]
    rw [<- List.map_concat]
    rw [ List.take_concat_get ]
    -- Obligations
    { rw [ List.length_map ]
      apply Nat.mod_lt
      simp
    }
    { simp; exact Nat.lt_of_lt_pred nLt}
end VarE
end CorrectHashPlayer
----------------------------------------------------------------------

----------------------------------------------------------------------
section GoodPlayerProp
  variable (v : Value )
  variable (p : TreePathElem Value)
  variable (path' : TreePath Value)

-- Node [ last  ] = opHash (H v) (Sibling last)
  lemma goodStrBottomGame :
    let path := p :: path'
    let pLast : Fin path.length := ⟨ path.length - 1 , by rw [ List.length ]; simp ⟩
    let GP := CGoodPlayer v path
    GP.hashStr.node pLast = opHash ( H v ) (GP.hashStr.sibling  pLast)
    := by
    unfold CGoodPlayer
    unfold RevStr
    unfold Drop0
    unfold NodeHashPathF
    simp

  -- Mid-games are interesting.
  -- Node [ n ] = opHash Node[n+1] Sib[n]
  lemma goodMidGame :
    let path := p :: path'
    let GP := CGoodPlayer v path
    forall (n : Nat) ( lt : n < path.length - 1),
    GP.hashStr.node ⟨ n , by trans path.length - 1; assumption; rw [ List.length ]; simp⟩
    = opHash ( GP.hashStr.node ⟨ n + 1 , by rw [ List.length ] at *; simp at *; assumption ⟩ )
            (GP.hashStr.sibling ⟨ n , by trans path.length - 1; assumption; rw [ List.length ]; simp⟩ )
    := by
      simp
      intros n nLt
      unfold CGoodPlayer
      unfold NodeHashPathF
      simp
      rw [ ScanlGetN ]
      rw [ ScanlGetN ]
      -- rw [ <- opHash ]
      -- rw [ <- opHash ]
      rw [ <- List.foldl  ]
      rw [ <- List.foldl  ]
      rw [ <- List.map_take ]
      rw [ <- List.map_take ]
      have foldC := @List.foldl_concat PathElem Hash opHash (H v) ((hashElem p :: List.map hashElem path')[List.length path' - n]) ( (hashElem p :: List.map hashElem (List.take (List.length path' - (n + 1)) path')) )
      rw [ <- foldC ]
      clear foldC
      rw [ List.map_take ]
      rw [ List.map_take ]
      rw [ <- List.take_cons]
      rw [ <- List.take_cons]
      have eqMS : (List.length path' - (n + 1)).succ = List.length path' - n := by
           { rw [ <- Nat.succ_sub ]; simp; exact Nat.succ_le_of_lt nLt }
      rw [ eqMS ]
      rw [ lemmaTakeAppend ]

      -- Proof obligations
      { simp ; exact LtToRevSucc }
      { simp ; exact LtToRev }

end GoodPlayerProp
----------------------------------------------------------------------
