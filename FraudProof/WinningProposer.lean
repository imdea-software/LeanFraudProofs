-- Definitions
import FraudProof.Value
import FraudProof.MTree
import FraudProof.Hash

-- Players
import FraudProof.Players

-- Extra Props
import FraudProof.BToMTree -- ( hashElem, treeTohashPath, sumP, ScanPath )
import FraudProof.List -- Extra List lemmas showing properties between ScanL -- Get -- Foldl
import FraudProof.Nat -- ( Extra lemmas )

-- Math Lib
import Mathlib.Data.List.Basic

-- disabling autoimplicit
set_option autoImplicit false


open Proposer

-- * Property Definition
----------------------------------------------------------------------
--  Winning Proposer Definition!
namespace WinningProposer


section GoodProp
  variable (n : Nat)
  variable (Player : HC n)

  @[simp]
  def GoodInit (h : Hash) := Player.pathNode 0 = h

  @[simp]
  def GoodRoot (h : Hash ) := Player.pathNode ⟨ n , by simp ⟩ = h

  @[simp]
  def GoodMid  :=
    forall (m : Nat) (mLtn : m < n ),
    Player.pathNode ⟨ (m + 1) , by apply Nat.succ_lt_succ;assumption⟩ =
    opHash ( Player.pathNode ⟨ m , by apply Nat.lt_add_one_of_lt; assumption ⟩) ( Player.pathSib ⟨ m , mLtn ⟩ )
end GoodProp

-- Definition of winning proposers.
-- Giving the size of the game |pathLen| and two hashes |hv,hr|
-- Hash |hv| represents the hash of a value |v : Value| we are showing belongs
-- to a merklee tree |mt : MTree|.
-- Hash |hr| is the hash of |mt|.
structure PropHash (pathLen : Nat) (hv hr : Hash) where
  -- The path is grater than 0. Otherwise, we don't have a tree.
  pathLenNZ : 0 < pathLen
  -- We have a strategy.
  strategies : HC pathLen
  -- First node in our path is hash |hv|
  nodeZero : GoodInit pathLen strategies hv
  -- Last node in our path is hash |hr|
  nodeRoot : GoodRoot pathLen strategies hr
  -- All nodes are related: path[n+1] = path[n] ⊕ sib[n]
  allGames : GoodMid pathLen strategies

-- Higher definition linking the intuition stated before.
def WinningProp (pathLen : Nat) (v : Value) (mt : MTree)
   := PropHash pathLen (H v) mt.hash

end WinningProposer

namespace GCShifts
-- We can shift good proposers by basically shifting their stategies and
-- structures.
--
-- We have two morphisims
-- Shift left and right
open WinningProposer

def DropHead (pLen : Nat) (hv hr : Hash)(A : PropHash (pLen + 1 + 1) hv hr) :
  PropHash (pLen+1) (A.strategies.pathNode ⟨ 1 , by simp ⟩) hr :=
  { pathLenNZ := by simp
  , strategies := DropHeadHC A.strategies
  , nodeZero := by
             unfold GoodInit
             unfold DropHeadHC
             simp
  , nodeRoot := by
             unfold GoodRoot
             unfold DropHeadHC
             simp
             exact A.nodeRoot
  , allGames := by
             simp
             unfold DropHeadHC
             simp
             intros m mLt
             exact A.allGames (m+1) (by simp; assumption)
  }

def DropLast (pLen : Nat) (hv hr : Hash) (A : PropHash (pLen + 1 + 1) hv hr)
  : PropHash (pLen + 1) hv (A.strategies.pathNode ⟨ pLen + 1, by simp ⟩) :=
  { pathLenNZ := by simp
  , strategies := DropLastHC A.strategies
  , nodeZero := by
             unfold DropLastHC
             simp
             exact A.nodeZero
  , nodeRoot := by
             unfold DropLastHC
             simp
  , allGames := by
             unfold DropLastHC
             simp
             intros m mLt
             exact A.allGames m (by exact Nat.lt_succ_of_lt mLt)
  }


end GCShifts
namespace GCLemmas
  lemma GChalOneH { hv hr : Hash } ( gc : WinningProposer.PropHash 1 hv hr):
    opHash hv (gc.strategies.pathSib 0) = hr
    := by
    cases gc with
    | mk pLen str nZ nR allg =>
      simp
      rw [ <- nZ ]
      rw [ <- nR ]
      simp
      have g0 := allg 0 (by simp)
      simp at g0
      rw [ g0 ]

end GCLemmas
----------------------------------------------------------------------

----------------------------------------------------------------------
-- * Construction of Winning Proposers
-- Here we show how to build a Winnong Proposer.
-- We show that |PropHash| is inhabited.
namespace OldLemmas
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

-- Similar to the nodes, proposers may be required to provide sibling hashes.
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

end OldLemmas
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
namespace Build
section HashProposer
  -- Let |h| be a |Hash| and |path| a path in the tree leading to a value |v|,
  -- such that |H v| = |h|
  variable (h : Hash)
  -- variable (path : TreePath Value)
  variable (path : Path)

  -- Definition!
  def HPlayer : HC path.length
    :=
    -- let pathElem : Path := treeTohashPath path
    -- have eqLen : pathElem.length = path.length := by exact List.length_map _ _
    { pathNode := fun p =>
      match p with
      | Fin.mk pVal pLt =>
        (List.scanl opHash h path)[pVal]'( by rw [List.length_scanl] ; assumption )
    , pathSib := List.get path
    -- fun s => match s with
    --                       | Fin.mk sVal sLt => List.get path ⟨ sVal  , sLt⟩
    }

  -- pathNode[n+1] = pathNode[n] ⊕ pathSib[n]
  lemma midGameCorrect:
    forall (n : Nat) (nLt : n < path.length),
      let HP := HPlayer h path
      HP.pathNode ⟨ n + 1 , by simp; assumption ⟩
      = opHash (HP.pathNode ⟨ n , by trans path.length; assumption; simp ⟩) (HP.pathSib ⟨ n , nLt⟩)
      := by
      intros n nLt
      unfold HPlayer
      simp
      rw [ ScanlGetN, ScanlGetN ]
      rw [ <- List.foldl_concat opHash ]
      rw [ <- List.concat_nil ]
      rw [ List.append_concat, List.append_nil, List.take_concat_get ]

      -- Obligations
      { trans path.length; assumption; simp}
      { simp; assumption }
end HashProposer

  def WinningProposerPath
    (h : Hash) (path : Path)
    ( pathNNil : 0 < path.length )
    : WinningProposer.PropHash path.length h (listPathHashes h path)
    :=
    { pathLenNZ := pathNNil
    , strategies := HPlayer h path
    , nodeZero := by simp [ HPlayer ]
    , nodeRoot := by simp [ HPlayer ]
                     rw [ ScanlGetN ]
                     simp
                     simp
    , allGames := by simp
                     intros m mLtn
                     exact midGameCorrect h path m mLtn
    }

  def WinningProposerTreePath (v : Value) (path : TreePath Value) (pathNNil : 0 < path.length)
  := WinningProposerPath (H v) (treeTohashPath path) (by unfold treeTohashPath; rw [ List.length_map ]; assumption)

  @[simp]
  def LP_HPlayer {m n : Nat} (eqMN : m = n) (p : HC m) : HC n
  := { pathNode := fun k => match k with
                            | ⟨ kV , kLtn ⟩ => p.pathNode ⟨ kV , by rw [ eqMN ]; assumption ⟩
     , pathSib := fun k => match k with
                            | ⟨ kV , kLtn ⟩ => p.pathSib ⟨ kV , by rw [ eqMN ]; assumption ⟩
     }


  -- Let |v| be a value, |bt| a binary tree of values, such thah |v| is in |bt|,
  -- i.e. there is a non-empty path |path| from |v| to the root.
  -- We can create a winning strategy.
  def WProposerCreate ( v : Value ) (bt : BTree Value) (path : TreePath Value) (pathNNil : 0 < path.length)
      ( vInTree : valueInProof v bt = some path )
      : WinningProposer.WinningProp path.length v (hash_BTree bt)
      := have eqLen : path.length = List.length (treeTohashPath path) := (by unfold treeTohashPath; rw [ List.length_map ])
    { pathLenNZ := pathNNil
    , strategies := LP_HPlayer (by rw [ eqLen ]) (HPlayer (H v) (treeTohashPath path))
    , nodeZero := by simp [HPlayer]
    , nodeRoot := by simp [HPlayer]
                     rw [ ScanlGetN, eqLen]
                     unfold treeTohashPath
                     rw [ List.take_length]
                     exact VinTree v bt path vInTree
                     -- Proof Obligations
                     { simp }
    , allGames := by simp; intros m mLtn
                     exact midGameCorrect (H v) (List.map hashElem path) m (by rw [ List.length_map ]; assumption)
    }


end Build
----------------------------------------------------------------------

----------------------------------------------------------------------

-- * Deprecated
----------------------------------------------------------------------
-- Good (by definition) Player
-- Since we play games in a range | 0 ... init.pL - 1|, we only need to
-- provide an strategy on such range.
-- This is equivalent to play finite games. Very finite, as soon as we start
-- the game, we have a cap to the number of moves.
-- @[simp]
-- def CGoodPlayer (v : Value) (path : TreePath Value)
--   : Proposer path.length
--   :=
--     let hashPath : Path := treeTohashPath path
--     have EqLen : hashPath.length = path.length := by
--       exact List.length_map _ _
--     let strategies :=
--       { node := fun p => match p with
--              | Fin.mk pVal pLt =>
--              (
--              RevStr $ -- The game goes walking the path /backwards/
--              Drop0  $ -- NodeHashPath0 = ( H v )
--              NodeHashPathF (H v) hashPath
--              ) ⟨ pVal ,  by rw [ EqLen ]; apply pLt⟩
--       , sibling := RevStr (@SibsF' _ hashPath ( by rw [ EqLen ] ))
--       }
--   -- Good Proposer knows that | valH = H val |
--   { value := v
--   , hashStr := strategies
--   }
----------------------------------------------------------------------

-- lemma GPlEmpty : (CGoodPlayer v []).hashStr.sibling n = nE
--   := by
--   unfold CGoodPlayer
--   simp
--   cases n
--   contradiction
----------------------------------------------------------------------

-- section GoodPlayerProp
--   variable (v : Value )
--   variable (p : TreePathElem Value)
--   variable (path' : TreePath Value)

-- -- Node [ last  ] = opHash (H v) (Sibling last)
--   lemma goodStrBottomGame :
--     let path := p :: path'
--     let pLast : Fin path.length := ⟨ path.length - 1 , by rw [ List.length ]; simp ⟩
--     let GP := CGoodPlayer v path
--     GP.hashStr.node pLast = opHash ( H v ) (GP.hashStr.sibling  pLast)
--     := by
--     unfold CGoodPlayer
--     unfold RevStr
--     unfold Drop0
--     unfold NodeHashPathF
--     simp

--   -- Mid-games are interesting.
--   -- Node [ n ] = opHash Node[n+1] Sib[n]
--   lemma goodMidGame :
--     let path := p :: path'
--     let GP := CGoodPlayer v path
--     forall (n : Nat) ( lt : n < path.length - 1),
--     GP.hashStr.node ⟨ n , by trans path.length - 1; assumption; rw [ List.length ]; simp⟩
--     = opHash ( GP.hashStr.node ⟨ n + 1 , by rw [ List.length ] at *; simp at *; assumption ⟩ )
--             (GP.hashStr.sibling ⟨ n , by trans path.length - 1; assumption; rw [ List.length ]; simp⟩ )
--     := by
--       simp
--       intros n nLt
--       unfold CGoodPlayer
--       unfold NodeHashPathF
--       simp
--       rw [ ScanlGetN ]
--       rw [ ScanlGetN ]
--       -- rw [ <- opHash ]
--       -- rw [ <- opHash ]
--       rw [ <- List.foldl  ]
--       rw [ <- List.foldl  ]
--       rw [ <- List.map_take ]
--       rw [ <- List.map_take ]
--       have foldC := @List.foldl_concat PathElem Hash opHash (H v) ((hashElem p :: List.map hashElem path')[List.length path' - n]) ( (hashElem p :: List.map hashElem (List.take (List.length path' - (n + 1)) path')) )
--       rw [ <- foldC ]
--       clear foldC
--       rw [ List.map_take ]
--       rw [ List.map_take ]
--       rw [ <- List.take_cons]
--       rw [ <- List.take_cons]
--       have eqMS : (List.length path' - (n + 1)).succ = List.length path' - n := by
--            { rw [ <- Nat.succ_sub ]; simp; exact Nat.succ_le_of_lt nLt }
--       rw [ eqMS ]
--       rw [ lemmaTakeAppend ]

--       -- Proof obligations
--       { simp ; exact LtToRevSucc }
--       { simp ; exact LtToRev }

-- end GoodPlayerProp
-- ----------------------------------------------------------------------
