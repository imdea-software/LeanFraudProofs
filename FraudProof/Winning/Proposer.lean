-- Definitions
-- import FraudProof.DataStructures.Value
import FraudProof.DataStructures.MTree
import FraudProof.DataStructures.Hash

-- Players
import FraudProof.Players

-- Extra Props
import FraudProof.Extras.BToMTree -- ( hashElem, treeTohashPath, sumP, ScanPath )
import FraudProof.Extras.List -- Extra List lemmas showing properties between ScanL -- Get -- Foldl
import FraudProof.Extras.Nat -- ( Extra lemmas )

-- Math Lib
import Mathlib.Data.List.Basic


open Proposer

-- * Property Definition
----------------------------------------------------------------------
--  Winning Proposer Definition!
namespace WinningProposer

section GoodProp
  variable {ℍ : Type}
  variable (n : Nat)
  variable (Player : HC ℍ n)

  @[simp]
  def GoodInit (h : ℍ) := Player.pathNode 0 = h

  @[simp]
  def GoodRoot (h : ℍ ) := Player.pathNode ⟨ n , by simp ⟩ = h

  @[simp]
  def GoodMid [HashMagma ℍ]:=
    forall (m : Nat) (mLtn : m < n ),
    Player.pathNode ⟨ (m + 1) , by apply Nat.succ_lt_succ;assumption⟩ =
    opHash ( Player.pathNode ⟨ m , by apply Nat.lt_add_one_of_lt; assumption ⟩) ( Player.pathSib ⟨ m , mLtn ⟩ )
end GoodProp

-- Definition of winning proposers.
-- Giving the size of the game |pathLen| and two hashes |hv,hr|
-- Hash |hv| represents the hash of a value |v : Value| we are showing belongs
-- to a merklee tree |mt : MTree|.
-- Hash |hr| is the hash of |mt|.
-- Another definition is that |PropHash n hv hr| is a path from |hv| to |hr| of
-- length |n|.
structure PropHash {ℍ : Type}[HashMagma ℍ](pathLen : Nat) (hv hr : ℍ) where
  -- The path is grater than 0. Otherwise, we don't have a tree.
  pathLenNZ : 0 < pathLen
  -- We have a strategy.
  strategies : HC ℍ pathLen
  -- First node in our path is hash |hv|
  nodeZero : GoodInit pathLen strategies hv
  -- Last node in our path is hash |hr|
  nodeRoot : GoodRoot pathLen strategies hr
  -- All nodes are related: path[n+1] = path[n] ⊕ sib[n]
  allGames : GoodMid pathLen strategies

-- Higher definition linking the intuition stated before.
def WinningProp {α ℍ : Type}[m : Hash α ℍ][HashMagma ℍ](pathLen : Nat) (v : α) (mt : MTree ℍ)
   := PropHash pathLen (m.mhash v) mt

lemma WinningOne {ℍ : Type}[HashMagma ℍ]{hb ht : ℍ} (P : PropHash 1 hb ht)
      : opHash hb (P.strategies.pathSib ⟨ 0 , by omega ⟩) = ht
      := by
        match P with
        | PropHash.mk NZ str nZ nR allGames =>
        unfold GoodInit at *
        unfold GoodRoot at *
        unfold GoodMid at *
        simp
        rw [ <- nZ , <- nR]
        have a := allGames 0 (by simp)
        rw [a]
        congr

end WinningProposer

namespace GCShifts
-- We can shift good proposers by basically shifting their stategies and
-- structures.
--
-- We have two morphisims
-- Drop Head, Drop Last
open WinningProposer

variable {ℍ : Type}

def DropHead [HashMagma ℍ](pLen : Nat) (hv hr : ℍ)(A : PropHash (pLen + 1 + 1) hv hr) :
  PropHash (pLen+1) (A.strategies.pathNode ⟨ 1 , by simp ⟩) hr :=
  { pathLenNZ := by simp
  , strategies := DropHeadHC ℍ A.strategies
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

def DropLast [HashMagma ℍ](pLen : Nat) (hv hr : ℍ) (A : PropHash (pLen + 1 + 1) hv hr)
  : PropHash (pLen + 1) hv (A.strategies.pathNode ⟨ pLen + 1, by simp ⟩) :=
  { pathLenNZ := by simp
  , strategies := DropLastHC ℍ A.strategies
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

namespace GCOps
-- Here we define operations over 'Good Proposers'
-- We should merge with the above section, but for now I'll keep it split.

open WinningProposer
variable {ℍ : Type}

def eqLength [HashMagma ℍ]{hb ht : ℍ} (n m : Nat) (eqnm : n = m) (P : PropHash n hb ht)
  : PropHash m hb ht
  := { pathLenNZ := by rw [ <- eqnm]; exact P.pathLenNZ
     , strategies :=
       { pathNode := fun p => match p with
                         | ⟨ pVal, pLt ⟩ => P.strategies.pathNode ⟨ pVal , by omega ⟩
       , pathSib := fun p => match p with
                         | ⟨ pVal, pLt ⟩ => P.strategies.pathSib ⟨ pVal , by omega ⟩
       }
     , nodeZero := by have pNZ := P.nodeZero
                      simp at *
                      assumption
     , nodeRoot := by have pR := P.nodeRoot
                      simp at *
                      have eqF : P.strategies.pathNode ⟨ n , by omega ⟩ = P.strategies.pathNode ⟨ m , by omega ⟩ := by congr
                      rw [ <- eqF ]
                      assumption
     , allGames := by have pAG := P.allGames
                      simp at *
                      intros w wLtm
                      exact pAG w (by omega)
}

def take_proposer [HashMagma ℍ]{hb ht : ℍ} (m n : Nat) (mNZ : 0 < m) (hmn : m < n + 1 )
  (P : PropHash n hb ht)
 : PropHash m hb (P.strategies.pathNode ⟨ m , by assumption ⟩)
 := { pathLenNZ := mNZ
    , strategies := Proposer.takeHC ℍ m (by omega) P.strategies
    , nodeZero := by have pNodeZ := P.nodeZero
                     simp [takeHC] at *
                     assumption
    , nodeRoot := by simp [takeHC] at *
    , allGames := by have pAllGames := P.allGames
                     simp [takeHC] at *
                     intros w wLtm
                     exact pAllGames w (by omega)
}

def drop_proposer [HashMagma ℍ]{hb ht: ℍ} (m n : Nat) (hmn : m < n)
  (P : PropHash n hb ht)
  : PropHash (n - m) (P.strategies.pathNode ⟨ m , by omega ⟩) ht
  := { pathLenNZ := by omega
     , strategies := dropHC ℍ m (by omega) P.strategies
     , nodeZero := by simp [ dropHC ]
     , nodeRoot := by have lt := P.nodeRoot
                      simp [ dropHC] at *
                      have eqN : m + ( n - m ) = n := by omega
                      have feq : P.strategies.pathNode ⟨m + (n - m), by omega⟩ = P.strategies.pathNode ⟨n, by omega ⟩ := by congr
                      rw [ feq ]
                      assumption
     , allGames := by have pAllGames := P.allGames
                      simp [dropHC] at *
                      intros m1 m1Ltn
                      exact pAllGames (m + m1) ( by omega )
}

end GCOps

namespace GCLemmas
  variable {ℍ : Type}
  lemma GChalOneH [HashMagma ℍ]{ hv hr : ℍ } ( gc : WinningProposer.PropHash 1 hv hr):
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
variable {ℍ : Type}
-- Definition of an array of hashes based on a path.
-- It defines hashes in a path.
-- @[simp]
def NodeHashPathF [HashMagma ℍ]( hv : ℍ ) ( path : Path ℍ) (n : Fin (path.length + 1)) : ℍ
:= match n with
  | Fin.mk nval nproof =>
    (ScanPath hv path)[nval]'( by unfold ScanPath; rw [ List.length_scanl ]; assumption )

-- Same as before, but with out Fin.
def NodeHashPath [HashMagma ℍ]( hv : ℍ ) ( path : Path ℍ) ( n : Nat ) ( nLt : n < (path.length + 1) ) : ℍ :=
  have nL : n < (ScanPath hv path).length := by unfold ScanPath; rw [ List.length_scanl ]; assumption
  (ScanPath hv path)[n]

-- Similar to the nodes, proposers may be required to provide sibling hashes.
@[simp]
def SibsF' { m : Nat} (path : Path ℍ) {eqLen : m = path.length} (n : Fin m) : PathElem ℍ
  := match n with
  | Fin.mk nVal nLt => List.get path ⟨ nVal , by rw [ <- eqLen ]; exact nLt ⟩
def Sibs ( path : Path ℍ) ( n : Nat ) ( nLpath : n < path.length ) : PathElem ℍ :=
   path[n]
----------------------------------------

----------------------------------------
-- Lemmas
@[simp]
lemma SibsF0 ( p : PathElem ℍ) (path : Path ℍ) : @SibsF' _ _ (p :: path) rfl ⟨ 0 , by simp ⟩ = p := by {
  unfold SibsF'
  simp
}

@[simp]
lemma Sibs0 ( p : PathElem ℍ ) (path : Path ℍ) {pl : 0 < (p::path).length}:
  Sibs (p :: path) 0 pl = p := by
  unfold Sibs
  simp

@[simp]
lemma hachChainF0 [o : HashMagma ℍ] hv ps : @NodeHashPathF ℍ o hv ps 0 = hv := by
  unfold NodeHashPathF
  unfold ScanPath
  simp

@[simp]
lemma hachChain0 [o : HashMagma ℍ] hv ps pLt : @NodeHashPath ℍ o hv ps 0 pLt = hv := by
  unfold NodeHashPath
  simp

lemma hashChainF [HashMagma ℍ] ps ( n : Fin ps.length ) :
  ( hv : ℍ ) ->
  NodeHashPathF hv ps { val := n.val + 1, isLt := by simp}
  = opHash ( NodeHashPathF hv ps n ) (@SibsF' ℍ _ ps (by simp) n) := by
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
    have pnLt : pnVal < pes.length := by { simp at nLt; assumption }
    rw  [ Fin.forall_iff ] at HInd
    have appN := HInd pnVal pnLt (opHash hV pe)
    -- unfold SibsF' at appN
    simp at *
    rw [appN]
    -- have eqmod : (hV :: List.scanl opHash (opHash hV pe) pes)[(pnVal + 1) % (pes.length + 1 + 1)]
    --               = (List.scanl opHash (opHash hV pe) pes)[(pnVal + 1) % (pes.length + 1 )] := sorry
    sorry -- Broke after update
    -- assumption


lemma hashChain [HashMagma ℍ]  ps :
  (n : Nat) ->
  -- Proof irrelevance ??
  (nLt : n < ps.length ) ->
  (NSuccLt : n + 1 < ps.length + 1 ) ->
  (NLtSucc : n < ps.length + 1 ) ->
  --
  ( hv : ℍ ) ->
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
variable (ℍ : Type)
    section HashProposer
    -- Let |h| be a |Hash| and |path| a path in the tree leading to a value |v|,
    -- such that |H v| = |h|
    variable (h : ℍ)
    -- variable (path : TreePath Value)
    variable (path : Path ℍ)

    -- Definition!
    def HPlayer [HashMagma ℍ]: HC ℍ path.length
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
    lemma midGameCorrect [HashMagma ℍ]:
        forall (n : Nat) (nLt : n < path.length),
        let HP := HPlayer ℍ h path
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
    [HashMagma ℍ]
    (h : ℍ) (path : Path ℍ)
    ( pathNNil : 0 < path.length )
    : WinningProposer.PropHash path.length h (listPathHashes h path)
    :=
    { pathLenNZ := pathNNil
    , strategies := HPlayer ℍ h path
    , nodeZero := by simp [ HPlayer ]
    , nodeRoot := by simp [ HPlayer ]
                     rw [ ScanlGetN ]
                     simp
                     simp
    , allGames := by simp; intros m mLtn; exact midGameCorrect ℍ h path m mLtn
    }

def WinningProposerTreePath {α :Type}[o : Hash α ℍ][HashMagma ℍ](v : α) (path : TreePath α) (pathNNil : 0 < path.length)
  := WinningProposerPath ℍ (o.mhash v) (treeTohashPath path) (by unfold treeTohashPath; rw [ List.length_map ]; assumption)

@[simp]
def LP_HPlayer {m n : Nat} (eqMN : m = n) (p : HC ℍ m) : HC ℍ n
:= { pathNode := fun k => match k with
                        | ⟨ kV , kLtn ⟩ => p.pathNode ⟨ kV , by rw [ eqMN ]; assumption ⟩
    , pathSib := fun k => match k with
                        | ⟨ kV , kLtn ⟩ => p.pathSib ⟨ kV , by rw [ eqMN ]; assumption ⟩
    }


  -- Let |v| be a value, |bt| a binary tree of values, such thah |v| is in |bt|,
  -- i.e. there is a non-empty path |path| from |v| to the root.
  -- We can create a winning strategy.
def WProposerCreate {α : Type}[aeq : BEq α][aeqLaw : LawfulBEq α][m : Hash α ℍ][op : HashMagma ℍ]( v : α ) (bt : BTree α) (path : TreePath α) (pathNNil : 0 < path.length)
    ( vInTree : valueInProof v bt = some path )
    : @WinningProposer.WinningProp α ℍ m op path.length v bt.hash_BTree
    := have eqLen : path.length = List.length (@treeTohashPath α ℍ _ _ path)
       := (by unfold treeTohashPath; rw [ List.length_map ])
    { pathLenNZ := pathNNil
    , strategies := LP_HPlayer ℍ (by rw [ eqLen ]) (HPlayer ℍ (m.mhash v) (treeTohashPath path))
    , nodeZero := by simp [HPlayer]
    , nodeRoot := by simp [HPlayer]
                     rw [ ScanlGetN, eqLen]
                     unfold treeTohashPath
                     rw [ List.take_length]
                     -- exact @VinTree α ℍ aeq aeqLaw m op v bt path vInTree
                     exact VinTree v bt path vInTree
                     -- Proof Obligations
                     { simp }
    , allGames := by simp; intros mVal mLtn
                     exact midGameCorrect ℍ (m.mhash v) (List.map hashElem path) mVal (by rw [ List.length_map ]; assumption)
    }

end Build
----------------------------------------------------------------------

