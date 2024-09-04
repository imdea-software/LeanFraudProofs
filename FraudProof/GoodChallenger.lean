import FraudProof.Value
import FraudProof.MTree
import FraudProof.Hash
import FraudProof.Challenger

import Init.Data.List.Basic
import Init.Data.Fin.Lemmas

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Sum.Basic
import Batteries.Data.List.Basic -- foldl

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring

import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Basic
import Mathlib.Order.SuccPred.Basic
-- * A GoodChallenger
--

-- Good Prop
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

def hashElem : BTree Value ⊕ BTree Value  → PathElem :=
  let hashTree := ( MTree.hash ∘ hash_BTree )
  Sum.map  hashTree hashTree

def treeTohashPath : TreePath Value  → Path :=
  List.map hashElem

def sumP {α : Type}  : Sum α α → α := (Sum.elim id id)

-- PathComputation v p = List.drop 1 (ScanPath v p)
def ScanPath ( v : Hash ) ( path : Path ) : List Hash
:= List.scanl opHash v path

@[simp]
lemma lenEqMapRev { α β : Type }
  ( l : List α ) ( f : α → β )
  : (List.reverse ( List.map f l )).length = l.length
  := by
  trans (List.map f l).length
  { exact List.length_reverse _}
  { exact List.length_map _ _ }

@[simp]
lemma TreeLenEq
  : (treeTohashPath path).length = path.length
  := by exact List.length_map _ _

lemma RevTreeLenEq ( path : TreePath Value )
  : (treeTohashPath path).reverse.length = path.length
  := by simp

def finLenEq { α β : Type }
  {ls : List α} { rs : List β } (eqLen : ls.length = rs.length)
  ( n : Fin ls.length ) : Fin rs.length
  := { val := n.val, isLt := by rw [ <- eqLen ]; simp }


-- Since we play games in a range | 0 ... init.pL - 1|, we only need to
-- provide an strategy on such range.
-- This is equivalent to play finite games. Very finite, as soon as we start
-- the game, we have a cap to the number of moves.

-- def NodeHashPath (v : Value) ( path : TreePath Value) (n : Nat) { nLt : n < (path.length + 1) } : Hash :=
--   have nL : n < (ScanPath (H v) $ treeTohashPath path).length := by unfold ScanPath; rw [ List.length_scanl ]; simp; assumption
--   (ScanPath (H v) $ treeTohashPath path)[n]

def NodeHashPathF' { m : Nat }( hv : Hash ) ( path : Path ) { eqLen : m = (path.length + 1)} (n : Fin m) : Hash
:=  List.get (ScanPath hv path) ⟨ n.val, by unfold ScanPath; rw [ List.length_scanl, <- eqLen] ; simp ⟩  -- ( by unfold ScanPath; rw [ List.length_scanl, <- eqLen] ; simp )
def NodeHashPathF ( hv : Hash ) ( path : Path ) (n : Fin (path.length + 1)) : Hash
:= (ScanPath hv path)[n]'( by unfold ScanPath; rw [ List.length_scanl ]; simp )

def NodeHashPath ( hv : Hash ) ( path : Path ) ( n : Nat ) ( nLt : n < (path.length + 1) ) : Hash :=
  have nL : n < (ScanPath hv path).length := by unfold ScanPath; rw [ List.length_scanl ]; assumption
  (ScanPath hv path)[n]

def SibsF' { m : Nat} (path : Path) {eqLen : m = path.length} (n : Fin m) : PathElem
  := match n with
  | Fin.mk nVal nLt => List.get path ⟨ nVal , by rw [ <- eqLen ]; exact nLt ⟩
def Sibs ( path : Path ) ( n : Nat ) ( nLpath : n < path.length ) : PathElem :=
   path[n]

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

lemma ScanlGet0 { α β : Type } ( op : α -> β -> α) ( b : α ) ( l : List β ):
  List.get (List.scanl op b l) ⟨ 0 , by rw [ List.length_scanl ]; simp ⟩ = b := by
  simp

lemma succInj ( m n : Nat) : m + 1 < n + 1 -> m < n := by
  cases m with
  | zero => simp
  | succ pm => simp

lemma ScanlGetN  { α β : Type } { op : α -> β -> α} { l : List β }:
  forall { n : Nat } {nLt : n < l.length + 1} { b : α } ,
  have isLt : n < ((List.scanl op b l)).length := by rw [ List.length_scanl ]; assumption
  ((List.scanl op b l))[n] = List.foldl op b ( List.take n l ) :=
  by
   simp
   induction l with
   | nil => simp
   | cons l ls HInd =>
     intros n nLt a
     cases n with
    | zero => simp
    | succ pd => simp
                 exact @HInd pd ( by simp at nLt; assumption ) (op a l)

@[simp]
lemma hachChainF0 hv ps : NodeHashPathF hv ps 0 = hv := by
  unfold NodeHashPathF
  unfold ScanPath
  simp

@[simp]
lemma hachChain0 hv ps pLt : NodeHashPath hv ps 0 pLt = hv := by
  unfold NodeHashPath
  simp
  unfold ScanPath
  simp

-- lemma hashChainF' ps :
--   ( n : Nat ) -> ( nLt : n < ps.length) ->
--   ( hv : Hash ) ->
--   NodeHashPath hv ps (n + 1) _
--   = opHash ( NodeHashPath hv ps n _ ) (Sibs ps n nLt) := sorry



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
    unfold SibsF'
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
  -- repeat {}
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


-- Fin n -> α are arrays of length n
-- The following function reverses it.
def RevStr {α : Type} { n : Nat  }( f : Fin n → α ) : Fin n → α :=
  fun a => match a with
  | Fin.mk val aLt => f ⟨ n - 1 - val , by exact Nat.sub_one_sub_lt aLt ⟩

def Drop0 { α : Type } {n : Nat} ( f : Fin (n + 1) → α ) : Fin n → α :=
  fun an => match an with
  | Fin.mk nVal nLt => f ⟨ nVal + 1, by simp ; assumption⟩

#check NodeHashPath

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

lemma GPlEmpty : (CGoodPlayer v []).hashStr.sibling n = nE
  := by
  unfold CGoodPlayer
  simp
  cases n
  contradiction

-- Node [ last  ] = opHash (H v) (Sibling last)
lemma goodStrBottomGame ( v : Value ) (p : TreePathElem Value) ( path : TreePath Value ) :
  let path' := p :: path -- not empty path
  let GPlayer := CGoodPlayer v path'
  let pLast : Fin path'.length := ⟨ path'.length - 1 , by rw [ List.length ]; simp ⟩
  GPlayer.hashStr.node  pLast = opHash ( H v ) (GPlayer.hashStr.sibling  pLast)
  := by
  unfold CGoodPlayer
  unfold RevStr
  unfold Drop0
  simp
  unfold treeTohashPath
  simp
  unfold SibsF'
  unfold NodeHashPathF
  unfold ScanPath
  simp

