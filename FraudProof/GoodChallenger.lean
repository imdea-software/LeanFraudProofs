import FraudProof.Value
import FraudProof.MTree
import FraudProof.Hash
import FraudProof.Challenger

import Init.Ext
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

@[simp]
def treeTohashPath : TreePath Value  → Path :=
  List.map hashElem

def sumP {α : Type}  : Sum α α → α := (Sum.elim id id)

-- PathComputation v p = List.drop 1 (ScanPath v p)
@[simp]
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


lemma LtToRev {n m : Nat} : m - n  < m + 1 := by apply Nat.lt_add_one_of_le; simp
lemma LtToRevSucc {n m : Nat}: m - ( n + 1 ) < m + 1 := by apply Nat.lt_add_one_of_le; simp

lemma mathE' : forall {a : Nat}, a - 0 < a + 1 := by simp

lemma mathE {n : Nat} { nNZ : 0 < n }: forall {a : Nat}, n < a -> a - n < a + 1 := by
  intros a pa
  trans a
  { simp
    exact And.intro ( by trans n; assumption; assumption ) ( by assumption )
  }
  simp

lemma Comp {n a : Nat} { hLt : n < a } : a - n < a + 1 := by
  cases n with
  | zero => simp
  | succ pn =>
    exact @mathE (pn.succ) (by simp) a hLt

-- lemma ScanL {α β : Type} :
--       forall
--       {l l': List β} { op :  α -> β -> α }
--       { v : α } { v' : β }
--       { eqLen : l.length = l'.length }
--       { n : Nat } {nLt : n < l'.length} ,
--       have lt : l'.length - n < l'.length + 1 := @Comp n l'.length nLt
--       (List.scanl op (op v v') l)[l'.length - n]'lt
--       =
--       op (( List.scanl op ( op v v' ) l)[l'.length - (n + 1)]'( by rw [ List.length_scanl ]; rw [ eqLen ] ; exact @Comp (n + 1) l'.length (by _ ) ))
--          (( v' :: l )[l'.length - n]'(by simp; rw [ eqLen ]; assumption ))



-- Since we play games in a range | 0 ... init.pL - 1|, we only need to
-- provide an strategy on such range.
-- This is equivalent to play finite games. Very finite, as soon as we start
-- the game, we have a cap to the number of moves.

-- def NodeHashPath (v : Value) ( path : TreePath Value) (n : Nat) { nLt : n < (path.length + 1) } : Hash :=
--   have nL : n < (ScanPath (H v) $ treeTohashPath path).length := by unfold ScanPath; rw [ List.length_scanl ]; simp; assumption
--   (ScanPath (H v) $ treeTohashPath path)[n]

def NodeHashPathF' { m : Nat }( hv : Hash ) ( path : Path ) { eqLen : m = (path.length + 1)} (n : Fin m) : Hash
:=  List.get (ScanPath hv path) ⟨ n.val, by unfold ScanPath; rw [ List.length_scanl, <- eqLen] ; simp ⟩  -- ( by unfold ScanPath; rw [ List.length_scanl, <- eqLen] ; simp )

@[simp]
def NodeHashPathF ( hv : Hash ) ( path : Path ) (n : Fin (path.length + 1)) : Hash
:= match n with
  | Fin.mk nval nproof =>
    (ScanPath hv path)[nval]'( by unfold ScanPath; rw [ List.length_scanl ]; assumption )

def NodeHashPath ( hv : Hash ) ( path : Path ) ( n : Nat ) ( nLt : n < (path.length + 1) ) : Hash :=
  have nL : n < (ScanPath hv path).length := by unfold ScanPath; rw [ List.length_scanl ]; assumption
  (ScanPath hv path)[n]

@[simp]
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

-- lemma FoldTake {α β ε: Type} {l : List β} { l' : List ε}{lenEq : l.length = l'.length}
--       {op : α -> β -> α} { v : α } { v' : β }
--    :
--       List.foldl op ( op v v' ) ( List.take (l'.length - n) l)
--       = List.foldl op v ( List.take (l'.length - n + 1) ( v' :: l ) ) := sorry
--
lemma lemmaTakeAppend { α : Type } ( ls : List α ) (m : Nat) mLt :
  (List.take m ls) ++ [ ls[m]'mLt ] = List.take m.succ ls
  := by {rw [ <- List.take_concat_get ]; simp; assumption}

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

-- lemma foldLast { α β : Type } { op : α -> β -> α }  { l : List β }:
--   forall { v : α } (last : β)(pred : List β) ( eq : l = pred ++ [last] ),
--   List.foldl op v (ls ++ rs)
--   = List.fold op (List.foldl op v ls) rs := by
--   induction l with
--   | nil => simp
--   | cons la ls HInd =>
--     intros v last pred Hyp
--     simp


@[simp]
lemma TakeLength { α : Type }{l : List α}:
  List.take l.length l = l := by
  cases l with
  | nil => simp
  | cons a as  => simp

lemma TakeEq { α : Type }{ l : List α } { n m : Nat }( eq : n = m ) :
  List.take n l = List.take m l := by rw [ eq ]

lemma SameGet { α : Type } { l : List α } :
  forall { n m : Nat } {eqNM : n = m} { nLt : n < l.length } { mLt : m < l.length} ,
  l.get ⟨ n , nLt ⟩ = l.get ⟨m , mLt ⟩  := by
  induction l with
  | nil =>
     intros; rw [ List.length ] at *; simp at *
  | cons w ws HInd =>
      intros n m eqNM nLt mLt
      cases n with
      | zero =>
        cases m with
        | zero => simp
        | succ _ => simp at eqNM
      | succ pn =>
        cases m with
        | zero => simp at eqNM
        | succ pm =>
          simp at nLt
          simp at mLt
          simp at eqNM
          simp
          apply @HInd pn pm eqNM nLt mLt

--   rw  [ @Fin.mk_eq_mk l.length n nLt m _ eqNM]
    -- l[n]'nLt = l[m]'( by rw [eqNM] at nLt; assumption ) := by
  -- rw [ List.get_eq_getElem  l _  ]
  -- rw [ List.get , Fin.val_eq_val _ _ eqNM ]
  --
  --
-- lemma getFromLast { α : Type }{ l : List α }:
--   forall { v : α }{ n : Nat }{ nLt : l.length - n < l.length + 1},
--   (v :: l).get ⟨ l.length - n  , nLt ⟩ =
--   l.get ⟨ l.length-n-1 , by _ ⟩ := by _
--   (v :: l)[l.length - n ] = l[l.length-n-1] := by
--   induction l with
--   | nil => simp
--   | cons w ws HInd =>
--          intros v n nLt
--          simp at nLt
--          simp
--          have rr : ws.length + 1 - n = (ws.length - n) + 1 := by ring_nf; rw [ Nat.add_sub_assoc ]; rw [ <- Nat.lt_add_one_iff ]; assumption
--          rw [ @SameGet α (v :: w :: ws) (ws.length + 1 - n) ( ws.length - n + 1 ) _ _ _]
--          rw [ <- List.getElem_cons_succ v (w :: ws) (ws.length - n) _ ]

lemma FoldRev { α β : Type }{l : List β}{op : α -> β -> α}:
  forall { v : α }( n : Nat) (nLt : n < l.length),
    List.foldl op v ( List.take (l.length - n) l)
    = op ( List.foldl op v (List.take (l.length - (n + 1)) l))
        ( l[l.length - (n + 1)] ) := by
    cases l with
    | nil => simp
    | cons p ps  =>
    intros v n nLt
    simp
    have eqN : ps.length + 1 - n = (ps.length - n) + 1 := by { ring_nf; exact Nat.add_sub_assoc ( by simp at nLt; rw [ Nat.lt_succ ] at nLt; assumption ) 1 }
    rw [ eqN ]
    simp
    rw [ <- List.foldl_concat op ]
    rw [ <- List.concat_nil, List.append_concat ]
    rw [ List.append_nil ]
    rw [ List.take_concat_get ]
    simp


lemma NotNilLast { α : Type }{ l : List α }{ notNil : 0 < l.length }:
  exists ls ll , l = ls ++ [ ll ] := by
  induction l with
  | nil => simp at notNil
  | cons a as HInd =>
    cases HC : as with
    | nil => existsi []; existsi a; simp
    | cons p ps =>
      rw [ HC ] at HInd
      have hIndps := @HInd ( by simp )
      match hIndps with
      | ⟨ ws , hws ⟩ =>
      match hws with
      | ⟨ w , hw ⟩ =>
      existsi (a :: ws)
      existsi w
      simp
      assumption

@[simp]
lemma TakeLength' { α β : Type }{l : List α} { l' : List β } :
  ( eqLen :  l.length = l'.length) ->
  List.take (List.length l) l' = l' := by
  intro eqLen
  rw [ eqLen ]
  apply TakeLength


@[simp]
lemma hachChainF0 hv ps : NodeHashPathF hv ps 0 = hv := by
  unfold NodeHashPathF
  unfold ScanPath
  simp

@[simp]
lemma hachChain0 hv ps pLt : NodeHashPath hv ps 0 pLt = hv := by
  unfold NodeHashPath
  simp
  -- unfold ScanPath
  -- simp

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
@[simp]
def RevStr {α : Type} { n : Nat  }( f : Fin n → α ) : Fin n → α :=
  fun a => match a with
  | Fin.mk val aLt => f ⟨ n - 1 - val , by exact Nat.sub_one_sub_lt aLt ⟩

-- def RevIff { α : Type} { n : Nat }( f g : Fin n → α ):
--   f = g ↔ RevStr f = RevStr g :=
--   Iff.intro
--   -- => )
--   (by intro fgEq; rw [ fgEq ])
--   ( by
--     intro revEq
--     funext x
--     match x with
--     | ⟨ xVal , xLt ⟩ =>
--     let rx := n - xVal - 1
--     have rxLt : rx < n := by { admit }
--     have rxLt' : n - 1 - rx < n := by { admit }
--     rw [ funext_iff ] at revEq
--     have fgrx := revEq ⟨ rx , rxLt ⟩
--     unfold RevStr at fgrx
--     simp at *
--     have eqX : n - 1 - rx = xVal := by {  admit }
--     have eqVals :⟨ n - 1 - rx , rxLt' ⟩ = Fin.mk xVal xLt  := by rw [Fin.ext_iff]; simp; assumption
--     rw [ <- eqVals ]
--     assumption
--   )

@[simp]
def Drop0 { α : Type } {n : Nat} ( f : Fin (n + 1) → α ) : Fin n → α :=
  fun an => match an with
  | Fin.mk nVal nLt => f ⟨ nVal + 1, by simp ; assumption⟩

@[simp]
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
    simp
    -- unfold treeTohashPath
    -- unfold SibsF'
    -- unfold NodeHashPathF
    -- unfold ScanPath
    -- simp

  -- Mid-games are interesting.
  -- Node [ n ] = opHash Node[n+1] Sib[n]
  lemma goodMidGame :
    let path := p :: path'
    let GP := CGoodPlayer v path
    forall (n : Nat) ( lt : n < path.length - 1),
    -- let fint : Fin n := ⟨ n , by trans path.length - 1; assumption; rw [ List.length ]; simp⟩
    GP.hashStr.node ⟨ n , by trans path.length - 1; assumption; rw [ List.length ]; simp⟩
    = opHash ( GP.hashStr.node ⟨ n + 1 , by rw [ List.length ] at *; simp at *; assumption ⟩ )
            (GP.hashStr.sibling ⟨ n , by trans path.length - 1; assumption; rw [ List.length ]; simp⟩ )
    := by {
      simp
      intros n nLt
      rw [ ScanlGetN ]
      rw [ ScanlGetN ]
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

      { simp ; exact LtToRevSucc }
      { simp ; exact LtToRev }
     }
end GoodPlayerProp
