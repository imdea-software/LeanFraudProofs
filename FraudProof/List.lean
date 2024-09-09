import Mathlib.Data.Fin.Basic -- Fin trans
import Mathlib.Data.List.Basic
import Batteries.Data.List.Basic -- foldl
import Mathlib.Tactic.Ring -- (ring, ring-rf)

-- Length / Fin
def finLenEq { α β : Type }
  {ls : List α} { rs : List β } (eqLen : ls.length = rs.length)
  ( n : Fin ls.length ) : Fin rs.length
  := { val := n.val, isLt := by rw [ <- eqLen ]; simp }

-- @[simp]
theorem lenEqMapRev { α β : Type }
  ( l : List α ) ( f : α → β )
  : (List.reverse ( List.map f l )).length = l.length
  := by
  trans (List.map f l).length
  { exact List.length_reverse _}
  { exact List.length_map _ _ }


lemma ScanlGet0 { α β : Type } ( op : α -> β -> α) ( b : α ) ( l : List β ):
  List.get (List.scanl op b l) ⟨ 0 , by rw [ List.length_scanl ]; simp ⟩ = b := by
  simp

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
