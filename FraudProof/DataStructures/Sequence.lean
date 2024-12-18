import Mathlib.Data.Fin.Tuple.Basic -- Fin.tail

----------------------------------------
-- * Sequences

-- Sequence of |n| elements
abbrev Sequence (n : Nat) (α : Type) := Fin n -> α

@[simp]
def polyLenSeqEq {α : Type}[BEq α]{n m : Nat}(p : Sequence n α)(q : Sequence m α) : Bool
  := match n , m with
     | .zero , .zero => true
     | .succ _pn, .succ _mn =>
       if p 0 == q 0
       then polyLenSeqEq (Fin.tail p) (Fin.tail q)
       else false
     | _ , _ => false

theorem seqEqLawLength {α : Type}[BEq α]{m n : Nat}(p : Sequence n α)(q : Sequence m α)(pEq : polyLenSeqEq p q)
  : n = m
  := by revert p q pEq n
        induction m with
        | zero =>
          intros n p q pEQq
          -- unfold polyLenSeqEq at pEQq
          cases n with
          | zero => rfl
          | succ pn => simp at pEQq
        | succ pm HInd =>
          intros n p q pEQq
          cases n with
          | zero => simp at pEQq
          | succ pn =>
            simp at pEQq
            simp
            have rsEq := pEQq.2
            exact @HInd pn (Fin.tail p) (Fin.tail q) rsEq

theorem seqEqLawRfl {α : Type}[BEq α][LawfulBEq α]{n : Nat}(p : Sequence n α)
  : polyLenSeqEq p p
  := by
   revert p
   induction n with
   | zero => intro _p; simp
   | succ pn HInd =>
      intro p
      simp
      apply HInd

theorem seqEqForAll  {α : Type}[BEq α][LawfulBEq α]{n m : Nat}(p : Sequence n α)(q : Sequence m α)
  : polyLenSeqEq p q -> forall (i : Nat)(ltN : i < n)(ltM : i < m), p ⟨ i , ltN⟩ = q ⟨ i , ltM ⟩
  := sorry

theorem seqEqLawDec {α : Type}[BEq α][LawfulBEq α]{n m : Nat}(p : Sequence n α)(q : Sequence m α)
   : polyLenSeqEq p q == true -> HEq p q
   := by revert p q m
         induction n with
         | zero =>
           intros m p q eq
           cases m with
           | zero => simp; apply funext; intro x; have l0 := x.2; simp at l0
           | succ pm => simp at eq
         | succ pn HInd =>
           intros m p q eq
           cases m with
           | zero => simp at eq
           | succ pm =>
             simp at eq
             have ind := @HInd pm (Fin.tail p) (Fin.tail q)
             simp at ind
             sorry

-- Nil Sequence
def nilSeq {γ : Type} : Sequence 0 γ
 := fun x => by have e := x.isLt; simp at e

def singleSeq {α : Type} (a : α) : Sequence 1 α
 := Fin.cons a nilSeq

-- Head
@[simp]
def headSeq {α : Type}{ n : Nat } ( seq : Sequence n.succ α) : α
  := seq ⟨ 0 , by simp ⟩

@[simp]
def headSeq' {α : Type}{ n : Nat } ( seq : Sequence n α)(notZ : 0 < n) : α
 := seq ⟨ 0 , notZ ⟩

-- Last
@[simp]
def lastSeq {α : Type}{n : Nat} (seq : Sequence n.succ α) : α
  := seq $ Fin.last n
@[simp]
def lastSeq' {α : Type}{n m : Nat} (seq : Sequence n α)(ns : n = m + 1) : α
  := seq ⟨ m , by omega ⟩

@[simp]
def snocSeq {α : Type}{n : Nat}(a : α)(seq : Sequence n α) : Sequence n.succ α
  := fun ⟨ x , _xLT ⟩ => if H : x < n then seq ⟨ x , H ⟩ else a

@[simp]
def eqLength {α : Type}{n m : Nat}(seq : Sequence n α)(eqP : n = m) : Sequence m α
 := fun ⟨ x , xLT ⟩ => seq ⟨ x , by omega ⟩

-- R Access
@[simp]
def getI {α : Type}{n: Nat}(seq : Sequence n α)(i : Nat)(iLTn : i < n) : α
 := seq ⟨ i , iLTn ⟩

@[simp]
def tailSeq {α : Type}{n : Nat}: Sequence n.succ α -> Sequence n α
  := Fin.tail

@[simp]
def desc_Seq {n : Nat}{α : Type} (seq : Sequence n.succ α) : α × Sequence n α
 := ⟨ headSeq seq , tailSeq seq ⟩

-- Map
@[simp]
def seqMap {α β : Type} {n : Nat} (f : α -> β) ( seq : Sequence n α ) : Sequence n β
  := match n with
     | 0 => nilSeq
     | .succ _pn => Fin.cons (f $ headSeq seq) (seqMap f (Fin.tail seq))

-- Replicate
@[simp]
def replicate {α : Type}{n : Nat}(c : α) : Sequence n α
 := fun _ => c

theorem Fin.snoc_head {α : Type}{ n : Nat }
   ( seq : Sequence n.succ α )(lt : α)
   : (@Fin.snoc n.succ (fun _ => α) seq lt) ⟨ 0 , by simp ⟩ = seq 0
   := by simp [snoc, castLT]

-- Take
@[simp]
def takeN {α : Type}{n : Nat}(m : Nat)(mLTn : m ≤ n)(s : Sequence n α) : Sequence m α
 := fun ⟨ p , plt ⟩ => s ⟨ p , by omega ⟩

-- Drop
@[simp]
def dropN {α : Type}{n : Nat}(m : Nat)(mLTn : m ≤ n)(s : Sequence n α) : Sequence (n - m) α
 := fun ⟨ p , pLT ⟩ => s ⟨ m + p , by omega ⟩

-- Concat
@[simp]
def concatSeq {α : Type}{n m : Nat}(p : Sequence n α)(q : Sequence m α) : Sequence (n + m) α
 := fun ⟨ x , xLT ⟩ =>
    if H : x < n then p ⟨ x , H ⟩
    else q ⟨ x - n , by omega ⟩

-- SplitAt
def splitSeq {α : Type}{n : Nat}(p : Sequence n α)(m : Nat)(mLTn : m ≤ n): Sequence m α × Sequence (n - m) α
  := ⟨ takeN m mLTn p , dropN m mLTn p ⟩

----------------------------------------

def sequence_coerce {α : Type} {n m : Nat}( hEq : n = m )(s : Sequence n α) : Sequence m α
  := fun ix => match ix with
               | ⟨ i , iLt ⟩ => s ⟨ i , by omega ⟩

instance beq_sequences {α : Type}[BEq α]{n : Nat} : BEq (Sequence n α) where
  beq sl sr :=
    match n with
   | .zero => true
   | .succ _pn => headSeq sl == headSeq sr
                  && beq_sequences.beq (Fin.tail sl) (Fin.tail sr)

-- theorem beq_sequence_head {α : Type}[BEq α]{n : Nat}(l r : Sequence n.succ α)(heq : l == r)
--         : l ⟨ 0 , by simp ⟩ == r ⟨ 0 , by simp ⟩
--         := by simp;

-- theorem beq_sequence_ {α : Type}[BEq α]{n : Nat}(l r : Sequence n α)(heq : l == r)
--         : forall (i : Nat), (iLt : i < n) -> l ⟨ i, iLt ⟩ == r ⟨ i , iLt ⟩
--         := by
--         intros i iLt
--         apply funext at heq

-- instance law_full_beq_seq {α : Type}[BEq α][LawfulBEq α]{n : Nat} : LawfulBEq (Sequence n α) where
--   eq_of_beq := by
--     intros a b heq
--     apply funext
--     intro x; replace ⟨ x , xLT ⟩ := x
--     induction x with
--     | zero => _
--     | succ px HPx => _
--   rfl := _

-- structure EqSeq (α : Type)(m n : Nat)(sl : Sequence m α)(sr : Sequence n α) where
--   sameLen : m = n
--   sameVals : sequence_coerce sameLen sl = sr

--
theorem split_seq_eq {α : Type}{n m : Nat}{ mLTn : m ≤ n }( seq : Sequence n α ):
  have ⟨ seql , seqr ⟩ := splitSeq seq m mLTn
  seq = sequence_coerce (by omega) (concatSeq seql seqr)
  -- seq = sequence_coerce (by omega) (concatSeq seql seqr)
  := by
  simp
  apply funext
  rw [ Fin.forall_iff ]
  intros i iLT
  simp [sequence_coerce]
  split
  case h.isTrue h => simp [splitSeq]
  case h.isFalse h =>
    simp [splitSeq]
    congr
    omega

theorem ConsTailSeqCoerce { α : Type }{n m : Nat} { ceq : n = m + 1 }(seq : Sequence n α)
  : Fin.cons ( seq ⟨ 0 , by omega ⟩ ) ( Fin.tail (sequence_coerce ceq seq )) = sequence_coerce ceq seq
  := by
  apply funext
  rw [ Fin.forall_iff ]
  intros i iLT
  repeat simp [sequence_coerce]
  match i with
  | .zero => simp
  | .succ pi => simp [Fin.cons, Fin.tail, sequence_coerce]

theorem ExtraCoerce {α : Type}{n : Nat}(req : n = n)(seq : Sequence n α)
        : seq = sequence_coerce req seq
        := by
        apply funext; rw [ Fin.forall_iff ]
        intros i iLT
        simp [sequence_coerce]

theorem ConcatSplitCoerce { α : Type } {n cut m : Nat}{cutLn : cut ≤ n}(ceq : n - cut = m) (seq : Sequence n α):
  have ⟨ fst, snd ⟩ := (splitSeq seq cut cutLn)
  concatSeq fst ( sequence_coerce ceq snd )
  = sequence_coerce (by omega) seq
  := by simp [splitSeq, concatSeq]
        apply funext
        rw [Fin.forall_iff]
        intros i iLT
        simp [sequence_coerce]
        split
        case h.isTrue h => simp
        case h.isFalse h => congr; omega
