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
   := sorry

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
 := fun ⟨ p , pLT ⟩ => s ⟨ p , by omega ⟩

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
