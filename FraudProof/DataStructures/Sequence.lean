import Mathlib.Data.Fin.Tuple.Basic -- Fin.tail

----------------------------------------
-- * Sequences

-- Sequence of |n| elements
abbrev Sequence (n : Nat) (α : Type) := Fin n -> α

-- Nil Sequence
def nilSeq {γ : Type} : Sequence 0 γ
 := fun x => by have e := x.isLt; simp at e

def singleSeq {α : Type} (a : α) : Sequence 1 α
 := Fin.cons a nilSeq

-- Head
@[simp]
def headSeq {α : Type}{ n : Nat } ( seq : Sequence n.succ α) : α
  := seq ⟨ 0 , by simp ⟩

-- Last
@[simp]
def lastSeq {α : Type}{n : Nat} (seq : Sequence n.succ α) : α
  := seq $ Fin.last n

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

-- Mapping
@[simp]
def seqMap {α β : Type} {n : Nat} (f : α -> β) ( seq : Sequence n α ) : Sequence n β
  := match n with
     | 0 => nilSeq
     | .succ _pn => Fin.cons (f $ headSeq seq) (seqMap f (Fin.tail seq))

@[simp]
def replicate {α : Type}{n : Nat}(c : α) : Sequence n α
 := fun _ => c


theorem Fin.snoc_head {α : Type}{ n : Nat }
   ( seq : Sequence n.succ α )(lt : α)
   : (@Fin.snoc n.succ (fun _ => α) seq lt) ⟨ 0 , by simp ⟩ = seq 0
   := by simp [snoc, castLT]

@[simp]
def takeN {α : Type}{n : Nat}(m : Nat)(mLTn : m < n)(s : Sequence n α) : Sequence m α
 := fun ⟨ p , plt ⟩ => s ⟨ p , by omega ⟩

@[simp]
def dropN {α : Type}{n : Nat}(m : Nat)(mLTn : m < n)(s : Sequence n α) : Sequence (n - m) α
 := fun ⟨ p , pLT ⟩ => s ⟨ p , by omega ⟩

----------------------------------------
