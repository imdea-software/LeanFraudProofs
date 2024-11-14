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

@[simp]
def lastSeq {α : Type}{n : Nat} (seq : Sequence n.succ α) : α
  := seq $ Fin.last n

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

----------------------------------------
