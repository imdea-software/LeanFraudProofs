import Mathlib.Tactic.Ring -- (ring, ring-rf)

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

lemma succInj ( m n : Nat) : m + 1 < n + 1 -> m < n := by
  cases m with
  | zero => simp
  | succ pm => simp
