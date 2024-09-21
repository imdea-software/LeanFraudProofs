theorem finEq {α : Type} {m n g: Nat} (eqmn :  m = n )(mLt : m < g)
      (f : Fin g -> α):  f ⟨ m , mLt ⟩ = f ⟨ n , by omega ⟩
      := by congr
