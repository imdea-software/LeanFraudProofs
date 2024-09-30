import FraudProof.DataStructures.Value

-- Hash definitions?
abbrev Hash := String

-- Assume there is a way to combine hashes
opaque Hash_Comb : Hash → Hash → Hash
infix:65 " ⊕ " => Hash_Comb -- left-assoc

opaque H : Value → Hash

-- We assume there are no collisions.
axiom hash_prop (v1 v2 : Value) : v1 ≠ v2 → H v1 ≠ H v2

axiom hop_neq_left {al ar bl br : Hash}
  : ¬ al = bl -> ¬ Hash_Comb al ar = bl ⊕ br

axiom hop_neq_rigth {al ar bl br : Hash}
  : ¬ (ar = br) -> ¬ (Hash_Comb al ar = Hash_Comb bl br)

axiom hop_neq_lr {al ar bl br : Hash}
  : ¬ (al = br) -> ¬ (Hash_Comb al ar = Hash_Comb bl br)

axiom hop_neq_rl {al ar bl br : Hash}
  : ¬ (ar = bl) -> ¬ (Hash_Comb al ar = Hash_Comb bl br)
