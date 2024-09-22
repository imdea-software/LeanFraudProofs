import FraudProof.DataStructures.Value

-- Hash definitions?
abbrev Hash := String

-- Assume there is a way to combine hashes
opaque Hash_Comb : Hash → Hash → Hash
infix:65 " ⊕ " => Hash_Comb -- left-assoc

opaque H : Value → Hash

-- We assume there are no collisions.
axiom hash_prop (v1 v2 : Value) : v1 ≠ v2 → H v1 ≠ H v2
