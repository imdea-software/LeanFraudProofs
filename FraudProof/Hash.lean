import FraudProof.Value
-- Hash definitions?
abbrev Hash := String

-- Assuem there is a way to combine hashes
opaque Hash_Comb : Hash → Hash → Hash
infix:65 " ⊕ " => Hash_Comb -- left-assoc

opaque H : Value → Hash

-- We assume there are no collisions.
axiom hash_prop (v1 v2 : Value) : v1 ≠ v2 → H v1 ≠ H v2
-- axiom hash_assoc (h1 h2 h3 : Hash) : Hash_Comb h1 (Hash_Comb h2 h3) = Hash_Comb (Hash_Comb h1 h2) h3
