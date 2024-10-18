import FraudProof.DataStructures.Value

-- Hash definitions?
abbrev Hash := String

@[class] structure SHashDefOp (v h : Type) where
  hash : v -> h
  comb : h -> h -> h

@[class] structure SLawFulHash (v h : Type) where
  hops : SHashDefOp v h
  -- No collisitions?
  noCollisions : forall (a b : v), a ≠ b -> hops.hash a ≠ hops.hash b
  -- NeqLeft
  neqLeft : forall (a1 a2 b : h), a1 ≠ a2 -> hops.comb a1 b ≠ hops.comb a2 b
  neqRight : forall (a b1 b2 : h), b1 ≠ b2 -> hops.comb a b1 ≠ hops.comb a b2


-- Assume there is a way to combine hashes
opaque Hash_Comb : Hash → Hash → Hash
infix:65 " ⊕ " => Hash_Comb -- left-assoc

opaque H : Value → Hash

-- We assume there are no collisions.
axiom hash_prop (v1 v2 : Value) : v1 ≠ v2 → H v1 ≠ H v2

axiom hop_neq_left {al ar bl br : Hash}
  : ¬ al = bl -> ¬ Hash_Comb al ar = bl ⊕ br

axiom hop_neq_right {al ar bl br : Hash}
  : ¬ (ar = br) -> ¬ (Hash_Comb al ar = Hash_Comb bl br)

-- These two are nonsense!
-- axiom hop_neq_lr {al ar bl br : Hash}
--   : ¬ (al = br) -> ¬ (Hash_Comb al ar = Hash_Comb bl br)

-- axiom hop_neq_rl {al ar bl br : Hash}
--   : ¬ (ar = bl) -> ¬ (Hash_Comb al ar = Hash_Comb bl br)
