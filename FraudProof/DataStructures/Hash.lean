import FraudProof.DataStructures.Value

----------------------------------------
-- * Generic Hash Function (for us)
-- Hash from |v| to |h|
-- plus a comb function.
@[class] structure Hash (α ℍ : Type) where
  mhash : α -> ℍ
@[class] structure HashMagma (ℍ : Type) where
  comb : ℍ -> ℍ -> ℍ

-- def impComp {α β : Type}{hStr : SHashDefOp α β} : β -> β -> β := hStr.comb
-- infix:65 " ⊕ " => impComp -- left-assoc

@[class] structure CollResistant (α ℍ : Type)[op : Hash α ℍ] where
  -- Collision resistant? It should be hard to find these guys.
  noCollisions : forall (a b : α), a ≠ b -> op.mhash a ≠ op.mhash b

-- Lawful versions
@[class] structure SLawFulHash (ℍ : Type)[m : HashMagma ℍ] where
  -- Combine diff hashes are diff.
  neqLeft : forall (a1 a2 b1 b2 : ℍ), a1 ≠ a2 -> m.comb a1 b1 ≠ m.comb a2 b2
  neqRight : forall (a1 a2 b1 b2 : ℍ), b1 ≠ b2 -> m.comb a1 b1 ≠ m.comb a2 b2

----------------------------------------

----------------------------------------
-- * Original Hash Definitions
-- We proved almost everything assuming opaque types and stuff.
namespace StringHash

  open ValueString

  abbrev Hash := String

  -- Assume there is a way to combine hashes
  opaque Hash_Comb : Hash → Hash → Hash
  -- infix:65 " ⊕ " => Hash_Comb -- left-assoc

  opaque H : Value → Hash

  -- We assume there are no collisions.
  axiom hash_prop (v1 v2 : Value) : v1 ≠ v2 → H v1 ≠ H v2

  axiom hop_neq_left {al ar bl br : Hash}
    : ¬ al = bl -> ¬ Hash_Comb al ar = Hash_Comb bl br

  axiom hop_neq_right {al ar bl br : Hash}
    : ¬ (ar = br) -> ¬ (Hash_Comb al ar = Hash_Comb bl br)

end StringHash

----------------------------------------
-- * Old definitions as news
--

namespace HashString
  abbrev StrHash (α : Type) := Hash α String
  -- abbrev LawFulStrHash (α : Type)(m : HashMagma String) := @SLawFulHash String m String

  open ValueString
  abbrev PlainHash := Hash String String
  -- abbrev LawFulPlain (m : HashMagma ℍ):= @SLawFulHash String m String
  -- #check LawFulPlain

end HashString

----------------------------------------
-- Useful names
----------------------------------------
