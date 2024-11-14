import FraudProof.DataStructures.Value

----------------------------------------
-- * Generic Hash Function (for us)
-- Hash from |v| to |h|
@[class] structure Hash (α ℍ : Type) where
  mhash : α -> ℍ
-- plus a comb function.
@[class] structure HashMagma (ℍ : Type) where
  comb : ℍ -> ℍ -> ℍ
----------------------------------------

----------------------------------------
-- * Hash Properties
--
-- ** Hash function collision resistant and Injective
@[class] structure CollResistant (α ℍ : Type)[op : Hash α ℍ] where
  -- Collision resistant? It should be hard to find these guys.
  noCollisions : forall (a b : α), a ≠ b -> op.mhash a ≠ op.mhash b

@[class] structure InjectiveHash (α ℍ : Type)[h : Hash α ℍ] where
  inject : forall (a b : α), h.mhash a = h.mhash b -> a = b

-- Injective is stronger than Collision resistant
def injIsCollResis {α ℍ : Type}[m : Hash α ℍ](inj : InjectiveHash α ℍ) : CollResistant α ℍ
  := { noCollisions := by intros a b neqab eqm; have inje := inj.inject _ _ eqm; contradiction}

-- ** Hash combination is collision resistant (both arguments) and Injective.
-- Lawful versions
@[class] structure SLawFulHash (ℍ : Type)[m : HashMagma ℍ] where
  -- Combine diff hashes are diff.
  neqLeft : forall (a1 a2 b1 b2 : ℍ), a1 ≠ a2 -> m.comb a1 b1 ≠ m.comb a2 b2
  neqRight : forall (a1 a2 b1 b2 : ℍ), b1 ≠ b2 -> m.comb a1 b1 ≠ m.comb a2 b2

@[class] structure InjectiveMagma (ℍ : Type)[m : HashMagma ℍ] where
  injectL : forall (a1 a2 b1 b2 : ℍ), m.comb a1 b1 = m.comb a2 b2 -> a1 = a2
  injectR : forall (a1 a2 b1 b2 : ℍ), m.comb a1 b1 = m.comb a2 b2 -> b1 = b2


-- Injective is stronger than Collision resistant
-- Constructive ok
def injIsLawful {ℍ : Type}{m : HashMagma ℍ}(inj : InjectiveMagma ℍ) : SLawFulHash ℍ
 := { neqLeft
    := by intros a1 a2 b1 b2 neq12 eq
          apply neq12
          have inj := inj.injectL _ _ _ _ eq
          assumption
    , neqRight
    := by intros a1 a2 b1 b2 neq12 eq
          apply neq12
          have inj := inj.injectR _ _ _ _ eq
          assumption
    }
-- Need some other stuff, dec over ℍ eq?
-- def lawfulIsInj {ℍ : Type}{m : HashMagma ℍ}(lful : SLawFulHash ℍ) : InjectiveMagma ℍ
--   :=
--   { injectL := _
--   , injectR := _
--   }
----------------------------------------


----------------------------------------
-- ** Hash and HashComb collision resistant?
@[class] structure HHCombCollResistant (α ℍ : Type)[h : Hash α ℍ][m : HashMagma ℍ] where
  noColl : forall (a : α)(b c : ℍ), h.mhash a ≠ m.comb b c

-- This is a bit weird.
-- Hash combination is define as the hash of the concat of hashes
-- m.comb a b = h.mhash (a ++ b)
----------------------------------------

----------------------------------------
----------------------------------------
-- Deprecated
--
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
