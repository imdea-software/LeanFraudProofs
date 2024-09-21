import Lake
open Lake DSL

package "FraudProof" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
    , ⟨`autoImplicit , false ⟩ -- removed autoImplicit bullshit.
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «FraudProof» where
  -- add any library configuration options here
