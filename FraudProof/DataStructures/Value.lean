abbrev Value := String

-- opaque ValEq : Value -> Value -> Bool

-- axiom ValEqRfl ( v : Value ) : ValEq v v

-- instance : BEq Value where
--     beq := ValEq

-- -- Lawful
-- axiom ValBEqEq : forall { a b : Value }, (a == b) = true -> a = b

-- instance : LawfulBEq Value where
--   eq_of_beq := ValBEqEq
--   rfl := fun {a} => ValEqRfl a
