-- I don't want to define values.

opaque Value : Type
opaque ValEq : Value -> Value -> Bool
axiom ValEqRfl ( v : Value ) : ValEq v v
instance : BEq Value where
    beq := ValEq
