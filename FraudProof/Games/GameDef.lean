inductive Player : Type where
  | Proposer
  | Chooser

abbrev Winner := Player

@[simp]
def winning_proposer (b : Bool) : Winner := if b then .Proposer else .Chooser
@[simp]
def winning_chooser (b : Bool) : Winner := if b then .Chooser else .Proposer

inductive Side : Type where
    | Left
    | Right

abbrev PMoves (ℍ : Type) := ℍ × ℍ

-- Idioms
@[simp]
def PMoves.left {ℍ : Type} : PMoves ℍ -> ℍ
  := fun e => e.1
@[simp]
def PMoves.right {ℍ : Type} : PMoves ℍ -> ℍ
  := fun e => e.2

inductive ChooserPrimMoves (α : Type) : Type
  | Now
  | Continue (opts : α)

abbrev ChooserSmp := ChooserPrimMoves Unit
abbrev ChooserMoves := ChooserPrimMoves Side

-- def condWProp (b : Bool) := if b then Player.Proposer else Player.Chooser

-- inductive PMoves' (α β : Type)
--  | End (v : α)
--  | Next (p : β)


-- @[simp]
-- def PMoves.destruct {α : Type} : PMoves α -> α × α
--   | .Next p => p

-- def PMoves'.map {α β γ σ : Type}
--   (f : α -> β)(g : γ -> σ)
--   : PMoves' α γ -> PMoves' β σ
--   | .End a => .End $ f a
--   | .Next p => .Next $ g p

