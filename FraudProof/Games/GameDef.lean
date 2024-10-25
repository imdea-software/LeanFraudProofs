import FraudProof.DataStructures.Hash
import FraudProof.Players

inductive Player : Type := | Proposer | Chooser
abbrev Winner := Player

def condWProp (b : Bool) := if b then Player.Proposer else Player.Chooser

abbrev ProposerMoves (ℍ : Type) := ℍ × ℍ

def ProposerMoves.left {ℍ : Type}(p : ProposerMoves ℍ)
  := p.1
def ProposerMoves.right {ℍ : Type}(p : ProposerMoves ℍ)
  := p.2

def hProposed {ℍ : Type}[m : HashMagma ℍ](p : ProposerMoves ℍ) : ℍ
   := m.comb p.1 p.2

inductive ChooserPrimMoves (α : Type) : Type
  | Now
  | Continue (opts : α)

abbrev ChooserSmp := ChooserPrimMoves Unit
abbrev ChooserMoves := ChooserPrimMoves Chooser.Side

-- inductive Winner : Type := | Proposer | Chooser
-- inductive Player : Type := | Proposer | Chooser


-- |Singlecutgame| describes a game cutting once at |cut| the game verifies that
-- there is a path of length |len| between |hb| and |ht|.
-- structure SingleCutGame (cut len : Nat)( hb ht : Hash ) where
--  -- this is the min trusted computation.
--  oneStep : Hash -> Hash -> Hash -> Prop
--  --
--  POne : Proposer.IPlayer cut len hb ht
--  PTwo : Chooser.IPlayer cut len hb ht
