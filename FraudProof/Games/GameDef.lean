import FraudProof.DataStructures.Hash
import FraudProof.Players

inductive Player : Type := | Proposer | Chooser
abbrev Winner := Player

def condWProp (b : Bool) := if b then Player.Proposer else Player.Chooser

inductive PMoves' (α β : Type)
 | End (v : α)
 | Next (p : β)

abbrev PMoves (ℍ : Type) := PMoves' Empty (ℍ × ℍ)

def PMoves'.map {α β γ σ : Type}
  (f : α -> β)(g : γ -> σ)
  : PMoves' α γ -> PMoves' β σ
  | .End a => .End $ f a
  | .Next p => .Next $ g p

def PMoves.left {ℍ : Type} : PMoves ℍ -> ℍ
 | .Next e => e.1
def PMoves.right {ℍ : Type} : PMoves ℍ -> ℍ
 | .Next e => e.2

def hProposed {ℍ : Type}[o : HashMagma ℍ]
    (p : PMoves ℍ) : ℍ
    := match p with
       | .Next e => o.comb e.1 e.2

inductive ChooserPrimMoves (α : Type) : Type
  | Now
  | Continue (opts : α)

abbrev ChooserSmp := ChooserPrimMoves Unit
abbrev ChooserMoves := ChooserPrimMoves Chooser.Side


-- def GenGame {pos pMs cMs : Type}
--   (p1 : pos -> Option pMs)
--   (p2 : pos -> pMs -> Option cMs)
--   (joinP : pos -> pMs -> cMs -> pos) <-- this should give a wellfounded rel!
--   (p : pos)
--   : Winner
--   := match p1 p with
--      | none => Player.Chooser
--      | some pM =>
--        match p2 p pM with
--         | none => Player.Proposer
--         | some cM => GenGame p1 p2 joinP $ joinP p pM cM
--   termination_by wr
  -- decreasing_by simp_wf
