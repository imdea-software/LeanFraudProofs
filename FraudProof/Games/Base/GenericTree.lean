import FraudProof.DataStructures.BTree -- Btree

-- Generalize players too?
import FraudProof.Players.FromBToMTree -- Complex Strategies


----------------------------------------
-- * DA
-- Folding data into res
structure CompTree (α β γ : Type) where
  data : ABTree α β
  res : γ
  -- fold (leaf: α -> γ) (node: β -> γ -> γ -> γ) data = res

-- What is the game then? The revelear revels information at each point.
-- We have two difining conditions to decide when public information matches
-- private information.
-- + Leafs : α' -> α -> (history : γ) -> Winner.
-- Giving the public info, the revealed element and the resulting value, we can
-- decide who the winner is.
-- + Nodes : β' -> β -> γ -> γ -> (history : γ) -> Winner
-- Same as before, but at node level.
-- Public info, revealed info, 2 sub trees res, plus history.
--
-- We need history to know when someone is lying. Maybe there is a better way to
-- do it.
--
-- If we follow catamorphisms, is this the same as having a histomorphism?
--
----------------------------------------

----------------------------------------
-- * Winning Conditions
-- We have two winning conditions based on the two constructurs our type has.
-- + leafCondition : α' -> α -> γ -> Winner
-- + midCondition : β' -> β -> γ -> γ -> γ -> Winner
--
-- Both basically take all information at a giving point and return who the
-- winner is.
----------------------------------------

----------------------------------------
-- * Game Mechanics
def treeArbitrationGame {α α' β β' γ : Type}
    -- Game Mechanics
    (leafCondition : α' -> α -> γ -> Winner)
    (midCondition  : β' -> β -> γ -> γ -> γ -> Winner)
    -- Public Information
    (da : CompTree α' β' γ)
    -- Players
    (reveler : ABTree (Option α) (Option (β × γ × γ)))
    (chooser : ABTree (Option Unit) ((γ × β × γ × γ) -> Option ChooserMoves))
    --
    : Winner :=
    -- Reveler plays first
    match da.data, reveler with
    | .leaf h, .leaf (some a) => leafCondition h a da.res
    | .node ib bl br , .node (some proposition) nextProposerLeft nextProposerRight =>
      match chooser with
      | .node cfun nextChooserLeft nextChooserRight =>
        match cfun ⟨ da.res , proposition ⟩ with
        -- Chooser -> challenge hashes now.
        | some .Now =>
          midCondition ib proposition.1 da.res proposition.2.1 proposition.2.2
        -- Chooser chooses to go left.
        | some (.Continue .Left) =>
          treeArbitrationGame leafCondition midCondition ⟨ bl , proposition.2.1 ⟩ nextProposerLeft nextChooserLeft
        -- Chooser chooses to go right.
        | some (.Continue .Right) =>
          treeArbitrationGame leafCondition midCondition ⟨ br , proposition.2.2 ⟩ nextProposerRight nextChooserRight
        -- No moves
        | none => Player.Proposer
      -- Chooser does not follows computation tree.
      | _ => Player.Proposer
    -- If reveler does not follow the compuetation tree, it loses.
    | _ , _ => Player.Chooser
----------------------------------------
