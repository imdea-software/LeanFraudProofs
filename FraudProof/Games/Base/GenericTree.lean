import FraudProof.DataStructures.BTree -- Btree

import FraudProof.DataStructures.SeqBTree -- Sequence -> BTree

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
def treeCompArbGame {α α' β β' γ : Type}
    -- Game Mechanics
    (leafCondition : α' -> α -> γ -> Winner)
    (midCondition  : β' -> β -> γ -> γ -> γ -> Winner)
    -- Public Information
    (da : CompTree α' β' γ)
    -- Players
    (reveler : ABTree (Option α) (Option (β × γ × γ)))
    (chooser : ABTree Unit ((γ × β × γ × γ) -> Option ChooserMoves))
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
          treeCompArbGame leafCondition midCondition ⟨ bl , proposition.2.1 ⟩ nextProposerLeft nextChooserLeft
        -- Chooser chooses to go right.
        | some (.Continue .Right) =>
          treeCompArbGame leafCondition midCondition ⟨ br , proposition.2.2 ⟩ nextProposerRight nextChooserRight
        -- No moves
        | none => Player.Proposer
      -- Chooser does not follows computation tree.
      | _ => Player.Proposer
    -- If reveler does not follow the compuetation tree, it loses.
    | _ , _ => Player.Chooser


-- * Game Mechanics
def homogeneous_tree_game {pinfo γ : Type}
    -- {α : Type}
    -- (leaf_condition : pinfo -> γ -> Winner)
    (midCondition  : pinfo -> γ -> γ -> γ -> Winner)
    -- Public Information
    (da : ABTree pinfo pinfo)
    -- Players
    (reveler : ABTree
               -- Leaves do not give information, it comes from the previous level.
               Unit -- γ (to be checked by leaf_condition)
               --
               (Option (γ × γ × γ)))
    (chooser : ABTree Unit ((pinfo × γ × γ × γ) -> Option ChooserMoves))
    --
    : Winner :=
    match da , reveler, chooser with
    | .node pub_now pub_l pub_r
      , .node (some ⟨ γ_root, γ_left, γ_right ⟩) re_left re_right
      , .node ch_fun  cho_left cho_right =>
      match ch_fun ⟨ pub_now , γ_root, γ_left, γ_right ⟩ with
      | some .Now =>
        midCondition pub_now  γ_root γ_left γ_right
      | some (.Continue .Left) =>
        homogeneous_tree_game midCondition pub_l re_left cho_left
      | some (.Continue .Right) =>
        homogeneous_tree_game midCondition pub_r re_right cho_right
      | none => Player.Proposer
    -- Bad Revealer player? -- Revelear plays first.
    | .node _ _ _ , .node none _ _, _ => Player.Chooser
    | .node _ _ _ , .leaf _ , _ => Player.Chooser
    -- Bad Chooser player?
    -- Revealear reveals something but chooser doesn't have any move.
    | .node _ _ _ , .node (some _) _ _ , .leaf _  => Player.Proposer
    -- Proposer made it to the end?
    | .leaf _ ,  _ , _ => Player.Proposer
----------------------------------------

----------------------------------------
-- * DA Path
-- Folding data into res
structure ImpTreePath (n : Nat)(α γ : Type) where
  data : α × ISkeleton n
  res : γ
  -- fold (leaf: α -> γ) (node: β -> γ -> γ -> γ) imp_tree = res
  -- DA : imp_tree ! data.2 = data.1

-- Explicit Tree, {leaf := .leaf, node := .node}
def ExpTree (n : Nat)(α α' β : Type)
 := ImpTreePath n α' (ABTree α β)

def pathToElem {α γ : Type}{n : Nat}
    -- Game Mechanics
    (leafCondition : ImpTreePath 0 α γ -> Winner)
    (nodeCondition : γ × γ × γ -> Winner)
    -- DA
    (da : ImpTreePath n α γ)
    -- Players
    (proposer : Sequence n (Option (PMoves γ)))
    (chooser : Sequence n (γ × γ × γ -> Option ChooserSmp))
    --
    : Winner
    := match n with
       | 0 => leafCondition da
       | .succ _pn =>
         match headSeq proposer with
         | .none => Player.Chooser -- Proposer forfeits the game
         | .some (.Next proposed) =>
           match headSeq chooser ⟨ da.res , proposed ⟩ with
           | .none => Player.Proposer -- Chooser forfeits the game
           | .some .Now => nodeCondition ⟨ da.res , proposed ⟩
           | .some (.Continue _) =>
             have nextRes := match headSeq da.data.2 with
                    | .inl _ => proposed.1
                    | .inr _ => proposed.2
             pathToElem leafCondition nodeCondition
               -- Next step DA
               ⟨ ⟨ da.data.1 , tailSeq da.data.2⟩ , nextRes ⟩
               -- Next step players
               (tailSeq proposer)
               (tailSeq chooser)


def optJoin {α : Type} : Option (Option α) -> Option α
 := fun x => match x with | none => none | some none => none | some (some j) => some j

-- This is exactly a DA. Skeleton DA.
-- When proving stuff, we went to play the same game forgetting that there is a
-- value, this game can be played just using hashes.
def skeleton_da_to_tree {lgn : Nat}{γ : Type}
    -- Path Skeleton
    (skeleton : ISkeleton (2^lgn.succ - 1))
    -- Res
    (res : γ)
    : (CompTree SkElem SkElem γ)
    := { data := perfectSeq skeleton , res := res }

-- Homogeneous game.
def perfect_seq_to_tree {γ : Type} {lgn : Nat}
    -- Is this just hash eq?
    (leafCondition : γ × γ -> Winner)
    -- Hash compose eq?
    (nodeCondition : γ × γ × γ -> Winner)
    -- DA
    (path : ISkeleton (2^lgn.succ - 1))
    -- Players
    (proposer : Sequence (2^lgn.succ - 1) (Option (γ × γ × γ)))
    (chooser : Sequence (2^lgn.succ - 1) (SkElem × γ × γ × γ -> Option ChooserSmp))
    --
    : Winner
    :=
    -- Build trees out of sequences.
    have tree_da := perfectSeq path
    have tree_proposer := perfectSeq proposer
    have tree_chooser := perfectSeq chooser
    --
    _

def btreePathToElem {α γ : Type} {n : Nat}
    -- Transformation reqs
    (leafInt : α -> γ)
    -- Game Mechanics
    (leafCondition : ImpTreePath 0 α γ -> Winner)
    (nodeCondition : γ × γ × γ -> Winner)
    -- DA
    (da : ImpTreePath n α γ)
    -- Players
    (proposer : Sequence n (Option (γ × γ × γ)))
    (chooser : Sequence n (γ × γ × γ -> Option ChooserSmp))
    --
    : Winner
    :=
    -- Transformations
    let tDA := seqHABTree da.data.2 -- Sequence n of sides
    let tP := ABTree.map optJoin id $ seqHABTree proposer
    let tC := ABTree.map
         (fun _ => some ()) (fun _ => sorry ) $ seqHABTree chooser
    -- The transformation |seqHABTree| enables some invalid game states!
    match n with
       | 0 => leafCondition da
       | .succ _pn =>
          let treeDA : CompTree (Option SkElem) SkElem γ
             := ⟨ tDA , da.res ⟩
          treeCompArbGame _ _ treeDA tP tC
