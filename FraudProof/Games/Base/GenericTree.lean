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

def simp_tree {α α' β β' γ : Type}
    -- Game Mechanics
    -- Next goals function: how from current goal and information provided the
    -- reveler, generates next goals. Do we need to take β' (arena info) into
    -- account?
    (splitter : γ -> β -> γ × γ)
    -- Conditions
    (leafCondition : α' -> α -> γ -> Winner)
    (midCondition  : β' -> β -> γ -> Winner)
    -- Public Information
    (da : CompTree α' β' γ)
    -- Da is a game arena (ABTree α' β') and some result of type γ
    -- Players
    (reveler : ABTree (Option α) (Option β))
    (chooser : ABTree Unit (γ -> β -> Option ChooserMoves))
    : Winner
 := match da.data, reveler with
    | .leaf h, .leaf (some a) => leafCondition h a da.res
    | .node ib bl br , .node (some proposition) nextProposerLeft nextProposerRight =>
      match chooser with
      | .node cfun nextChooserLeft nextChooserRight =>
        match cfun da.res proposition with
        -- Chooser -> challenge hashes now.
        | some .Now =>
          midCondition ib proposition da.res
        -- Chooser chooses to go left.
        | some (.Continue .Left) =>
          simp_tree splitter leafCondition midCondition
          -- next da
          ⟨ bl , (splitter da.res proposition).1 ⟩
          --
          nextProposerLeft nextChooserLeft
        -- Chooser chooses to go right.
        | some (.Continue .Right) =>
          simp_tree splitter leafCondition midCondition
          -- next da
            ⟨ br , (splitter da.res proposition).2 ⟩
          --
            nextProposerRight nextChooserRight
        -- No moves
        | none => Player.Proposer
      -- Chooser does not follows computation tree.
      | _ => Player.Proposer
    -- If reveler does not follow the compuetation tree, it loses.
    | _ , _ => Player.Chooser

-- Reveler winning_condition is just always winning if challenged
def reveler_winning_condition_simp_game {α α' β β' γ : Type}
    (splitter : γ -> β -> γ × γ)
    -- Game Mechanics
    (leafCondition : α' -> α -> γ -> Winner)
    (midCondition  : β' -> β -> γ -> Winner)
    -- Public Information
    (da : CompTree α' β' γ)
    -- Players
    (reveler : ABTree (Option α) (Option β))
  : Prop :=
  match da.data , reveler with
  | .node b bl br , .node (.some proposed) left_reveler right_reveler =>
    -- If challenged, proposer wins
    midCondition b proposed da.res = Player.Proposer
    -- Same for each branch
    ∧ reveler_winning_condition_simp_game splitter
       leafCondition midCondition
       {data := bl, res:= (splitter da.res proposed).1}
       left_reveler
    ∧ reveler_winning_condition_simp_game splitter
       leafCondition midCondition
       {data := br, res:= (splitter da.res proposed).2}
       right_reveler
   | .leaf a, .leaf (.some a') =>
     leafCondition a a' da.res = Player.Proposer
   | _ , _ => False

theorem simp_game_reveler_wins {α α' β β' γ : Type}
    (splitter : γ -> β -> γ × γ)
    (leafCondition : α' -> α -> γ -> Winner)
    (midCondition  : β' -> β -> γ -> Winner)
    (da : CompTree α' β' γ)
    (reveler : ABTree (Option α) (Option β))
    (wProp : reveler_winning_condition_simp_game splitter leafCondition midCondition da reveler)
    (chooser : ABTree Unit (γ -> β -> Option ChooserMoves))
    : simp_tree splitter leafCondition midCondition da reveler chooser = Player.Proposer
    := by
     revert da reveler chooser; intro da
     -- unfold reveler_winning_condition_simp_game
     -- unfold simp_tree
     have ⟨ arena , res ⟩ := da
     revert res
     induction arena with
     | leaf v =>
       intros res reveler wProp chooser
       cases HR : reveler with
       | node i _ _ =>
         unfold reveler_winning_condition_simp_game at wProp
         rw [HR] at wProp
         simp at wProp
       | leaf p =>
         cases HP : p with
         | none => rw [HP] at HR; rw [HR] at wProp; simp [reveler_winning_condition_simp_game] at wProp
         | some ped => simp [simp_tree]; rw [HP] at HR; rw [HR] at wProp; simp [reveler_winning_condition_simp_game] at wProp; assumption
     | node b bl br HL HR =>
       intro res reveler wProp chooser
       cases HRev : reveler with
       | leaf _ => clear HL HR; rw [HRev] at wProp; simp [reveler_winning_condition_simp_game] at wProp
       | node ped pl pr =>
         cases HPed : ped with
         | none => rw [HPed] at HRev; rw [HRev] at wProp; simp [reveler_winning_condition_simp_game] at wProp
         | some proposed =>
           rw [HPed] at HRev; rw [HRev] at wProp; simp [reveler_winning_condition_simp_game] at wProp
           simp [simp_tree]
           cases HCho : chooser with
           | leaf _ => simp
           | node cf cl cr =>
             simp
             cases HCed : cf res proposed with
             | none => simp
             | some ced =>
               cases HCee : ced with
               | Now => simp; exact wProp.1
               | Continue s =>
                 cases HSide : s with
                 | Left => simp; apply HL; exact wProp.2.1
                 | Right =>simp; apply HR; exact wProp.2.2


-- Generic game focusing on |da : CompTree|
-- Here the arena is |ABTree|
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

-- Splitter Tree Game
-- This is a similar game, but here we can split da.res following a function.
-- res := [a,c], revelear can just revel something |b| and the game continues
-- |[a,b] or [b,c]|
def splitter_tree_game {α α' β β' γ γ' : Type}
    -- splitte
    (splitter : γ -> γ' -> (γ × γ))
    -- Game Mechanics
    (leafCondition : α' -> α -> γ -> Winner)
    (midCondition  : β' -> β -> γ -> γ -> γ -> Winner)
    -- Public Information
    (da : CompTree α' β' γ)
    -- Players
    (reveler : ABTree (Option α) (Option (β × γ')))
    (chooser : ABTree Unit ((γ × β × γ × γ) -> Option ChooserMoves))
    --
    : Winner :=
    -- Reveler plays first
    match da.data, reveler with
    | .leaf h, .leaf (some a) => leafCondition h a da.res
    | .node ib bl br , .node (some proposition) nextProposerLeft nextProposerRight =>
      match chooser with
      | .node cfun nextChooserLeft nextChooserRight =>
        have sp := splitter da.res proposition.2
        match cfun ⟨ da.res , ( proposition.1 , sp ) ⟩ with
        -- Chooser -> challenge hashes now.
        | some .Now =>
          midCondition ib proposition.1 da.res sp.1 sp.2
        -- Chooser chooses to go left.
        | some (.Continue .Left) =>
          splitter_tree_game splitter leafCondition midCondition ⟨ bl , sp.1 ⟩ nextProposerLeft nextChooserLeft
        -- Chooser chooses to go right.
        | some (.Continue .Right) =>
          splitter_tree_game splitter leafCondition midCondition ⟨ br , sp.2 ⟩ nextProposerRight nextChooserRight
        -- No moves
        | none => Player.Proposer
      -- Chooser does not follows computation tree.
      | _ => Player.Proposer
    -- If reveler does not follow the compuetation tree, it loses.
    | _ , _ => Player.Chooser

-- Reveler  winning condition
def reveler_winning_condition
  {α α' β β' γ : Type}
    -- Game Mechanics
    (leafCondition : α' -> α -> γ -> Winner)
    (midCondition  : β' -> β -> γ -> γ -> γ -> Winner)
    -- Public Information
    (da : CompTree α' β' γ)
    -- Players
    (reveler : ABTree (Option α) (Option (β × γ × γ)))
  : Prop :=
  match da.data , reveler with
  | .node b bl br , .node (.some proposed) left_reveler right_reveler =>
    -- If challenged, proposer wins
    midCondition b proposed.1 da.res proposed.2.1 proposed.2.2 = Player.Proposer
    -- Same for each branch
    ∧ reveler_winning_condition leafCondition midCondition
                                               {data := bl, res:=proposed.2.1}
                                               left_reveler
    ∧ reveler_winning_condition leafCondition midCondition
                                               {data := br, res:=proposed.2.2}
                                               right_reveler
   | .leaf a, .leaf (.some a') =>
     leafCondition a a' da.res = Player.Proposer
   | _ , _ => False

-- TODO Prove that this is correct
theorem winning_proposer_wins {α α' β β' γ : Type}
    -- Game Mechanics
    (leafCondition : α' -> α -> γ -> Winner)
    (midCondition  : β' -> β -> γ -> γ -> γ -> Winner)
    -- Public Information
    (da : CompTree α' β' γ)
    -- Players
    (reveler : ABTree (Option α) (Option (β × γ × γ)))
    (good_reveler : reveler_winning_condition leafCondition midCondition da reveler)
    : forall (chooser : ABTree Unit ((γ × β × γ × γ) -> Option ChooserMoves)),
      treeCompArbGame leafCondition midCondition da reveler chooser = Player.Proposer
    := sorry


-- Another generid tree, more focused on logarithmic games.
-- We may want to prove that the previous generic games and these ones are
-- equivalent?
def homogeneous_tree_game {pinfo γ : Type}
    (winning_condition  : pinfo -> γ -> γ -> γ -> Winner)
    -- Public Information -- Board and ranges.
    (da : ABTree pinfo pinfo)
    (rn : γ × γ)
    -- Players
    (reveler : ABTree (Option γ) (Option γ))
    -- chooser does not play at leaves.
    (chooser : ABTree Unit ((pinfo × γ × γ × γ) -> Option ChooserMoves))
    : Winner :=
    match da , reveler, chooser with
    -- Mid games
    | .node pub_now pub_l pub_r
      , .node (some γ_mid) re_left re_right
      , .node ch_fun  cho_left cho_right =>
      match ch_fun ⟨ pub_now , rn.1 , γ_mid , rn.2 ⟩ with
      | some .Now =>
        winning_condition pub_now rn.1 γ_mid rn.2
      | some (.Continue .Left) =>
        homogeneous_tree_game winning_condition pub_l ⟨ rn.1 , γ_mid ⟩ re_left cho_left
      | some (.Continue .Right) =>
        homogeneous_tree_game winning_condition pub_r ⟨ γ_mid , rn.2 ⟩ re_right cho_right
      | none => Player.Proposer
    -- Last single-shot game
    | .leaf pub_now , .leaf (some h) , _ =>
        winning_condition pub_now rn.1 h rn.2
    -- Bad Revealer player -- Revelear plays first.
    | .node _ _ _ , .node none _ _, _ => Player.Chooser
    | .node _ _ _ , .leaf _ , _ => Player.Chooser
    -- Bad Chooser player
    -- Revealear reveals something but chooser doesn't move.
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

-- Building up arena.
def tree_da {γ : Type} { lgn : Nat }
   (seq_da : ImpTreePath (2^lgn.succ - 1) γ γ)
   : CompTree Unit Unit (γ × γ)-- ABTree Unit Unit × (γ × γ)
   := { data := sorry -- Data does not matter here.
      , res := ⟨ seq_da.1.1 , seq_da.2 ⟩  }

-- Homogeneous game.
-- def perfect_seq_to_tree {γ : Type} {lgn : Nat}
--     -- Is this just hash eq?
--     (leafCondition : γ × γ -> Winner)
--     -- Hash compose eq?
--     (nodeCondition : γ × γ × γ -> Winner)
--     -- DA
--     (path : ISkeleton (2^lgn.succ - 1))
--     -- Players
--     (proposer : Sequence (2^lgn.succ - 1) (Option (γ × γ × γ)))
--     (chooser : Sequence (2^lgn.succ - 1) (SkElem × γ × γ × γ -> Option ChooserSmp))
--     --
--     : Winner
--     :=
--     -- Build trees out of sequences.
--     have tree_da := perfectSeq path
--     have tree_proposer := perfectSeq proposer
--     have tree_chooser := perfectSeq chooser
--     --
--     _

-- def btreePathToElem {α γ : Type} {n : Nat}
--     -- Transformation reqs
--     (leafInt : α -> γ)
--     -- Game Mechanics
--     (leafCondition : ImpTreePath 0 α γ -> Winner)
--     (nodeCondition : γ × γ × γ -> Winner)
--     -- DA
--     (da : ImpTreePath n α γ)
--     -- Players
--     (proposer : Sequence n (Option (γ × γ × γ)))
--     (chooser : Sequence n (γ × γ × γ -> Option ChooserSmp))
--     --
--     : Winner
--     :=
--     -- Transformations
--     let tDA := seqHABTree da.data.2 -- Sequence n of sides
--     let tP := ABTree.map optJoin id $ seqHABTree proposer
--     let tC := ABTree.map
--          (fun _ => some ()) (fun _ => sorry ) $ seqHABTree chooser
--     -- The transformation |seqHABTree| enables some invalid game states!
--     match n with
--        | 0 => leafCondition da
--        | .succ _pn =>
--           let treeDA : CompTree (Option SkElem) SkElem γ
--              := ⟨ tDA , da.res ⟩
--           treeCompArbGame _ _ treeDA tP tC
