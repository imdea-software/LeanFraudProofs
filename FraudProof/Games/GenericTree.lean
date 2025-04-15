import FraudProof.Games.GameDef
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.SeqBTree -- Sequence -> BTree

import FraudProof.DataStructures.MTree -- Merkle-Tree

----------------------------------------
-- * Range
abbrev Range (ℍ : Type) := ℍ × ℍ

def all_true (ls : List Bool) : Bool := ls.all id

def leaf_condition_range {ℍ : Type}[BEq ℍ]
  := fun (_k : Unit) (h : ℍ) (hda : ℍ × ℍ)
     => all_true [ h == hda.1 , hda.1 == hda.2]

-- Defining mid condition when going forward one step.
-- That means
-- [a -> b]!n.succ ->
--  P-> (c,d), [a -> c]!n and (c (+) d = b)
def mid_condition_range_one_step_forward {ℍ : Type}[BEq ℍ][m : HashMagma ℍ]
  : Unit -- Arena conditions
  -- -> SkElem -- Extra proposed
  -> Range ℍ -- Current Data
  -- Data Proposed
  -> Range ℍ -> Range ℍ
  -> Bool
  := (fun _ hres hl hr =>
        let ⟨ parent_from , parent_to⟩ := hres -- [a -> b]
        let ⟨ left_from , left_to⟩ := hl -- [a -> c]
        let ⟨ right_l , right_r ⟩ := hr -- (c, d)
        -- let new_to := match side with
        --               | .inl _ => right_l
        --               | .inr _ => right_r
          -- Mid condition is the expected one
        all_true
            [ parent_from == left_from
            , left_to == right_l
            , (m.comb right_l right_r) == parent_to
            ]
      )

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
-- These can vary from game to game.
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
def treeCompArbGame {α α' β γ : Type}
    -- Game Mechanics
    (leafCondition : α -> α' -> γ -> Bool)
    (midCondition  : β -> γ -> γ -> γ -> Bool)
    -- Public Information
    (da : CompTree α β γ)
    -- Players
    (reveler : ABTree (Option α') (Option (γ × γ)))
    (chooser : ABTree Unit ((γ × γ × γ) -> Option ChooserMoves))
    --
    : Winner :=
    -- Reveler plays first
    match da.data, reveler with
    | .leaf h, .leaf (some a) =>
       if leafCondition h a da.res then Player.Proposer else Player.Chooser
    | .node ib bl br , .node (some proposition) nextProposerLeft nextProposerRight =>
      match chooser with
      | .node cfun nextChooserLeft nextChooserRight =>
        match cfun ⟨ da.res , proposition ⟩ with
        -- Chooser -> challenge hashes now.
        | some .Now =>
        if midCondition ib da.res proposition.1 proposition.2
        then Player.Proposer else Player.Chooser
        -- Chooser chooses to go left.
        | some (.Continue .Left) =>
          treeCompArbGame leafCondition midCondition ⟨ bl , proposition.1 ⟩ nextProposerLeft nextChooserLeft
        -- Chooser chooses to go right.
        | some (.Continue .Right) =>
          treeCompArbGame leafCondition midCondition ⟨ br , proposition.2 ⟩ nextProposerRight nextChooserRight
        -- No moves
        | none => Player.Proposer
      -- Chooser does not follows computation tree.
      | _ => Player.Proposer
    -- If reveler does not follow the compuetation tree, it loses.
    | _ , _ => Player.Chooser

def tree_comp_winning_conditions {α α' β γ : Type}
    -- Game Mechanics
    (leafCondition : α -> α' -> γ -> Prop)
    (midCondition  : β -> γ -> γ -> γ -> Prop)
    -- Public Information
    (da : CompTree α β γ)
    (player : ABTree (Option α') (Option (γ × γ)))
  : Prop :=
  match da.data , player with
  | .leaf a' , .leaf (.some a) => leafCondition a' a da.res
  | .node b' gl gr , .node (.some b) pl pr =>
    midCondition b' da.res b.1 b.2
    ∧ tree_comp_winning_conditions leafCondition midCondition ⟨ gl , b.1 ⟩ pl
    ∧ tree_comp_winning_conditions leafCondition midCondition ⟨ gr , b.2 ⟩ pr
  | _ , _ => False

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

----------------------------------------
-- * Reveler  winning condition
-- Reveler wins all possible games.
def reveler_winning_condition
  {α α' β γ : Type}
    -- Game Mechanics
    (leafCondition : α -> α' -> γ -> Bool)
    (midCondition  : β -> γ -> γ -> γ -> Bool)
    -- Public Information
    (da : CompTree α β γ)
    -- Players
    (reveler : ABTree (Option α') (Option (γ × γ)))
  : Prop :=
  match da.data , reveler with
  | .node b bl br , .node (.some proposed) left_reveler right_reveler =>
    -- If challenged, proposer wins
    midCondition b da.res proposed.1 proposed.2
    -- Same for each branch
    ∧ reveler_winning_condition leafCondition midCondition
                                               {data := bl, res:=proposed.1}
                                               left_reveler
    ∧ reveler_winning_condition leafCondition midCondition
                                               {data := br, res:=proposed.2}
                                               right_reveler
   | .leaf a, .leaf (.some a') =>
     leafCondition a a' da.res
   | _ , _ => False

def winning_condition_player {α α' β β' γ : Type}
    -- Game Mechanics
    (leafCondition : α' -> α -> γ -> Prop)
    (midCondition  : β' -> β -> γ -> Prop) -- If True then P.Proposer.
    (splitter : γ -> β -> γ × γ)
    -- Public Information
    (da : CompTree α' β' γ)
    (player : ABTree (Option α) (Option β))
  : Prop :=
  match da.data , player with
  | .leaf a' , .leaf (.some a) => leafCondition a' a da.res
  | .node b' gl gr , .node (.some b) pl pr =>
    midCondition b' b da.res
    ∧ winning_condition_player leafCondition midCondition splitter ⟨ gl , (splitter da.res b).1 ⟩ pl
    ∧ winning_condition_player leafCondition midCondition splitter ⟨ gr , (splitter da.res b).2 ⟩ pr
  | _ , _ => False

-- Gen chooser from knowing the path?
-- Assuming we have a DA that the top hash is correct.
-- When splitting if it is not the one the player knows to be correct, goes to the right.
-- When splitting if the proposed hash *is* the one the player knows to be correct, goes to the left.
-- Inv: top hash is always correct, data it is not. If top hash is not correct,
-- we do not know what tree are we playing with. In other words, we do not know the data.
--
def gen_to_fun_chooser {α β γ: Type}[BEq β]
    : ABTree (Option α) (Option β) -> ABTree Unit (γ -> β -> Option ChooserMoves)
    := ABTree.map
      (fun _ => ())
      (fun mid _r proposed =>
        if mid == proposed
        then .some (.Continue .Left)
        else .some (.Continue .Right)
        )

theorem winning_proposer_wins {α α' β' γ : Type}
    -- Game Mechanics
    (leafCondition : α' -> α -> γ -> Bool)
    (midCondition  : β' -> γ -> γ -> γ -> Bool)
    -- Public Information
    (da : CompTree α' β' γ)
    -- Players
    (reveler : ABTree (Option α) (Option (γ × γ)))
    (good_reveler : reveler_winning_condition leafCondition midCondition da reveler)
    : forall (chooser : ABTree Unit ((γ × γ × γ) -> Option ChooserMoves)),
      treeCompArbGame leafCondition midCondition da reveler chooser = Player.Proposer
    := by
 revert good_reveler reveler
 have ⟨ data , res ⟩ := da
 revert res
 induction data with
 | leaf v =>
   intros res reveler rev_win ch
   cases reveler with
   | node _ _ _ => simp [reveler_winning_condition] at rev_win
   | leaf v' =>
     cases v' with
     | none => simp [reveler_winning_condition] at rev_win
     | some p =>
       simp [treeCompArbGame]
       simp [reveler_winning_condition] at rev_win
       assumption
 | node g gl gr IndL IndR =>
   intros res reveler rev_win ch
   cases reveler with
   | leaf _ => simp [reveler_winning_condition] at rev_win
   | node mb rl rr =>
     cases mb with
     | none => simp [reveler_winning_condition] at rev_win
     | some rev_p =>
       simp [treeCompArbGame]
       simp [reveler_winning_condition] at rev_win
       cases ch with
       | leaf _ => simp
       | node mch chl chr =>
         simp; split
         case h_1 x heq => simp; exact rev_win.1
         case h_2 x heq => apply IndL; exact rev_win.2.1
         case h_3 x heq => apply IndR; exact rev_win.2.2
         case h_4 x heq => simp


def prop_winner : Winner -> Prop
    | .Proposer => True
    | .Chooser => False

lemma prop_win_chooser (p : Winner)
  : ¬ prop_winner p
    ↔ p = Player.Chooser
  := by
  cases p
  all_goals { simp [prop_winner]}

-- Principle of inoncense.
-- If Hashes match what we know, there is no reason to challenge them.
-- So, in our world, we assume they are correct if the observable data is okay.
axiom no_challenge_matching_data {α α' β β' γ : Type}
     {splitter : γ -> β -> γ × γ}
     {da : CompTree α' β' γ}
     {leafCondition : α' -> α -> γ -> Prop}
     {midCondition  : β' -> β -> γ -> Prop}
     { player : ABTree (Option α) (Option β) }
     ( knowing : winning_condition_player leafCondition midCondition splitter da player )
     : forall {other_player : ABTree (Option α) (Option β) },
       winning_condition_player leafCondition midCondition splitter da other_player

-- This is a generic proof. There is a specific one at ElemInTree!
-- theorem winning_chooser_wins {α α' β β' γ : Type}
--     [BEq β][LawfulBEq β]
--     (splitter : γ -> β -> γ × γ)
--     -- Conditions
--     (leafCondition : α' -> α -> γ -> Winner)
--     (midCondition  : β' -> β -> γ -> Winner)
--     -- Public Information
--     (da : CompTree α' β' γ)
--     -- Reveler
--     (reveler : ABTree (Option α) (Option β))
--     -- Chooser
--     (wise_chooser : ABTree (Option α) (Option β))
--     -- Assumptions
--     (win_chooser : winning_condition_player
--                    (fun x y z => prop_winner $ leafCondition x y z)
--                    (fun x y z => prop_winner $ midCondition x y z) splitter da wise_chooser)
--     (lossing_reveler : ¬ winning_condition_player
--                    (fun x y z => prop_winner $ leafCondition x y z)
--                    (fun x y z => prop_winner $ midCondition x y z) splitter da reveler)
--     : simp_tree splitter
--       leafCondition
--       midCondition
--       da reveler (gen_to_fun_chooser wise_chooser) = Player.Chooser
--     := by
--  revert reveler wise_chooser da; intro da
--  have ⟨ data , res ⟩ := da
--  revert res; clear da
--  -- unfold simp_tree; simp
--  induction data with
--  | leaf a' =>
--    intros res reveler chooser wCh loPro
--    unfold simp_tree
--    cases H : reveler with
--    | leaf r =>
--      cases r with
--      | some p =>
--        simp
--        unfold winning_condition_player at loPro; simp at loPro
--        rw [H] at loPro; simp at loPro
--        rw [prop_win_chooser ] at loPro
--        assumption
--      | none => simp
--    | node _ _ _ => simp
--  | node b' gl gr HIndL HIndR =>
--    intros res reveler wise_chooser wCh loPro
--    cases HR : reveler with
--    | leaf _ => simp [simp_tree]
--    | node p pl pr =>
--      cases HP : p with
--      | none => simp [simp_tree]
--      | some proposed =>
--        simp [gen_to_fun_chooser]
--        cases HC : wise_chooser with
--        | leaf _ => rw [HC] at wCh; simp [winning_condition_player] at wCh
--        | node ch chL chR =>
--          simp
--          cases HCed : ch with
--          | none =>
--            rw [HC, HCed] at wCh
--            simp [winning_condition_player] at wCh
--          | some ched =>
--            simp [simp_tree]
--            split
--            case h_1 x heq =>
--             -- simp at heq
--             have iteeq := @ite_eq_iff _ (ched == proposed) _ (some (ChooserPrimMoves.Continue Side.Left)) (some (ChooserPrimMoves.Continue Side.Right)) (some ChooserPrimMoves.Now)
--             rw [iteeq] at heq
--             simp at heq
--            case h_2 x heq =>
--              simp at heq
--              subst heq
--              -- Win Left Condition
--              rw [ HC, HCed ] at wCh ; simp [winning_condition_player] at wCh
--              -- have subwin_ch := wCh.2.1 ; rw [heq] at subwin_ch
--              -- Not Winning?
--              rw [HR,HP] at loPro --; simp [winning_condition_player] at loPro
--              unfold winning_condition_player at loPro
--              have lemm {a b c : Prop} :  a ∧ b ∧ c <-> a ∧ c ∧ b := by tauto
--              rw [lemm] at loPro
--              simp at loPro
--              replace loPro := loPro wCh.1 (no_challenge_matching_data wCh.2.2)
--              have hind := HIndL (splitter res ched).1 pl chL
--                wCh.2.1
--                loPro
--              exact hind
--            case h_3 x heq =>
--              simp at heq
--              -- Winning chooser left
--              rw [HC, HCed] at wCh; simp [winning_condition_player] at wCh
--              -- unfold winning_condition_player at wCh
--              have hind := HIndR (splitter res proposed).2 pr chR
--                -- This case is the interesting one. We need to specialize our winning chooser.
--                -- In this case, we need to assume something else, like, if res
--                -- does not match, then I won't play
--                -- We have that data is correct, but we need to show that it wins
--                -- against all other possible datum.
--                ( by sorry )
--                --
--                sorry
--              exact hind
--            case h_4 x heq =>
--              have iteeq := @ite_eq_iff _ (ched == proposed) _ (some (ChooserPrimMoves.Continue Side.Left)) (some (ChooserPrimMoves.Continue Side.Right)) none
--              rw [iteeq] at heq
--              simp at heq
----------------------------------------

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
         match proposer.head with
         | .none => Player.Chooser -- Proposer forfeits the game
         | .some proposed =>
           match chooser.head ⟨ da.res , proposed ⟩ with
           | .none => Player.Proposer -- Chooser forfeits the game
           | .some .Now => nodeCondition ⟨ da.res , proposed ⟩
           | .some (.Continue _) =>
             have nextRes := match da.data.2.head with
                    | .Left => proposed.1
                    | .Right => proposed.2
             pathToElem leafCondition nodeCondition
               -- Next step DA
               ⟨ ⟨ da.data.1 , da.data.2.tail⟩ , nextRes ⟩
               -- Next step players
               proposer.tail
               chooser.tail


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
-- def tree_da {γ : Type} { lgn : Nat }
--    (seq_da : ImpTreePath (2^lgn.succ - 1) γ γ)
--    : CompTree Unit Unit (γ × γ)-- ABTree Unit Unit × (γ × γ)
--    := { data := sorry -- Data does not matter here.
--       , res := ⟨ seq_da.1.1 , seq_da.2 ⟩  }

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

def Unique_Leaf_Condition {α α' γ : Type}(lc : α -> α' -> γ -> Bool)
  : Prop := forall (a : α)(x y : α')(r r' : γ),
        ¬ r = r' -> lc a x r = true -> lc a y r' = false

def Unique_Mid_Condition {β γ : Type}(md : β -> γ -> γ -> γ -> Bool)
  : Prop := forall (b : β)( k1 k2 x y : γ), ¬ (k1 = k2 ) -> ¬ md b k1 x y =  md b k2 x y

theorem chooser_data_availability {α α' β γ : Type}
    [BEq γ][LawfulBEq γ]
    -- Conditions
    (leafCondition : α -> α' -> γ -> Bool)
    (unique_leaf : Unique_Leaf_Condition leafCondition)
    (midCondition  : β -> γ -> γ -> γ -> Bool)
    (unique_mid : Unique_Mid_Condition midCondition) -- This is provided by hashing stuff
    -- Public Information
    -- (da : CompTree α β γ)
    (data : ABTree α β)
    (ch_res da_res : γ)
    -- Reveler
    (reveler : ABTree (Option α') (Option (γ × γ)))
    -- Chooser
    (wise_chooser : ABTree α' (γ × γ))
    -- Assumptions
    (win_chooser : tree_comp_winning_conditions
                   (fun x y z => leafCondition x y z)
                   (fun w x y z  => midCondition w x y z) ⟨ data, ch_res ⟩ (wise_chooser.map some some))
    (hneq : ¬ (ch_res = da_res))
    : treeCompArbGame leafCondition midCondition
                      ⟨ data , da_res⟩ reveler
                      ( wise_chooser.map (fun _ => ()) (fun k gargs =>
                       if (k.1 == gargs.2.1 && k.2 == gargs.2.2)
                       then some .Now
                       else if (k.1 != gargs.2.1)
                            then some $ .Continue .Left
                            else some $ .Continue .Right
                       ))
                      = Player.Chooser
    := by
    revert hneq win_chooser wise_chooser reveler ch_res da_res
    induction data with
    | leaf v =>
     intros ch_res da_res rev wch win_ch nheq
     cases rev with
     | node _ _ _ => simp [treeCompArbGame]
     | leaf mp => cases mp with
                  | none => simp [treeCompArbGame]
                  | some p =>
                    simp [treeCompArbGame]
                    cases wch with
                    | node _ _ _ => simp [tree_comp_winning_conditions] at win_ch
                    | leaf ch_l =>
                      simp [tree_comp_winning_conditions, prop_winner] at win_ch
                      -- Uniqueness of Leaves - Collision free hash!!
                      unfold Unique_Leaf_Condition at unique_leaf
                      apply unique_leaf
                      exact nheq
                      assumption
    | node gb gl gr HIndL HIndR =>
     intros ch_res da_res rev wch win_ch nheq
     cases rev with
     | leaf _ => simp [treeCompArbGame]
     | node mrev revl revr =>
       cases mrev with
       | none =>  simp [treeCompArbGame]
       | some proposed =>
         simp [treeCompArbGame]
         cases wch with
         | leaf _ => simp [tree_comp_winning_conditions] at win_ch
         | node ch_n chl chr =>
           simp [tree_comp_winning_conditions] at win_ch
           simp
           split
           case h_1 x heq =>
             clear HIndL HIndR
             rw [ite_eq_iff] at heq
             cases heq
             case inl h =>
               simp at h
               have micond := win_ch.1
               have umid := unique_mid gb ch_res da_res proposed.1 proposed.2 nheq
               rw [h.1,h.2] at micond
               rw [micond] at umid
               simp at *; assumption
             case inr h => -- Nonsense
               simp at *
               replace ⟨ hpneq , h ⟩ := h
               rw [ite_eq_iff] at h
               simp at h
           case h_2 x heq =>
             apply HIndL; exact win_ch.2.1
             clear HIndL HIndR
             rw [ite_eq_iff] at heq
             simp at heq
             exact heq.2
           case h_3 x heq =>
             apply HIndR; exact win_ch.2.2
             clear HIndL HIndR
             rw [ite_eq_iff] at heq
             simp at heq
             replace ⟨heq , arg ⟩ := heq
             tauto
           case h_4 x heq =>
             clear HIndL HIndR win_ch
             rw [ite_eq_iff] at heq
             simp at heq
             replace ⟨ _ , heq ⟩ := heq
             rw [ite_eq_iff] at heq
             simp at heq

--
--
@[simp]
def leaf_condition_length_one {ℍ : Type}[BEq ℍ][HashMagma ℍ]
  : SkElem -> ℍ -> Range ℍ -> Bool
  := (fun side prop ⟨ src , dst ⟩ => op_side side src prop == dst)

-- Simpler game using splitter.
def spl_game {ℍ : Type}[BEq ℍ][m : HashMagma ℍ]
    -- DA provides last two sides.
    (da : CompTree SkElem Unit (Range ℍ))
    --
    (proposer : ABTree (Option ℍ) (Option ℍ))
    (chooser : ABTree Unit (Range ℍ -> ℍ -> Option ChooserMoves))
    --
    : Winner
    :=
    simp_tree
      -- Splitting range into two ranges
      (fun (a,b) c => ((a,c),(c,b)))
      (fun s h rh => winning_proposer $ @leaf_condition_length_one _ _ m s h rh)
      -- Chooser won't challenge these. Game is played until reaching a leaf.
      (fun _ _ _ => Player.Proposer)
      da proposer chooser

--

def gen_chooser_opt {ℍ : Type}
   -- [DecidableEq ℍ]
   [BEq ℍ]
   (data : Option (ℍ × ℍ) )
   (proposed : ℍ × ℍ × ℍ)
   : Option ChooserMoves
   := data.map ( fun (l , r) =>
     if l == proposed.2.1 ∧ r == proposed.2.2
     then .Now
     else if ¬ l == proposed.2.1
          then .Continue .Left
          else .Continue .Right
   )
