import FraudProof.Games.GameDef -- Players, Winner

import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

import FraudProof.Games.GenericTree -- Generic Game

----------------------------------------
-- * BTree as hashes.
-- We know the structure of the data plus the hashes of their leaves.
structure ComputationTree (α ℍ : Type) where
  computation : BTree α -- Btree in this case, in can be generalized
  res : ℍ
  -- {𝔸}, fold 𝔸_hash computation = res
  -- one binary operation and leafs (In this case, that's why BTree)
----------------------------------------

def dac_leaf_winning_condition {α ℍ : Type} [BEq ℍ]
  [o : Hash α ℍ](hc : ℍ) (a : α)(_h : ℍ) : Bool := o.mhash a == hc

def dac_node_winning_condition {ℍ : Type} [BEq ℍ]
  [m : HashMagma ℍ] (top hl hr : ℍ) : Bool := m.comb hl hr == top
@[simp]
def data_challenge_game{α ℍ : Type}
    [BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
    (da : ComputationTree ℍ ℍ)
    --
    (reveler : ABTree (Option α) (Option (ℍ × ℍ)) )
    (chooser : ABTree Unit (ℍ × ℍ × ℍ -> Option ChooserMoves))
    --
    : Winner :=
    @treeCompArbGame ℍ α Unit ℍ
      -- Leaf winning condition
      dac_leaf_winning_condition
      -- Node winning condition
      (fun _  =>  dac_node_winning_condition)
      -- DA
      ⟨ da.computation , da.res ⟩
      -- Revelear Strategy
      reveler
      -- Chooser Strategy
      (ABTree.map
        (fun _ => ())
        (fun fhs ⟨hrs , hl , hr ⟩ => fhs ⟨ hrs, hl , hr ⟩)
        chooser)

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

theorem dac_winning_gen_chooser {α ℍ : Type}
    [hash : Hash α ℍ][HashMagma ℍ]
    [BEq ℍ][LawfulBEq ℍ]
    -- Public Information
    (pub_data : ABTree ℍ Unit)
    -- Players
    (revealer : ABTree (Option α) (Option (ℍ × ℍ)))(rev_res : ℍ)
    (chooser : ABTree (Option α) (Option (ℍ × ℍ)))(ch_res : ℍ)
    -- Chooser knows the data and hashes do not match
    (good_chooser: winning_condition_player
                    (fun hc a h => dac_leaf_winning_condition hc a h)
                    (fun _ (l,r) res => dac_node_winning_condition res l r)
                    (fun _ => id) ⟨ pub_data , ch_res ⟩ chooser)
    (hneq : ¬ rev_res = ch_res)
    : data_challenge_game ⟨ pub_data , rev_res ⟩
         revealer (chooser.map (fun _ => ()) gen_chooser_opt)
         = Player.Chooser
    := sorry


@[simp]
def treeArbitrationGame {α ℍ : Type}
    [BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
    (da : ComputationTree ℍ ℍ)
    --
    (reveler : ABTree (Option α) (Option (ℍ × ℍ)) )
    (chooser : ABTree Unit (ℍ × ℍ × ℍ -> Option ChooserMoves))
    --
    : Winner :=
    @treeCompArbGame ℍ α Unit ℍ
      -- Leaf winning condition
      (fun ha data res => (o.mhash data == ha) ∧ (ha == res))
      -- Node winning condition
      (fun _ r hl hr =>  m.comb hl hr == r)
      -- DA
      ⟨ da.computation , da.res ⟩
      -- Revelear Strategy
      reveler
      -- Chooser Strategy
      (ABTree.map
        (fun _ => ())
        (fun fhs ⟨hrs , hl , hr ⟩ => fhs ⟨ hrs, hl , hr ⟩)
        chooser)
----------------------------------------

@[simp]
def arbitrationTree {α ℍ : Type}
    [BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
    (arena : ABTree Unit Unit)
    (res : ℍ)
    --
    (reveler : ABTree (Option α) (Option (ℍ×ℍ)) )
    (chooser : ABTree Unit (ℍ × ℍ × ℍ -> Option ChooserMoves))
    --
    : Winner :=
    @treeCompArbGame Unit α Unit ℍ
      -- Leaf winning condition
      (fun _ a hres => o.mhash a == hres)
      -- Node winning condition
      (fun _ r hl hr =>  m.comb hl hr == r)
      -- DA
      ⟨ arena , res ⟩
      -- Revelear Strategy
      reveler
      -- Chooser Strategy
      (ABTree.map (fun _ => ()) (fun fhs ⟨hrs , hl , hr ⟩ => fhs ⟨ hrs, hl , hr ⟩) chooser)

