-- Data Structures
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes
import FraudProof.DataStructures.Sequence

import FraudProof.Games.GameDef
import FraudProof.Games.FromBtoMTree
import FraudProof.Games.ElemInTree


-- * Linear L2

inductive P1_Actions (α ℍ : Type) : Type
  where
  | Propose (da : BTree α × ℍ)
   (proposed_dac_strategy : ABTree (Option α) (Option (ℍ × ℍ)))
   (proposed_elem_strategies : {n : Nat} -> ISkeleton n -> Sequence n (Option (ℍ × ℍ)))

inductive P2_Actions (α ℍ : Type)  : Type
  where
   | DAC (str : ABTree Unit ((ℍ × ℍ × ℍ) -> Option ChooserMoves))
   | Invalid {n : Nat} (p : α) (seq : ISkeleton n) (str : Sequence n ((ℍ × ℍ × ℍ) -> Option ChooserSmp))
   | Ok

-- Simple linear protocol, no time. Assuming no player play to lose.
-- If chooser wins, the proposed block is discarded. This is not how the real
-- world behaves.
def linear_l2_protocol{α ℍ : Type}
  [BEq α][BEq ℍ][Hash α ℍ][HashMagma ℍ]
   (val_fun : α -> Bool)
   --
   (playerOne : P1_Actions α ℍ)
   (playerTwo : (BTree α × ℍ) -> P2_Actions α ℍ)
   --
   : Option (BTree α × ℍ)
   := match playerOne with
      | .Propose da dac_str elem_str =>
        match playerTwo da with
         | .Ok => .some da
         | .Invalid e ph str => -- Merkle tree is correct, but there is an invalid element in it.
            -- Path is valid. I think in Arb is just the position. (0 <= pos < n)? play : invalid.
            match da.fst.iaccess ph with
            | .some (.inl _) =>
                match elem_in_forward ph e da.snd
                                (elem_str ph)
                                str
                with
                | .Proposer =>
                  -- Proposer wins showing the element is there.
                  if val_fun e then .some da else .none
                | .Chooser =>
                  -- Proposer fails to provide hashes?
                  .none
            -- Path is not valid.
            | _ => .some da
         | .DAC ch_str =>
            -- Challenging Sequencer (Merkle tree is not correct)
            match data_challenge_game ⟨ da.fst.map (fun _ => ()) , da.snd ⟩ dac_str ch_str with
            | .Proposer => .some da
            | .Chooser => .none

-- ** Crafting Honest Players.
-- *** Honest Player One. -- Proposer
-- *** Honest Player Two. -- Chooser
--
-- **** Witness Finding.
structure IH (ℍ : Type) where
  side : SkElem
  spine : ℍ
  sib : ℍ

structure Witness (α ℍ : Type) : Type
  where
   length :  Nat
   pathInfo : Sequence length (IH ℍ)
   src : α
   dst : ℍ

-- find (if there is one) the leftest invalid value.
def find_left_invalid_path {α ℍ: Type}
  [o : Hash α ℍ][m : HashMagma ℍ]
  (val : α -> Bool) :
  BTree α -> Option (Witness α ℍ)
  | .leaf a => if val a then none else some ⟨ 0 , .nil , a , o.mhash a ⟩
  | .node bl br =>
    match find_left_invalid_path val bl with
    | .none => (find_left_invalid_path val br).map
     (fun ⟨ n , ls , e , t⟩ => ⟨ n.succ, ls.snoc {side := .Right ,  spine := t, sib := bl.hash_BTree}, e , m.comb bl.hash_BTree t⟩ )
    | .some ⟨ n , ls , e, t⟩ => .some $ ⟨ n.succ, ls.snoc { side := .Left , spine := t , sib := br.hash_BTree}, e, m.comb t br.hash_BTree⟩
-- Gen chooser.
def generate_honest_chooser {α ℍ : Type}
    [o : Hash α ℍ][m : HashMagma ℍ]
    (data : BTree α)
    : ABTree α (ℍ × ℍ)
    := match data with
       | .leaf v => .leaf v
       | .node bl br =>
          have bl' := generate_honest_chooser bl
          have br' := generate_honest_chooser br
          .node (bl'.getI' o.mhash (fun (l,r) => m.comb l r)
                ,br'.getI' o.mhash (fun (l,r) => m.comb l r) ) bl' br'

def generate_merkle_tree {α ℍ : Type}
   [o : Hash α ℍ][m : HashMagma ℍ]
   (data : BTree α) : ABTree α ℍ
   := match data with
      | .leaf v => .leaf v
      | .node bl br =>
          have bl' := generate_merkle_tree bl
          have br' := generate_merkle_tree br
          .node (m.comb (bl'.getI' o.mhash id) (br'.getI' o.mhash id)) bl' br'

def gen_chooser_opt {ℍ : Type}
   [BEq ℍ]
   (data : ℍ × ℍ )
   (proposed : ℍ × ℍ × ℍ)
   : Option ChooserMoves
   := .some $
     if data.1 == proposed.2.1 ∧ data.2 == proposed.2.2
     then .Now
     else if ¬ data.1 == proposed.2.1
          then .Continue .Left
          else .Continue .Right

def honest_chooser {α ℍ : Type}
  [BEq ℍ][Hash α ℍ][HashMagma ℍ]
  (val_fun : α -> Bool)
  (public_data : BTree α) (da_mtree : ℍ)
  : P2_Actions α ℍ
 :=
 -- Check if the merkle tree matches
 if da_mtree == public_data.hash_BTree
 -- If so, look up invalid elements
 then
    match @find_left_invalid_path α ℍ _ _ val_fun public_data with
      -- all valid elements, ok
      | .none => .Ok
      -- return where the invalid element is
      | .some ph =>
        .Invalid
           ph.src
           (ph.pathInfo.map (fun p => p.side) )
           -- Naive Strategy. (We will need more info for the logarithmic game.)
           ( ph.pathInfo.map (fun i (s1,s2,t) => .some $ if op_side i.side s1 s2 == t then .Continue () else .Now) )
 -- challenge merkle tree with strategy
 else .DAC ((generate_honest_chooser public_data).map (fun _ => ()) gen_chooser_opt)
