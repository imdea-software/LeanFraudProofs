-- Data Structures
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes
import FraudProof.DataStructures.Sequence

import FraudProof.Games.GameDef
import FraudProof.Games.FromBtoMTree
import FraudProof.Games.ElemInTree


-- * Linear L2

structure P1_Actions (α ℍ : Type) : Type
 where
 da : BTree α × ℍ
 dac_str : ABTree (Option α) (Option (ℍ × ℍ))
 gen_elem_str : {n : Nat} -> ISkeleton n -> Sequence n (Option (ℍ × ℍ))

def valid_da {α ℍ : Type} [Hash α ℍ][HashMagma ℍ]
  (da : BTree α × ℍ)(val_fun : α -> Bool)
 : Prop
 -- Merkle Tree is correct
 := da.fst.hash_BTree = da.snd
 -- All elements are |val_fun| valid
 ∧ (da.fst.fold val_fun and)

inductive P2_Actions (α ℍ : Type)  : Type
  where
   | DAC (str : ABTree Unit ((ℍ × ℍ × ℍ) -> Option ChooserMoves))
   | Invalid {n : Nat} (p : α) (seq : ISkeleton n) (str : Sequence n ((ℍ × ℍ × ℍ) -> Option ChooserSmp))
   | Ok

-- Simple linear protocol, no time. Assuming no player play to lose.
-- If chooser wins, the proposed block is discarded. This is not how the real
-- world behaves.
def linear_l2_protocol{α ℍ : Type}
  -- [BEq α]
  [BEq ℍ][Hash α ℍ][HashMagma ℍ]
   (val_fun : α -> Bool)
   --
   (playerOne : P1_Actions α ℍ)
   (playerTwo : (BTree α × ℍ) -> P2_Actions α ℍ)
   --
   : Bool
   := match playerTwo playerOne.da with
         | .Ok => true
         | .Invalid e ph str => -- Merkle tree is correct, but there is an invalid element in it.
            -- Path is valid. I think in Arb is just the position. (0 <= pos < n)? play : invalid.
            match playerOne.da.fst.iaccess ph with
            | .some (.inl _) =>
                match elem_in_forward ph e playerOne.da.snd
                                (playerOne.gen_elem_str ph)
                                str
                with
                | .Proposer =>
                  -- Proposer wins showing the element is there.
                  val_fun e
                | .Chooser =>
                  -- Proposer fails to provide hashes?
                  false
            -- Path is not valid.
            | _ => true
         | .DAC ch_str =>
            -- Challenging Sequencer (Merkle tree is not correct)
            match data_challenge_game ⟨ playerOne.da.fst.map (fun _ => ()) , playerOne.da.snd ⟩ playerOne.dac_str ch_str with
            | .Proposer => true
            | .Chooser => false

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

theorem find_nothing_is_valid {α ℍ : Type}
  [o : Hash α ℍ][m : HashMagma ℍ]
  (val : α -> Bool)
  ( t : BTree α )
  : @find_left_invalid_path _ _ o m val t = .none -> t.fold val and = true
  := sorry

theorem find_invalid_path_accessed {α ℍ : Type}
  [o : Hash α ℍ][m : HashMagma ℍ]
  (val : α -> Bool)
  ( t : BTree α )
  (wit : Witness α ℍ)
  : @find_left_invalid_path _ _ o m val t = .some wit
    -> t.iaccess (wit.pathInfo.map (fun f => f.side)) = .some (.inl wit.src)
    ∧ val wit.src = false
    ∧ True -- (Sequence.head wit.pathInfo).spine = o.mhash wit.src
    ∧ True -- fold is dst
    ∧ True -- all mid matches.
  := sorry

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

theorem honest_chooser_valid {α ℍ}
   [BEq ℍ][LawfulBEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
   (val_fun : α -> Bool)
   (p1 : P1_Actions α ℍ)
   : linear_l2_protocol val_fun p1 ( fun (t, mt) => honest_chooser val_fun t mt)
     ↔ valid_da p1.da val_fun
   := by
   apply Iff.intro
   · have ⟨ da , dac_str, gen_elem_str ⟩ := p1
     unfold linear_l2_protocol
     simp [honest_chooser]
     unfold valid_da
     cases Hm : (da.2 == ABTree.fold o.mhash (fun x ↦ m.comb) da.1)
     case true =>
       simp
       cases Hval : @find_left_invalid_path α ℍ _ _ val_fun da.1 with
       | none =>
         simp at *
         apply And.intro
         · symm; assumption
         · apply @find_nothing_is_valid α ℍ o m val_fun; assumption
       | some wit =>
         simp at *
         have fres := find_invalid_path_accessed val_fun da.1 wit Hval
         unfold Sequence.map at fres
         rw [fres.1]
         simp
         rw [fres.2.1]
         split
         · simp
         · simp
     case false =>
       simp


   · _
