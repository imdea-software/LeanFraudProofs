-- Data Structures
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes
import FraudProof.DataStructures.Sequence

import FraudProof.Games.GameDef
import FraudProof.Games.FromBtoMTree -- DAC
import FraudProof.Games.ElemInTree

-- import FraudProof.Games.FMBC


-- * Generate Honest HashTree
def generate_honest_hashtree {α ℍ : Type}
    [o : Hash α ℍ][m : HashMagma ℍ]
    (data : BTree α)
    : ABTree α (ℍ × ℍ)
    := match data with
       | .leaf v => .leaf v
       | .node bl br =>
          have bl' := generate_honest_hashtree bl
          have br' := generate_honest_hashtree br
          .node (bl'.getI' o.mhash (fun (l,r) => m.comb l r)
                ,br'.getI' o.mhash (fun (l,r) => m.comb l r) ) bl' br'

-- lemma generate_honest_hashtree = ABTree.hash_SubTree

-- * Linear L2

structure P1_Actions (α ℍ : Type) : Type
 where
 da : BTree α × ℍ
 dac_str : ABTree (Option α) (Option (ℍ × ℍ))
 gen_elem_str : {n : Nat} -> ISkeleton n -> (Sequence n (Option (ℍ × ℍ)) × Option α)

def honest_playerOne {α ℍ : Type}
  [Hash α ℍ][HashMagma ℍ]
  (val_fun : α -> Bool)
  (raw : BTree α)
  : Option (P1_Actions α ℍ)
  := if raw.fold val_fun and
     then .none
     else .some $
          { da := (raw , raw.hash_BTree)
          , dac_str := (generate_honest_hashtree raw).map .some .some
          , gen_elem_str := sorry -- all possible element challenges.
          }

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
  [BEq ℍ][o : Hash α ℍ][HashMagma ℍ]
   (val_fun : α -> Bool)
   --
   (playerOne : P1_Actions α ℍ)
   (playerTwo : (BTree α × ℍ) -> P2_Actions α ℍ)
   --
   : Bool
   := match playerTwo playerOne.da with
         | .Ok => true
         | .Invalid _e ph str => -- Merkle tree is correct, but there is an invalid element in it.
            -- Path is valid. I think in Arb is just the position. (0 <= pos < n)? play : invalid.
            match playerOne.da.fst.iaccess ph with
            | .some (.inl _) =>
                match elem_in_backward_rev
                       ph
                         playerOne.da.snd
                         (playerOne.gen_elem_str ph)
                         str
                with
                | (.Proposer , .some v) => -- v has to be e (_e now)
                  -- Proposer wins showing the element is there.
                  val_fun v
                | (.Proposer , .none) =>
                  -- Proposer wins bc challenger lost
                  true
                | (.Chooser , _) =>
                  -- Proposer fails to provide hashes?
                  false
            -- Path is not valid.
            | _ => true
         | .DAC ch_str =>
            -- Challenging Sequencer (Merkle tree is not correct)
            match data_challenge_game
                ⟨ playerOne.da.fst.map o.mhash , playerOne.da.snd ⟩
                playerOne.dac_str ch_str with
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
     (fun ⟨ n , ls , e , t⟩ => ⟨ n.succ, ls.cons {side := .Right ,  spine := t, sib := bl.hash_BTree}, e , m.comb bl.hash_BTree t⟩ )
    | .some ⟨ n , ls , e, t⟩ => .some $ ⟨ n.succ, ls.cons { side := .Left , spine := t , sib := br.hash_BTree}, e, m.comb t br.hash_BTree⟩

theorem find_valid_nothing {α ℍ : Type}
  [o : Hash α ℍ][m : HashMagma ℍ]
  (val : α -> Bool)
  ( t : BTree α )
  (valid : t.fold val and = true)
  : @find_left_invalid_path _ _ o m val t = .none
  := by
  revert valid
  induction t with
  | leaf v =>
    simp [find_left_invalid_path]
  | node _ bl br HL HR =>
    simp; intros lT rT
    simp [find_left_invalid_path]
    replace HL := HL lT
    rw [HL]; simp
    apply HR; assumption

theorem find_nothing_is_valid {α ℍ : Type}
  [o : Hash α ℍ][m : HashMagma ℍ]
  (val : α -> Bool)
  ( t : BTree α )
  : @find_left_invalid_path _ _ o m val t = .none -> t.fold val and = true
  := by
  induction t with
  | leaf v => simp [find_left_invalid_path]
  | node b bl br HL HR =>
    simp [find_left_invalid_path]
    split
    case h_1 x heq =>
      simp; intro hr; replace heq := HL heq; replace hr := HR hr; apply And.intro; all_goals { assumption }
    case h_2 x heq => simp


theorem find_invalid_path_accessed {α ℍ : Type}
  [o : Hash α ℍ][m : HashMagma ℍ]
  (val : α -> Bool)
  ( t : BTree α )
  (wit : Witness α ℍ)
  : @find_left_invalid_path _ _ o m val t = .some wit
    -> t.iaccess (wit.pathInfo.map (fun f => f.side)) = .some (.inl wit.src)
    ∧ val wit.src = false
    -- This is required for more intelligent exporations (like log)
    -- ∧ True (Sequence.head wit.pathInfo).spine = o.mhash wit.src
    -- ∧ True fold is dst
    -- ∧ True all mid matches.
  := by
  revert wit
  induction t with
  | leaf v =>
    simp [find_left_invalid_path]
    intro vF
    simp [ABTree.iaccess, sequence_forget ]
    simp [ABTree.access]
    assumption
  | node _ bl br HL HR =>
    intro wit
    simp [find_left_invalid_path]
    split
    case h_1 x heq =>
         simp
         intro x hr witD
         replace hr := HR x hr
         rw [<- witD]
         simp [ABTree.iaccess, sequence_forget, ABTree.access]
         simp [ABTree.iaccess, sequence_forget] at hr
         assumption
    case h_2 x n ls e H heq =>
     simp
     intro witD
     rw [<- witD]
     simp [ ABTree.iaccess, sequence_forget, ABTree.access ]
     simp [ ABTree.iaccess, sequence_forget] at HL
     have hl := HL _ heq
     simp at hl
     assumption


def generate_merkle_tree {α ℍ : Type}
   [o : Hash α ℍ][m : HashMagma ℍ]
   (data : BTree α) : ABTree α ℍ
   := match data with
      | .leaf v => .leaf v
      | .node bl br =>
          have bl' := generate_merkle_tree bl
          have br' := generate_merkle_tree br
          .node (m.comb (bl'.getI' o.mhash id) (br'.getI' o.mhash id)) bl' br'

def gen_chooser_opt' {ℍ : Type}
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
  [BEq ℍ][Hash α ℍ][m : HashMagma ℍ]
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
           -- From top to element.
           (.constant ( fun (top, hl , hr) => .some $ if m.comb hl hr == top then .Continue () else .Now))
           -- Naive Strategy. (We will need more info for the logarithmic game.)
 -- challenge merkle tree with strategy
 else .DAC ((generate_honest_hashtree public_data).map (fun _ => ()) gen_chooser_opt')

lemma const_comp {α β γ : Type}
 (f : α -> β) (g : γ) : (fun _ => g) ∘ f = (fun _ => g)
 := by apply funext; intro _; simp

lemma gen_chooser_opt_some {ℍ : Type} [BEq ℍ]:
  (((fun fhs x ↦ fhs x) ∘ gen_chooser_opt) ∘ some) = (fun fhs x ↦ fhs x) ∘ (@gen_chooser_opt' ℍ _)
  := by
  apply funext
  intro x; simp; apply funext; intro y
  simp [gen_chooser_opt, gen_chooser_opt']

lemma fold_getI_hash { α ℍ : Type }
  [o : Hash α ℍ][m : HashMagma ℍ]
  (b : ABTree α Unit)
  : ABTree.fold o.mhash (fun _ ↦ m.comb) b
  = ABTree.getI' o.mhash (fun x ↦ m.comb x.1 x.2) (generate_honest_hashtree b)
 := by induction b with
   | leaf v => simp [generate_honest_hashtree, ABTree.getI']
   | node _ bl br HL HR =>
     unfold generate_honest_hashtree
     simp [ABTree.getI']; congr

lemma honest_chooser_wins {α ℍ : Type}
   [BEq ℍ][LawfulBEq ℍ][o : Hash α ℍ] [m : HashMagma ℍ]
   (da : BTree α)
    : winning_condition_player (fun hc a h ↦ dac_leaf_winning_condition hc a h = true)
        (fun _x x res ↦ dac_node_winning_condition res x.1 x.2 = true) (fun _x ↦ id)
        { data := ABTree.map o.mhash id da, res := ABTree.fold o.mhash (fun _x ↦ m.comb) da }
        (ABTree.map some some (generate_honest_hashtree da))
    := by
    induction da with
    | leaf v =>
      simp
      simp [generate_honest_hashtree, winning_condition_player, dac_leaf_winning_condition]
    | node _ bl br HL HR =>
      simp [generate_honest_hashtree , winning_condition_player]
      simp at *
      apply And.intro
      · simp [dac_node_winning_condition]
        rw [<- fold_getI_hash, <- fold_getI_hash]
      · apply And.intro; all_goals {
              rw [<- fold_getI_hash]
              assumption
        }

lemma honest_chooser_accepts_valid {α ℍ : Type}
   [BEq ℍ][LawfulBEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
   (val_fun : α -> Bool)
   (data : BTree α)( mk : ℍ )
   ( da_valid : valid_da (data, mk) val_fun)
   : honest_chooser val_fun data mk = .Ok
   := by
   simp [honest_chooser]
   have none := @find_valid_nothing _ _ o m val_fun data da_valid.2
   rw [none]
   simp
   have ⟨ hash , _ ⟩ := da_valid
   simp at hash
   symm; assumption


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
         -- This step is something weird.
         -- I think protocols assumes that the result is good?
         -- rw [fres.2]
         -- split; all_goals simp
         sorry
     case false =>
       simp
       have w_cho :=
         @dac_winning_gen_chooser α ℍ _ _ _ _
                                  (da.1.map  o.mhash )
                                  -- Rev info
                                  dac_str da.2
                                  -- Chooser Info
                                  ((generate_honest_hashtree da.fst).map .some .some)
                                  (ABTree.fold o.mhash (fun _ => m.comb) da.fst)
       simp [generate_honest_hashtree] at w_cho
       rw [abtree_map_compose] at w_cho
       rw [abtree_map_compose] at w_cho
       rw [abtree_map_compose]
       rw [const_comp ] at w_cho
       rw [const_comp ] at w_cho
       rw [const_comp]
       rw [<- gen_chooser_opt_some ]
       simp at Hm
       have ass :=
            w_cho
            (honest_chooser_wins _)
            Hm
       rw [ass]
       simp
   · simp
     have ⟨ da , dac_str , gen_elem_str ⟩ := p1
     simp; intro vDa
     simp [linear_l2_protocol]
     have hcho := honest_chooser_accepts_valid val_fun da.1 da.2 vDa
     rw [hcho]
