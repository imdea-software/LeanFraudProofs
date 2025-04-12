-- Data Structures
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes
import FraudProof.DataStructures.Sequence
import FraudProof.DataStructures.TreeAccess -- Access

import FraudProof.Games.GameDef
import FraudProof.Games.FromBtoMTree -- DAC
import FraudProof.Games.ElemInTree

/-!
# Arranger Block Validity Fraud Proofs

We explore a simple protocol with two kind of players: One proposing blocks and
the other just challenging.

The main goal is to prove that when we have an honest challenger challenging
only /good/ blocks are accepted: See `honest_chooser_valid`
-/

-- This depends on what game we are playing.
-- def generate_honest_strategies_forward {α ℍ : Type}
--     -- Tree with anotations.
--     (t : ABTree α (MkData ℍ))
--     {n : Nat}(ph : ISkeleton n)
--     : Sequence n (Option (ℍ × ℍ) × Option α)
--     := sorry

-- * Linear L2

structure P1_Actions (α ℍ : Type) : Type
 where
 da : BTree α × ℍ
 dac_str : ABTree (Option α) (Option (ℍ × ℍ))
 gen_elem_str : {n : Nat} -> ISkeleton n -> (Sequence n (Option (ℍ × ℍ)) × Option α)

-- Honest Proposer takes raw data |t| and creates a claim.
-- def honest_playerOne {α ℍ : Type} [DecidableEq α]
--   [Hash α ℍ][HashMagma ℍ]
--   (val_fun : α -> Bool)
--   (t : BTree α)
--   : Option (P1_Actions α ℍ)
--   := if t.fold val_fun and ∧ (find_dups id t.toList).isNone
--      then .some $
--           { da := (t , t.hash_BTree)
--           , dac_str := (t.hash_SubTree).map .some .some
--           , gen_elem_str := sorry -- all possible element challenges.
--           }
--      else .none


structure Local_valid {α ℍ : Type}[DecidableEq α][Hash α ℍ][HashMagma ℍ]
          (data : BTree α)(mk : ℍ)(val_fun : α -> Bool)
  where
  MkTree : data.hash_BTree = mk
  ValidElems : data.fold val_fun and = true
  NoDup : List.Nodup data.toList

def Valid_Seq {α ℍ : Type} {lgn : Nat}
  [DecidableEq α][Hash α ℍ][HashMagma ℍ]
  (data : Sequence (2^lgn) α)(merkle_tree : ℍ)(P : α -> Bool)
  := Local_valid (perfectSeqLeaves data) merkle_tree P

def local_valid {α ℍ : Type} [DecidableEq α][Hash α ℍ][HashMagma ℍ]
  (da : BTree α × ℍ)(val_fun : α -> Bool) : Prop
 -- Merkle Tree is correct
 := da.fst.hash_BTree = da.snd
 -- All elements are |val_fun| valid
 ∧ (da.fst.fold val_fun and)
 -- There are no duplicated elements.
 ∧ List.Nodup da.fst.toList

theorem struct_and_iff_valid {α ℍ : Type}[DecidableEq α][Hash α ℍ][HashMagma ℍ]
        (data : BTree α)(mk : ℍ)(val_fun : α -> Bool)
        : Local_valid data mk val_fun ↔ local_valid (data , mk) val_fun
        := by
 apply Iff.intro
 · intro v_D; simp [local_valid]
   apply And.intro
   · exact v_D.MkTree
   · apply And.intro
     · exact v_D.ValidElems
     · exact v_D.NoDup
 · intro valid; simp [local_valid] at valid
   exact { MkTree := valid.1
         , ValidElems := valid.2.1
         , NoDup := (valid.2).2
         }

inductive P2_Actions (α ℍ : Type)  : Type
  where
   | DAC (str : ABTree Unit ((ℍ × ℍ × ℍ) -> Option ChooserMoves))
   | Invalid {n : Nat} (p : α) (seq : ISkeleton n) (str : Sequence n ((ℍ × ℍ × ℍ) -> Option ChooserSmp))
   | Duplicate (n m : Nat)
      -- There are two paths
      (path_p : ISkeleton n) (path_q : ISkeleton m)
      -- Strategies to force proposer to show elements.
      (str_p : Sequence n ((ℍ × ℍ × ℍ) -> Option ChooserSmp))
      (str_q : Sequence m ((ℍ × ℍ × ℍ) -> Option ChooserSmp))
   | Ok

-- Simple linear protocol, no time. Assuming no player play to lose.
-- If chooser wins, the proposed block is discarded. This is not how the real
-- world behaves.
@[simp]
def inner_l2_actions {α ℍ : Type}
  [BEq α] -- Checking dup
  [BEq ℍ][o : Hash α ℍ][HashMagma ℍ]
   (val_fun : α -> Bool)
   --
   (playerOne : P1_Actions α ℍ)
   (playerTwo : P2_Actions α ℍ)
   --
   : Bool
   := match playerTwo with
         | .DAC ch_str =>
            -- Challenging Sequencer (Merkle tree is not correct)
            match data_challenge_game
                ⟨ playerOne.da.fst.map o.mhash , playerOne.da.snd ⟩
                playerOne.dac_str ch_str with
            | .Proposer => true
            | .Chooser => false
         | .Ok => true
         | .Invalid _e ph str =>
            -- Merkle tree is correct, but there is an invalid element in it.
            -- Path is valid. I think in Arb is just the position. (0 <= pos < n)? play : invalid.
            match playerOne.da.fst.iaccess ph with
            | .some (.inl _) =>
                -- we can check element e validity if we wanna.
                match elem_in_backward_rev
                         ph -- Path provided by the player 2
                         playerOne.da.snd -- Consented hash (provided by the player 1)
                         -- Strategies.
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
         | .Duplicate _lp _lq path_p path_q str_p str_q =>
            -- Simbolic game (executed when needed)
            have res :=
                match elem_in_backward_rev
                         path_p
                         playerOne.da.snd -- Consented hash (provided by the player 1)
                         -- Strategies.
                         (playerOne.gen_elem_str path_p)
                         str_p
                      , elem_in_backward_rev
                         path_q
                         playerOne.da.snd -- Consented hash (provided by the player 1)
                         -- Strategies.
                         (playerOne.gen_elem_str path_q)
                         str_q with
                 | (.Proposer, .some v_1) , (.Proposer , .some v_2) => v_1 != v_2
                 | (.Proposer, .none) , _ => true -- Chooser lost |path_p| challenge
                 | (.Proposer, _) , (.Proposer, .none) => true -- Chooser lost |path_q| challenge
                 -- Chooser wins. I write all cases to be sure I am not missing anything.
                 | (.Chooser , _ ) , _ => false
                 | _ , (.Chooser , _ ) => false
            -- L1 checks paths are diff and trigger two elem in and check they differ.
            if path_p.1 == path_q.1
            then true
            else res


def linear_l2_protocol{α ℍ : Type}
  [BEq α] -- Checking dup
  [BEq ℍ][o : Hash α ℍ][HashMagma ℍ]
   (val_fun : α -> Bool)
   --
   (playerOne : P1_Actions α ℍ)
   (playerTwo : (BTree α × ℍ) -> P2_Actions α ℍ)
   --
   : Bool
   := inner_l2_actions val_fun playerOne (playerTwo playerOne.da)

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
  [DecidableEq α]
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
      | .none =>
      -- Check for dups.
        match find_dups (·.snd) public_data.toPaths_elems with
        | .none => .Ok
        | .some (_pred, e_1, _mid, e_2, _succs) =>
          .Duplicate
            e_1.1.length e_2.1.length ⟨ e_1.1 , rfl ⟩ ⟨ e_2.1 , rfl ⟩
            -- Since we are playing the linear game. this is okay
            -- TODO check backward/forward compatibility.
            naive_lin_forward
            naive_lin_forward
      -- return where the invalid element is
      | .some ph =>
        .Invalid
           ph.src
           (ph.pathInfo.map (fun p => p.side) )
           -- From top to element.
           naive_lin_forward
           -- Naive Strategy. (We will need more info for the logarithmic game.)
 -- challenge merkle tree with strategy
 else .DAC ((public_data.hash_SubTree).map (fun _ => ()) gen_chooser_opt')

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
  = ABTree.getI' o.mhash (fun x => m.comb x.1 x.2) b.hash_SubTree
 := by induction b with
   | leaf v => simp [ABTree.hash_SubTree, ABTree.getI']
   | node _ bl br HL HR =>
     unfold ABTree.hash_SubTree
     simp [ABTree.getI']; congr

lemma honest_chooser_wins {α ℍ : Type}
   [BEq ℍ][LawfulBEq ℍ][o : Hash α ℍ] [m : HashMagma ℍ]
   (da : BTree α)
    : winning_condition_player (fun hc a h ↦ dac_leaf_winning_condition hc a h = true)
        (fun _x x res ↦ dac_node_winning_condition res x.1 x.2 = true) (fun _x ↦ id)
        { data := ABTree.map o.mhash id da, res := ABTree.fold o.mhash (fun _x ↦ m.comb) da }
        (ABTree.map some .some da.hash_SubTree)
    := by
    induction da with
    | leaf v =>
      simp
      simp [ABTree.hash_SubTree, winning_condition_player, dac_leaf_winning_condition]
    | node _ bl br HL HR =>
      simp [ABTree.hash_SubTree, winning_condition_player]
      simp at *
      apply And.intro
      · simp [dac_node_winning_condition]
        rw [<- ABTree.hash_SubTree]
        rw [<- fold_getI_hash, <- fold_getI_hash]
      · apply And.intro; all_goals {
              rw [<- ABTree.hash_SubTree]
              rw [<- fold_getI_hash]
              assumption
        }

lemma honest_chooser_accepts_valid {α ℍ : Type}
   [DecidableEq α]
   [BEq ℍ][LawfulBEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
   (val_fun : α -> Bool)
   (data : BTree α)( mk : ℍ )
   ( da_valid : Local_valid data mk val_fun)
   : honest_chooser val_fun data mk = .Ok
   := by
   simp [honest_chooser]
   -- its valid so hashes matches.
   have Hmatch := da_valid.MkTree; simp [BTree.hash_BTree] at Hmatch
   rw [Hmatch]; simp
   -- its valid so all elements should be valid
   have none := @find_valid_nothing _ _ o m val_fun data da_valid.ValidElems
   rw [none]
   simp
   -- its valid so no dups.
   have elnodups := da_valid.NoDup
   rw [<- toPath_elems] at elnodups
   have nodups := no_dups_finds_none (·.snd) data.toPaths_elems elnodups
   rw [nodups]

theorem honest_chooser_valid {α ℍ}
   [BEq ℍ][LawfulBEq ℍ][DecidableEq α]
   [o : Hash α ℍ][m : HashMagma ℍ][InjectiveHash α ℍ][InjectiveMagma ℍ]
   (val_fun : α -> Bool)
   (p1 : P1_Actions α ℍ)
   : linear_l2_protocol val_fun p1 ( fun (t, mt) => honest_chooser val_fun t mt)
     ↔ local_valid p1.da val_fun
   := by
   apply Iff.intro
   · have ⟨ da , dac_str, gen_elem_str ⟩ := p1
     unfold linear_l2_protocol
     simp [honest_chooser]
     unfold local_valid
     cases Hm : (da.2 == ABTree.fold o.mhash (fun x ↦ m.comb) da.1)
     case true =>
       simp
       cases Hval : @find_left_invalid_path α ℍ _ _ val_fun da.1 with
       | none =>
         simp at *
         -- Find dups!
         cases Hdups : find_dups (·.snd) da.1.toPaths_elems with
         | none =>
            simp
            apply And.intro
            · symm; assumption
            · apply @find_nothing_is_valid α ℍ o m val_fun at Hval
              apply And.intro
              · assumption
              · apply finds_no_dup at Hdups
                rw [toPath_elems] at Hdups
                assumption
         | some witness =>
           have ( pred, e_1, mid, e_2, succs ) := witness
           -- Here is where all the magic happens.
           have ⟨ Hpath_1, Hpath_2, neq_paths , same_elems⟩ := finds_dups_law_elem_sk da.1 _ _ Hdups
           -- finds_dups is programmed/verified to do exactly what we want.
           rw [access_iaccess] at Hpath_1; simp [sequence_lift] at Hpath_1
           rw [access_iaccess] at Hpath_2; simp [sequence_lift] at Hpath_2
           simp
           -- We play to win both games.
           have HE_1 := elem_back_rev_honest_two (gen_elem_str (sequence_lift e_1.1 ))
                        (by symm at Hm; exact Hm)
                        Hpath_1
           have HE_2 := elem_back_rev_honest_two (gen_elem_str (sequence_lift e_2.1 ))
                        (by symm at Hm; exact Hm)
                        Hpath_2
           cases HE_1
           -- Proposer wins first game
           case inl x =>
             cases HE_2
             -- and Proposer wins second game
             case inl y =>
               simp [sequence_lift] at y; rw [y]
               simp [sequence_lift] at x; rw [x]
               simp
               rw [same_elems]; simp
               intro ff; contradiction
             -- but quits second game
             case inr y =>
               simp [sequence_lift] at y; rw [y]
               simp [sequence_lift] at x; rw [x]
               simp; intro ff; contradiction
           -- Proposer quits first game
           case inr x =>
             simp [sequence_lift] at x; rw [x]
             simp; intro ff; contradiction
       | some wit =>
         simp at *
         have fres := find_invalid_path_accessed val_fun da.1 wit Hval
         unfold Sequence.map at fres
         rw [fres.1]
         simp
         symm at Hm
         have HEle := @elem_back_rev_honest_two α ℍ _ _ _ _ _ _ _ _
                                                _ -- (wit.pathInfo.map (fun p => p.side))
                                                da.2 wit.src (gen_elem_str (wit.pathInfo.map (fun p => p.side)))
                                                da.1 Hm fres.1
         cases HEle with
         | inl HE =>
           simp [Sequence.map] at HE; rw [HE]; simp
           intro wit_val
           replace fres := fres.2
           rw [fres] at wit_val; simp at wit_val
         | inr HE => simp [Sequence.map] at HE; rw [HE]; simp
     case false =>
       simp
       have w_cho :=
         @dac_winning_gen_chooser α ℍ _ _ _ _
                                  (da.1.map  o.mhash )
                                  -- Rev info
                                  dac_str da.2
                                  -- Chooser Info
                                  (da.fst.hash_SubTree.map .some .some)
                                  (ABTree.fold o.mhash (fun _ => m.comb) da.fst)
       simp [ABTree.hash_SubTree] at w_cho
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
       unfold ABTree.hash_SubTree
       rw [ass]
       simp
   · simp
     have ⟨ da , dac_str , gen_elem_str ⟩ := p1
     simp; intro vDa
     simp [linear_l2_protocol]
     have hcho := honest_chooser_accepts_valid val_fun da.1 da.2 (by rw [struct_and_iff_valid]; simpa)
     rw [hcho]

----------------------------------------
-- ## Stateful Protocol.
-- Now we have a history of all previous accepted batches.

def historical_valid
  {α ℍ : Type} [DecidableEq α][Hash α ℍ][HashMagma ℍ]
  --
  (Hist : List (BTree α × ℍ))
  (val_fun : α -> Bool)
  : Prop
  :=
  -- Each epoch is `local_valid`
  (∀ e ∈ Hist, local_valid e val_fun)
  ∧ -- Plus there are no duplicated elements.
  (List.Nodup (Hist.map (BTree.toList $ ·.fst)).flatten)

inductive P2_History_Actions (α ℍ : Type) : Type where
 | Local (ll : P2_Actions α ℍ) : P2_History_Actions α ℍ
 | DupHistory_Actions
      -- Here is an element in epoch
      (epoch : Nat) -- This is depentent on the history.
      ( n : Nat )(path_p: ISkeleton n) (str_p : Sequence n ((ℍ × ℍ × ℍ) -> Option ChooserSmp))
      --
      (m : Nat)(path_q: ISkeleton m)(str_q : Sequence m ((ℍ × ℍ × ℍ) -> Option ChooserSmp))
      : P2_History_Actions α ℍ

structure P1_History_Actions (α ℍ : Type) : Type where
 local_str : P1_Actions α ℍ
 global_str : List (BTree α × ℍ)  -> {n : Nat} -> ISkeleton n -> (Sequence n (Option (ℍ × ℍ)) × Option α)

def find_first_dup_in_history
   {α ℍ : Type}[DecidableEq α]
   -- We have a list of elements in a tree
   (elems : List (Skeleton × α))
   --
   (hist : List (BTree α × ℍ))
   --
   : Option ( (List (BTree α × ℍ) × (BTree α × ℍ) × List (BTree α × ℍ))
            ×
            (  (List (Skeleton × α) × (Skeleton × α) × List (Skeleton × α))
             × (List (Skeleton × α) × (Skeleton × α) × List (Skeleton × α))
            ))
   := split_at_first_pred
      (fun (e : (BTree α × ℍ)) => find_intersect (·.snd) e.fst.toPaths_elems elems) hist

def historical_honest_algorith {α ℍ : Type}
  [DecidableEq α]
  [BEq ℍ][Hash α ℍ][m : HashMagma ℍ]
  --
  (val_fun : α -> Bool)
  --
  (history : List (BTree α × ℍ))
  --
  (public_data : BTree α)
  (da_mtree : ℍ)
  --
  : P2_History_Actions α ℍ
  := match find_first_dup_in_history public_data.toPaths_elems history with
    | .some ((pred, _e , _) , ( (_, e1, _) , (_ , e2 , _)) ) =>
      .DupHistory_Actions pred.length.succ
          -- Same as before, we need to choose strategies before playing,
          -- depending on which arbitration games we are playing.
          -- Naive lin forward does not need extra info, but logarithmic
          -- requires more.
          e1.fst.length ⟨ e1.fst , rfl ⟩ naive_lin_forward
          e2.fst.length ⟨ e2.fst , rfl ⟩ naive_lin_forward
    | .none => .Local $ honest_chooser val_fun public_data da_mtree

-- This is the step in our blockchain evolution.
--
def linear_l2_historical_protocol{α ℍ : Type}
  [BEq α] -- Checking dup
  [BEq ℍ][o : Hash α ℍ][HashMagma ℍ]
   (val_fun : α -> Bool)
   (hist : List (BTree α × ℍ))
   --
   (playerOne : P1_History_Actions α ℍ)
   (playerTwo : List (BTree α × ℍ) -> (BTree α × ℍ) -> P2_History_Actions α ℍ)
   --
   : Bool
   := match playerTwo hist playerOne.local_str.da with
   | .DupHistory_Actions
       epoch _fpLen fpSkl fpStr _spLen spSkl spStr
       => match hist[epoch]? with
       -- Get epoch from history
       | .none => true -- Wins POne
       | .some p =>
         -- We play two consecutive membership games
         match elem_in_backward_rev
                  fpSkl
                  p.snd
                  -- Strategies
                  (playerOne.global_str hist fpSkl)  -- Missing Player One Strategy
                  fpStr
             , elem_in_backward_rev
                  spSkl
                  playerOne.local_str.da.snd -- Current Da
                  -- Strategies
                  (playerOne.local_str.gen_elem_str spSkl)
                  spStr
             with
          -- Both games reach values
          | (.Proposer, .some v1) , (.Proposer, .some v2) => v1 != v2
          -- Proposer wins
          | (.Proposer, .none) , _ => true
          | _ , (.Proposer, .none) => true
          -- Chooser wins
          | (.Chooser , _ ) , _ => false
          | _ , (.Chooser, _)   => false

   | .Local act => inner_l2_actions val_fun playerOne.local_str act

-- Historical Honest Valid
theorem history_honest_chooser_valid {α ℍ}
   [BEq ℍ][LawfulBEq ℍ][DecidableEq α]
   [o : Hash α ℍ][m : HashMagma ℍ][InjectiveHash α ℍ][InjectiveMagma ℍ]
   (val_fun : α -> Bool)
   (p1 : P1_History_Actions α ℍ)
   --
   (hist : List (BTree α × ℍ))
   (hist_valid : historical_valid hist val_fun)
   --
   : linear_l2_historical_protocol val_fun hist p1
        ( fun h (t, mt) => historical_honest_algorith val_fun h t mt)
     ↔ historical_valid (hist ++ [p1.local_str.da]) val_fun
   := sorry

----------------------------------------
