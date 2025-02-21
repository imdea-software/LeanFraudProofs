import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.Sequence

-- Library to go from sequences to trees.
--
@[simp]
def isEven (n : Nat) : Bool := 2*(n/2) == n

theorem isEvenProof (n : Nat) (p : isEven n) : n = n/2 + n/2
  := by simp [isEven] at p
        omega

theorem isOddProof (n : Nat) (p : ¬ isEven n) : n = n/2 + n/2 + 1
 := by simp [isEven] at p
       omega

def emptyLeaf {α β : Type} : ABTree (Option α) β := .leaf none
def single {α : Type}( a : α ) : ABTree (Option α) α := .node a emptyLeaf emptyLeaf

def infixSeq {α : Type} (t : ABTree α α) : Sequence t.size α
  := match t with
        | .leaf v => .single v
        | .node a bl br =>
          sequence_coerce (by simp; omega)
          $ (infixSeq bl).append (.cons a (infixSeq br) )

def seqHABTree {α : Type}{ n : Nat }(seq : Sequence n α) : ABTree (Option α) α
  := match n with
     | .zero => .leaf none
     | .succ .zero => .leaf $ seq.head
     | .succ (.succ ppn) =>
        -- n == ppn.succ.succ
        let hn := ppn / 2
        -- hn + 1 = n / 2
        let lh := .take hn.succ (by omega) seq
        let nd := (seq.drop hn.succ).head' (by omega)
        let rh := .drop hn.succ.succ seq
        .node nd (seqHABTree lh) (seqHABTree rh)

def perfectSeq {α : Type}{n : Nat} (seq : Sequence ((2^n.succ) - 1) α)
  : ABTree α α
  := match n with
     | .zero =>
       .leaf seq.head
     | .succ _ =>
       have (seql , ar , seqr) := seq.perfect_split
       .node ar (perfectSeq seql) (perfectSeq seqr)

-- Size computing. Size of a perfect |seq| is the length of the seq.
lemma perfect_tree_size {α : Type}{n : Nat}(seq : Sequence ((2^n.succ) - 1) α):
    (perfectSeq seq).size = (2^n.succ) - 1
    :=  by induction n
           case zero => simp [perfectSeq]
           case succ pn HInd =>
             simp [perfectSeq]
             have ihL := HInd seq.perfect_split.1
             have ihR := HInd seq.perfect_split.2.2
             simp at ihL; simp at ihR
             rw [ihL,ihR]
             have ps := @pow_geq_one pn
             omega

theorem seq_tree_seq {α : Type}{n : Nat}(seq : Sequence ((2^n.succ) - 1) α):
  infixSeq (perfectSeq seq) = sequence_coerce (by rw [perfect_tree_size]) seq
  := by induction n
        -- Zero
        case zero =>
          simp [perfectSeq, infixSeq, Sequence.single]
          apply rfl_coerce
          have ⟨ ls , ln ⟩ := seq
          simp at *
          match ls with
            | .nil => simp at ln
            | .cons x _ => simp; simp at ln; assumption
        -- Succ
        case succ pn HInd =>
          simp [perfectSeq, infixSeq]
          have hL := HInd seq.perfect_split.1
          rw [hL]
          have hR := HInd seq.perfect_split.2.2
          rw [hR]
          simp
          apply rfl_coerce
          rw [<- rfl_coerce_up]
          rw [<- rfl_coerce_up]
          rw [<- rfl_coerce_up]
          simp [Sequence.perfect_split, Sequence.split, Sequence.tail]
          rw [<- rfl_coerce_up]
          have list_lm : (seq.1)[2 ^ (pn + 1) - 1]'(by rw [seq.2];sorry) :: (List.drop (2 ^ (pn + 1) - 1) seq.1).tail = List.drop (2 ^ (pn + 1) - 1) seq.1 := sorry
          rw [list_lm]
          rw [List.take_append_drop]

def gen_empty_perfect_tree : Nat -> ABTree Unit Unit
  | .zero => .leaf ()
  | .succ pn => .node () (gen_empty_perfect_tree pn) (gen_empty_perfect_tree pn)

def gen_info_perfect_tree {α β : Type}{h : Nat}
  (nodes : Sequence (2^h - 1) β)
  (leaves : Sequence (2^h) α)
  : ABTree α β
  := match h with
    | .zero => .leaf $ leaves.head
    | .succ _ =>
     have (ll , lr) := half_split_pow leaves
     have (ln , m, rn) := nodes.perfect_split
     .node m
     (gen_info_perfect_tree ln ll)
     (gen_info_perfect_tree rn lr)

lemma half_split_rev {α : Type}{lgn : Nat}
      (s : Sequence (2^lgn.succ) α)
      : half_split_pow s.reverse
      = ((half_split_pow s).2.reverse , (half_split_pow s).1.reverse)
      := sorry
 -- unfold half_split_pow
 -- unfold Sequence.reverse
 -- simp
 -- apply And.intro
 -- · apply funext
 --   intro x
 --   unfold Fin.rev
 --   simp
 --   congr
 --   omega
 -- · apply funext
 --   intro x
 --   have ⟨ xi , xLt ⟩ := x
 --   simp
 --   unfold Fin.rev
 --   simp
 --   have sameI : 2^(lgn + 1) - (2^lgn + xi + 1) = 2 ^ lgn - (xi + 1) := by omega
 --   congr

lemma half_perfect_split_same {α : Type} {n : Nat}
      ( s : Sequence (2^n.succ) α )
      : (sequence_coerce ( by have pNZ := @pow_gt_zero n; omega) (half_split_pow s).1).init
      =  (@sequence_coerce _ _ (2^n.succ -1 +1) ( by have pNZ := @pow_gt_zero n.succ; omega) s).init.perfect_split.1
      := sorry
      -- apply funext
      -- intro x
      -- simp [seqPerfectSplit, splitSeq, Fin.init]
      -- simp [half_split_pow]

lemma half_zip_with {α β ε : Type}{lgn : Nat}
    {f : α -> β -> ε}
    {sl : Sequence (2^lgn.succ) α}
    {sr : Sequence (2^lgn.succ) β}
    : (half_split_pow (sl.zip_with f sr)).1
    = (half_split_pow sl).1.zip_with f (half_split_pow sr).1
    := sorry
      -- apply funext
      -- intro x
      -- simp [half_split_pow]

lemma half_split_map_left {α β : Type}{lgn : Nat}
    {f : α -> β}
    ( s : Sequence (2^lgn.succ) α)
    : (half_split_pow (s.map f)).1
    = (half_split_pow s).1.map f
 := sorry
 -- by unfold half_split_pow;simp;unfold takeN
 --       apply funext
 --       intro x; simp

lemma perfect_split_constant { α : Type }{lgn : Nat}
  (a : α)
  -- (s : Sequence (2^lgn - 1) α)
  : @Sequence.constant _ (2^lgn - 1) a
  = (Sequence.constant a).perfect_split.1
  := sorry -- by apply funext; intro x; simp [seqPerfectSplit, splitSeq]

lemma gen_empty_size {n : Nat}
  : (gen_empty_perfect_tree n).size = 2^n.succ - 1
  := by
        induction n with
        | zero => simp [gen_empty_perfect_tree]
        | succ pn HInd =>
          simp [gen_empty_perfect_tree]
          simp at HInd
          rw [HInd]
          have pw_prop := @pow_gt_zero pn
          omega
