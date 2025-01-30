import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.Sequence


def pairTreesE {α : Type}{n m : Nat}(seq : Sequence m (BTree α))(_eve : m = n + n): Sequence n (BTree α)
  := match n with
     | .zero => nilSeq
     | .succ _pn =>
       let h1 := seq ⟨ 0 , by omega ⟩
       let h2 := seq ⟨ 1 , by omega ⟩
       let rs := dropN 2 (by omega) seq
       Fin.cons (.node h1 h2) (pairTreesE rs (by omega))

def pairTreesO {α : Type} {n m : Nat}(seq : Sequence m (BTree α))(_odd : m = n+n+1) : Sequence (n+1) (BTree α)
  := Fin.snoc (pairTreesE (takeN (2*n) (by omega) seq) (by omega)) (lastSeq' seq (by assumption))

--
@[simp]
def isEven (n : Nat) : Bool := 2*(n/2) == n

theorem isEvenProof (n : Nat) (p : isEven n) : n = n/2 + n/2
  := by simp [isEven] at p
        omega

theorem isOddProof (n : Nat) (p : ¬ isEven n) : n = n/2 + n/2 + 1
 := by simp [isEven] at p
       omega
--

-- Get Tree out of Sequence!
def pairTree {α : Type}{n : Nat}(seq : Sequence n (BTree α))(_pos : n > 0) : BTree α
  := match HN : n with
     | .zero => by simp at _pos
     -- If n = 1
     | .succ .zero => seq ⟨ 0 , by simp ⟩
     -- else
     | .succ (.succ ppn) =>
        if H : isEven n
            then pairTree (@pairTreesE _ (n/2) ppn.succ.succ seq (by simp at H;omega)) (by rw [HN]; simp at H; omega)
            else pairTree (@pairTreesO _ (n/2) ppn.succ.succ seq (by simp at H;omega)) (by omega)
   termination_by n
   decreasing_by
     · {simp_wf; rw [HN]; omega}
     · { simp_wf
         rw [HN]
         simp at H
         rw [HN] at H
         simp at H
         omega
     }
-- TODO Show it is balanced and stuff!


def emptyLeaf {α β : Type} : ABTree (Option α) β := .leaf none
def single {α : Type}( a : α ) : ABTree (Option α) α := .node a emptyLeaf emptyLeaf

def infixSeq {α : Type} (t : ABTree α α) : Sequence t.size α
  := match t with
        | .leaf v => singleSeq v
        | .node a bl br =>
          -- concatSeq (sequence_coerce (by simp; omega ) (Fin.snoc (infixSeq bl) a)  ) (infixSeq br)
          -- Editted to follow other lemmas (proved in the future hehe)
          sequence_coerce (by simp; omega) <|
          concatSeq (infixSeq bl)
                    (Fin.cons a (infixSeq br) )


def maybeSizeTree {α β : Type} : ABTree (Option α) β -> Nat
  := ABTree.sizeI  (fun x => match x with | none => 0 | some _ => 1) (fun _ => 1)

def seqHABTree {α : Type}{ n : Nat }(seq : Sequence n α) : ABTree (Option α) α
  := match n with
     | .zero => .leaf none
     | .succ .zero => .leaf $ seq ⟨ 0 , by simp ⟩
     | .succ (.succ ppn) =>
        -- n == ppn.succ.succ
        let hn := ppn / 2
        -- hn + 1 = n / 2
        let lh := takeN hn.succ (by omega) seq
        let nd := headSeq' (dropN hn.succ (by omega) seq) (by omega)
        let rh := dropN hn.succ.succ (by omega) seq
        --
        .node nd (seqHABTree lh) (seqHABTree rh)

-- Can we prove that we get the same sequence modulo padding?
-- theorem isoSeqTree ... : polyLenSeqEq (filter none infixSeq (seqHABTree seq)) seq
--

lemma pp2 { n : Nat } : 2^(n.succ) = 2^n + 2^n
  := by omega

lemma gt0Add ( m n : Nat)(hm : 0 < m )( hn : 0 ≤ n ) : 0 < m + n
  := by omega

lemma geq0Add ( m n : Nat)(hm : 0 ≤ m )( hn : 0 ≤ n ) : 0 ≤ m + n
  := by omega

lemma pow_gt_zero {m : Nat} : 0 < 2^m
  := match m with
     | .zero => by simp
     | .succ pn => by rw [Nat.pow_succ]; simp; apply pow_gt_zero

lemma pow_geq_one {m : Nat} : 1 ≤ 2^m
 := by induction m with
    | zero => simp
    | succ pm HM => omega

lemma ppGT {n : Nat} : 0 < 2 ^ n + 2 ^ n + (2 ^ n + 2 ^ n) - 1 - (2 ^ n + 2 ^ n - 1)
:= by have ps := @pow_geq_one n; omega

lemma eqPP {n : Nat} : 2 ^ (n + 1) + 2 ^ (n + 1) - 1 - (2 ^ (n + 1) - 1) = 2 ^ (n + 1) - 1 + 1
  := by have ps := @pow_geq_one n.succ; omega


def half_split {α : Type}{n : Nat}(seq : Sequence (2*n) α)
  : Sequence n α × Sequence n α
  := (takeN n (by omega) seq
  , sequence_coerce (by omega) $ dropN n (by omega) seq)

def half_split_pow {α : Type}{n : Nat}(seq : Sequence (2^n.succ) α)
  : Sequence (2^n) α × Sequence (2^n) α
  := (takeN (2^n) (by have pg := @pow_gt_zero n; omega) seq
  , sequence_coerce (by have pg := @pow_gt_zero n;omega)
  $ dropN (2^n) (by have pg := @pow_gt_zero n;omega) seq)

def join_seq_tree {α : Type}{n : Nat}
  (f : α -> α -> α)
  (seq : Sequence (2*n) α)
  : Sequence n α
  := match n with
    | .zero => nilSeq
    | .succ n =>
      Fin.cons (f (seq ⟨ 0 , by simp ⟩) (seq ⟨ 1 , by omega⟩))
      $ join_seq_tree f (Fin.tail $ Fin.tail seq)

def consume_seq {α : Type}{lgn : Nat}
  (f : α -> α -> α)
  (seq : Sequence (2^lgn) α)
  : α
  := match lgn with
    | .zero => headSeq seq
    | .succ plgn => consume_seq f
      $ join_seq_tree f
      $ @sequence_coerce _ _ (2 * 2^plgn)
        (by simp; rw [Nat.pow_add]; simp;omega) seq

-- lemma consume_tree_height {α β: Type}{lgn : Nat}
--       (seq : Sequence (2^lgn) (ABTree α β))
--       (topH : Nat)
--       (sameH : forall (i : Nat)(iLT : i < (2^lgn)), (seq ⟨ i , iLT⟩).height = topH  )
--       : (consume_seq .node seq).height = lgn
--       := _

def seqPerfectSplit {α : Type}{n : Nat}(seq : Sequence ((2^n.succ) - 1) α)
  : ( Sequence ((2^n) - 1) α × α × Sequence ((2^n) - 1) α)
  := have ( seql , hdseqr ) := splitSeq seq ((2^n) - 1) (by simp; omega)
    ( seql
    , hdseqr ⟨ 0 , by simp;have ps :=@pow_geq_one n; omega ⟩
    , Fin.tail (sequence_coerce (by rw [pp2]; have ps :=@pow_geq_one n; omega) hdseqr))


def concat_perfect_split {α : Type}{n : Nat}(seq : Sequence ((2^n.succ) - 1) α)
  : let ⟨ seql, m , seqr ⟩ := seqPerfectSplit seq
  seq = sequence_coerce
        (by simp; rw [pp2]; have ps := @pow_geq_one n.succ; omega )
        (concatSeq seql ( Fin.cons m seqr ))
  := by simp [seqPerfectSplit]
        -- Fin.cons ( s⟨0, _ ⟩ ) (Fin.tail seq_coerce s)
        rw [ConsTailSeqCoerce]
        -- concatSeq (split seq 1) (seq_coerce seq 2)
        simp [splitSeq]
        rw [ConcatSplitCoerce]
        --
        apply funext; rw [ Fin.forall_iff ]
        intros i iLT
        simp [sequence_coerce]

def perfectSeq {α : Type}{n : Nat} (seq : Sequence ((2^n.succ) - 1) α)
  : ABTree α α
  := match n with
     | .zero =>
       .leaf ( seq ⟨ 0 , by simp ⟩)
     | .succ pn =>
       have (seql , ar , seqr) := seqPerfectSplit seq
       .node ar (perfectSeq seql) (perfectSeq seqr)

-- Size computing. Size of a perfect |seq| is the length of the seq.
lemma perfect_tree_size {α : Type}{n : Nat}(seq : Sequence ((2^n.succ) - 1) α):
    (perfectSeq seq).size = (2^n.succ) - 1
    :=  by induction n
           case zero => simp [perfectSeq]
           case succ pn HInd =>
             simp [perfectSeq]
             have ihL := HInd (seqPerfectSplit seq).1
             have ihR := HInd (seqPerfectSplit seq).2.2
             simp at ihL; simp at ihR
             rw [ihL,ihR]
             have ps := @pow_geq_one pn
             omega

theorem seq_tree_seq {α : Type}{n : Nat}(seq : Sequence ((2^n.succ) - 1) α):
  infixSeq (perfectSeq seq) = sequence_coerce (by rw [perfect_tree_size]) seq
  := by induction n
        case zero =>
          simp [perfectSeq, infixSeq, singleSeq]
          apply funext
          simp
          intro x
          -- simp [sequence_coerce]
          replace ⟨ x , xLt ⟩ := x
          match x with
          | .zero => simp
          | .succ px => simp at xLt

        case succ pn HInd =>
          simp [perfectSeq, infixSeq]
          have hL := HInd (seqPerfectSplit seq).1
          rw [hL]
          have hR := HInd (seqPerfectSplit seq).2.2
          rw [hR]
          simp
          rw [ConsCoerce,ConcatCoerce, TransCoerce]
          apply coerce_eq_comm
          rw [TransCoerce]
          have seq_split := concat_perfect_split seq; simp at seq_split
          rw [Eq.comm]
          assumption
          -- Proof Obligations
          have psize := perfect_tree_size seq; simp [perfectSeq] at psize
          assumption

def gen_empty_perfect_tree : Nat -> ABTree Unit Unit
  | .zero => .leaf ()
  | .succ pn => .node () (gen_empty_perfect_tree pn) (gen_empty_perfect_tree pn)

def gen_info_perfect_tree {α β : Type}{h : Nat}
  (nodes : Sequence (2^h - 1) β)
  (leaves : Sequence (2^h) α)
  : ABTree α β
  := match h with
    | .zero => .leaf $ headSeq leaves
    | .succ _ =>
     have (ll , lr) := half_split_pow leaves
     have (ln , m, rn) := seqPerfectSplit nodes
     .node m
     (gen_info_perfect_tree ln ll)
     (gen_info_perfect_tree rn lr)

-- lemma half_pefect_split_same {α : Type} {n : Nat}
--       ( s : Sequence (2^n.succ) α )
--       : -- have init : Sequence (2^n.succ - 1) :=
--        have ⟨ left, mid, _ ⟩ : Sequence (2^n - 1) α × α × _ := (seqPerfectSplit $ Fin.init $ @sequence_coerce _ _ (2^n.succ - 1 + 1) sorry s)
--        (half_split_pow s).1
--       = sequence_coerce sorry (Fin.snoc left mid)
--       := sorry

lemma half_perfect_split_same {α : Type} {n : Nat}
      ( s : Sequence (2^n.succ) α )
      : Fin.init (sequence_coerce ( by have pNZ := @pow_gt_zero n; omega) (half_split_pow s).1)
      = (seqPerfectSplit ( Fin.init (@sequence_coerce _ _ (2^n.succ -1 +1) ( by have pNZ := @pow_gt_zero n.succ; omega) s))).1
      := by
      apply funext
      intro x
      simp [seqPerfectSplit, splitSeq, Fin.init]
      simp [half_split_pow]

lemma half_zip_with {α β ε : Type}{lgn : Nat}
    {f : α -> β -> ε}
    {sl : Sequence (2^lgn.succ) α}
    {sr : Sequence (2^lgn.succ) β}
    : (half_split_pow (seq_zip_with f sl sr)).1
    = seq_zip_with f (half_split_pow sl).1 (half_split_pow sr).1
    := by
      apply funext
      intro x
      simp [half_split_pow]


lemma perfect_split_constant { α : Type }{lgn : Nat}
  (a : α)
  -- (s : Sequence (2^lgn - 1) α)
  : @seq_constant _ (2^lgn - 1) a
  = (seqPerfectSplit (seq_constant a)).1
  := by apply funext; intro x; simp [seqPerfectSplit, splitSeq]

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
