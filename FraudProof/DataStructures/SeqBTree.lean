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

def seqPerfectSplit {α : Type}{n : Nat}(seq : Sequence ((2^n.succ) - 1) α)
  : ( Sequence ((2^n) - 1) α × α × Sequence ((2^n) - 1) α)
  := have ( seql , hdseqr ) := splitSeq seq ((2^n) - 1) (by simp; omega)
    ( seql
    , hdseqr ⟨ 0 , by simp;have ps :=@pow_geq_one n; omega ⟩
    , Fin.tail (sequence_coerce (by rw [pp2]; have ps :=@pow_geq_one n; omega) hdseqr))


def concat_perfect_split {α : Type}[BEq α]{n : Nat}(seq : Sequence ((2^n.succ) - 1) α)
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

def perfectSeq {α : Type}{n : Nat} (seq : Sequence ((2^n.succ) - 1) α) : ABTree α α
  := match n with
     | .zero =>
       .leaf ( seq ⟨ 0 , by simp ⟩)
     | .succ pn =>
       have (seql , ar , seqr) := seqPerfectSplit seq
       .node ar (perfectSeq seql) (perfectSeq seqr)

--
lemma perfect_tree_size {α : Type}{n : Nat}(seq : Sequence ((2^n.succ) - 1) α):
    (perfectSeq seq).size = (2^n.succ) - 1
    :=  by induction n
           case zero => simp
           case succ pn HInd =>
             simp
             have hl := HInd (takeN (2^ pn.succ -1) (by omega) seq)
             simp at hl
             rw [hl]
             have hr := HInd (Fin.tail (sequence_coerce (by simp; have ps := @pow_geq_one pn; omega) (dropN (2 ^ (pn + 1) - 1) (by omega) seq)))
             simp at hr; rw [hr]
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
          have hL := HInd (takeN (2 ^ (pn + 1) - 1) (by omega) seq)
          rw [hL]
          have hR := HInd (Fin.tail (sequence_coerce (by simp; have ps := @pow_geq_one pn; omega) (dropN (2 ^ (pn + 1) - 1) (by omega) seq)))
          rw [hR]
          simp
          rw [ConsCoerce]
          rw [ConsMid]
          rw [TransCoerce]
          rw [ConcatCoerce]
          rw [TransCoerce]
          rw [ConcatSplit]
          rw [TransCoerce]
          simp
