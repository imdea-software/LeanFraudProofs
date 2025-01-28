import Mathlib.Data.Fin.Tuple.Basic -- Fin.tail

-- import Mathlib.Data.Nat
import Init.PropLemmas
import Mathlib.Data.List.FinRange

----------------------------------------
-- * Sequences

-- Sequence of |n| elements
abbrev Sequence (n : Nat) (α : Type) := Fin n -> α

@[simp]
def seq_constant {α : Type} {n : Nat}(a : α) : Sequence n α
 := fun _ => a

@[simp]
def polyLenSeqEq {α : Type}[BEq α]{n m : Nat}(p : Sequence n α)(q : Sequence m α) : Bool
  := match n , m with
     | .zero , .zero => true
     | .succ _pn, .succ _mn =>
       if p 0 == q 0
       then polyLenSeqEq (Fin.tail p) (Fin.tail q)
       else false
     | _ , _ => false

theorem seqEqLawLength {α : Type}[BEq α]{m n : Nat}(p : Sequence n α)(q : Sequence m α)(pEq : polyLenSeqEq p q)
  : n = m
  := by revert p q pEq n
        induction m with
        | zero =>
          intros n p q pEQq
          -- unfold polyLenSeqEq at pEQq
          cases n with
          | zero => rfl
          | succ pn => simp at pEQq
        | succ pm HInd =>
          intros n p q pEQq
          cases n with
          | zero => simp at pEQq
          | succ pn =>
            simp at pEQq
            simp
            have rsEq := pEQq.2
            exact @HInd pn (Fin.tail p) (Fin.tail q) rsEq

theorem seqEqLawRfl {α : Type}[BEq α][LawfulBEq α]{n : Nat}(p : Sequence n α)
  : polyLenSeqEq p p
  := by
   revert p
   induction n with
   | zero => intro _p; simp
   | succ pn HInd =>
      intro p
      simp
      apply HInd

-- Nil Sequence
def nilSeq {γ : Type} : Sequence 0 γ
 := fun x => by have e := x.isLt; simp at e

def singleSeq {α : Type} (a : α) : Sequence 1 α
 := Fin.cons a nilSeq

-- Head
@[simp]
def headSeq {α : Type}{ n : Nat } ( seq : Sequence n.succ α) : α
  := seq ⟨ 0 , by simp ⟩

@[simp]
def headSeq' {α : Type}{ n : Nat } ( seq : Sequence n α)(notZ : 0 < n) : α
 := seq ⟨ 0 , notZ ⟩

-- Last
@[simp]
def lastSeq {α : Type}{n : Nat} (seq : Sequence n.succ α) : α
  := seq $ Fin.last n
@[simp]
def lastSeq' {α : Type}{n m : Nat} (seq : Sequence n α)(ns : n = m + 1) : α
  := seq ⟨ m , by omega ⟩
def lastSeq'' {α : Type}{n : Nat} (seq : Sequence n α)(notZ : 0 < n) : α
  := seq ⟨ n - 1, by omega ⟩


def zip_succ_int {α : Type}{n : Nat}
  (h : α) (seq : Sequence n.succ α) : Sequence n.succ (α × α)
  := match n with
    | .zero => singleSeq $ ( h, headSeq seq )
    | .succ _ =>
      have hd := headSeq seq
      Fin.cons (h, hd) $ zip_succ_int hd (Fin.tail seq)

def zip_succ {α : Type}{n : Nat}
  (seq : Sequence n.succ.succ α) : Sequence n.succ (α × α)
  := zip_succ_int (headSeq seq) (Fin.tail seq)

-- Same as above but using indexes.
def zip_succ' {α : Type}{n : Nat}
  (seq : Sequence n.succ.succ α) : Sequence n.succ (α × α)
  := fun i =>
    match i with
    | .mk i iLtns => ( seq ⟨ i , by omega ⟩ , seq ⟨ i.succ , by omega ⟩ )

@[simp]
def snocSeq {α : Type}{n : Nat}(a : α)(seq : Sequence n α) : Sequence n.succ α
  := fun ⟨ x , _xLT ⟩ => if H : x < n then seq ⟨ x , H ⟩ else a

-- @[simp]
-- def eqLength {α : Type}{n m : Nat}(seq : Sequence n α)(eqP : n = m) : Sequence m α
--  := fun ⟨ x , xLT ⟩ => seq ⟨ x , by omega ⟩

-- R Access
@[simp]
def getI {α : Type}{n: Nat}(seq : Sequence n α)(i : Nat)(iLTn : i < n) : α
 := seq ⟨ i , iLTn ⟩

@[simp]
def tailSeq {α : Type}{n : Nat}: Sequence n.succ α -> Sequence n α
  := Fin.tail

def tailSeq' {α : Type}{n : Nat}(s : Sequence n α) : Sequence n.pred α
 := fun z => match z with
             | .mk i iLT =>
             s ⟨ i.succ , by simp; apply Nat.succ_lt_of_lt_pred; assumption ⟩

@[simp]
def desc_Seq {n : Nat}{α : Type} (seq : Sequence n.succ α) : α × Sequence n α
 := ⟨ headSeq seq , tailSeq seq ⟩

-- Map
@[simp]
def seqMap {α β : Type} {n : Nat} (f : α -> β) ( seq : Sequence n α ) : Sequence n β
  := match n with
     | 0 => nilSeq
     | .succ _pn => Fin.cons (f $ headSeq seq) (seqMap f (Fin.tail seq))

@[simp]
def seq_zip_with {α β ε : Type}{n : Nat}
    (f : α -> β -> ε)
    (sl : Sequence n α)
    (sr : Sequence n β)
    : Sequence n ε
    := match n with
    | .zero => nilSeq
    | .succ _pn => Fin.cons
                   (f (headSeq sl) (headSeq sr))
                   (seq_zip_with f (Fin.tail sl) (Fin.tail sr))

@[simp]
def seq_scanl {α β : Type}{n : Nat}
  (f : α -> β -> α)
  (b : α)
  (seq : Sequence n β) : Sequence n.succ α
  := sorry -- To be defined

-- Replicate
@[simp]
def replicate {α : Type}{n : Nat}(c : α) : Sequence n α
 := fun _ => c

-- Reverse
@[simp]
def sequence_reverse {α : Type} {n : Nat} (seq : Sequence n α) : Sequence n α
  := seq ∘ Fin.rev

theorem Fin.snoc_head {α : Type}{ n : Nat }
   ( seq : Sequence n.succ α )(lt : α)
   : (@Fin.snoc n.succ (fun _ => α) seq lt) ⟨ 0 , by simp ⟩ = seq 0
   := by simp [snoc, castLT]

-- Take
@[simp]
def takeN {α : Type}{n : Nat}(m : Nat)(mLTn : m ≤ n)(s : Sequence n α) : Sequence m α
 := fun ⟨ p , plt ⟩ => s ⟨ p , by omega ⟩

-- Drop
@[simp]
def dropN {α : Type}{n : Nat}(m : Nat)(mLTn : m ≤ n)(s : Sequence n α) : Sequence (n - m) α
 := fun ⟨ p , pLT ⟩ => s ⟨ m + p , by omega ⟩

-- Concat
@[simp]
def concatSeq {α : Type}{n m : Nat}(p : Sequence n α)(q : Sequence m α) : Sequence (n + m) α
 := fun ⟨ x , xLT ⟩ =>
    if H : x < n then p ⟨ x , H ⟩
    else q ⟨ x - n , by omega ⟩

-- SplitAt
def splitSeq {α : Type}{n : Nat}(p : Sequence n α)(m : Nat)(mLTn : m ≤ n): Sequence m α × Sequence (n - m) α
  := ⟨ takeN m mLTn p , dropN m mLTn p ⟩

----------------------------------------

@[simp] -- I have defined it already hehe
def sequence_coerce {α : Type} {n m : Nat}( hEq : n = m )(s : Sequence n α) : Sequence m α
  := fun ix => match ix with
               | ⟨ i , iLt ⟩ => s ⟨ i , by omega ⟩

def beq_sequences {α : Type}[BEq α]{n : Nat} : BEq (Sequence n α) where
  beq sl sr :=
    match n with
   | .zero => true
   | .succ _pn => headSeq sl == headSeq sr
                  && beq_sequences.beq (Fin.tail sl) (Fin.tail sr)

def kyle_sequence_beq {n : Nat}{α : Type} [BEq α] (sl sr : Sequence n α) : Bool :=
  Nat.all n (fun i iLt => sl ⟨ i , iLt ⟩ == sr ⟨ i , iLt ⟩)

-- Here the magic is happening at Decidable α  and the decidable_of_iff.
def kyle_decidable_seq {α : Type} [dec : DecidableEq α](n : Nat) : DecidableEq (Sequence n α)
  := fun sl sr => decidable_of_iff (kyle_sequence_beq sl sr) <| by
                      constructor
                      case mp =>
                        intro h
                        apply funext
                        simpa [kyle_sequence_beq, Nat.all_eq_finRange_all] using h
                        -- intro x
                        -- have xinRange := List.mem_finRange x
                        -- apply h
                      case mpr =>
                        intro heq
                        rw [heq]
                        simp [kyle_sequence_beq, Nat.all_eq_finRange_all]


-- theorem beq_sequence_head {α : Type}[BEq α]{n : Nat}(l r : Sequence n.succ α)(heq : l == r)
--         : l ⟨ 0 , by simp ⟩ == r ⟨ 0 , by simp ⟩
--         := by simp;

-- theorem beq_sequence_ {α : Type}[BEq α]{n : Nat}(l r : Sequence n α)(heq : l == r)
--         : forall (i : Nat), (iLt : i < n) -> l ⟨ i, iLt ⟩ == r ⟨ i , iLt ⟩
--         := by
--         intros i iLt
--         apply funext at heq

-- instance law_full_beq_seq {α : Type}[BEq α][LawfulBEq α]{n : Nat} : LawfulBEq (Sequence n α) where
--   eq_of_beq := by
--     intros a b heq
--     apply funext
--     intro x; replace ⟨ x , xLT ⟩ := x
--     induction x with
--     | zero => _
--     | succ px HPx => _
--   rfl := _

-- structure EqSeq (α : Type)(m n : Nat)(sl : Sequence m α)(sr : Sequence n α) where
--   sameLen : m = n
--   sameVals : sequence_coerce sameLen sl = sr

--
theorem split_seq_eq {α : Type}{n m : Nat}{ mLTn : m ≤ n }( seq : Sequence n α ):
  have ⟨ seql , seqr ⟩ := splitSeq seq m mLTn
  seq = sequence_coerce (by omega) (concatSeq seql seqr)
  -- seq = sequence_coerce (by omega) (concatSeq seql seqr)
  := by
  simp
  apply funext
  rw [ Fin.forall_iff ]
  intros i iLT
  simp [sequence_coerce]
  split
  case h.isTrue h => simp [splitSeq]
  case h.isFalse h =>
    simp [splitSeq]
    congr
    omega

theorem ConsTailSeqCoerce { α : Type }{n m : Nat} { ceq : n = m + 1 }(seq : Sequence n α)
  : Fin.cons ( seq ⟨ 0 , by omega ⟩ ) ( Fin.tail (sequence_coerce ceq seq )) = sequence_coerce ceq seq
  := by
  apply funext
  rw [ Fin.forall_iff ]
  intros i iLT
  repeat simp [sequence_coerce]
  match i with
  | .zero => simp
  | .succ pi => simp [Fin.cons, Fin.tail, sequence_coerce]

theorem ExtraCoerce {α : Type}{n : Nat}(req : n = n)(seq : Sequence n α)
        : seq = sequence_coerce req seq
        := by
        apply funext; rw [ Fin.forall_iff ]
        intros i iLT
        simp [sequence_coerce]

theorem coerce_eq_comm {α : Type}{n m : Nat}
        {heq : n = m}
        (seql : Sequence n α)(seqr : Sequence m α)
        : sequence_coerce heq seql = seqr
        -> seql = sequence_coerce (by rw [Eq.comm] at heq; assumption ) seqr
        := by intro H; rw [ <- H]; apply ExtraCoerce; simp

theorem coerce_eq_comm' {α : Type}{n m : Nat}
        {heq : m = n}
        (seql : Sequence n α)(seqr : Sequence m α)
        : seql = sequence_coerce heq seqr
        -> sequence_coerce (by omega) seql = seqr
        := by intro H; rw [H]; apply ExtraCoerce; simp

theorem coerce_eq_coerce { α : Type }{n m l : Nat}
        {reql : n = l}{reqr : m = l}
        (seql : Sequence n α)(seqr : Sequence m α)
        : sequence_coerce reql seql = sequence_coerce reqr seqr
        -> sequence_coerce (by omega) seql = seqr
        := by intro H; apply coerce_eq_comm' at H
              rw [<- H]
              apply funext; rw [Fin.forall_iff]; intros i iLt
              simp

theorem TransCoerce {α : Type}{n m l : Nat}{fst : n = m}{snd : m = l}
      (seq : Sequence n α):
      sequence_coerce snd (sequence_coerce fst seq)
      = sequence_coerce (by omega) seq
      := by apply funext; intro x; simp

theorem ConsCoerce{α : Type}{n m : Nat}{heq : n = m}(a : α) (seq : Sequence n α):
   Fin.cons a (sequence_coerce heq seq)
   = sequence_coerce (by omega) (Fin.cons a seq)
   := by
   apply funext
   intro x; replace ⟨ x , xLt ⟩ := x
   match x with
   | .zero => simp
   | .succ px => simp [Fin.cons]

theorem TailCoerDrop {α : Type}{n m : Nat}(d : Nat){heq : n - d = m + 1} {dLt : d ≤ n}(seq : Sequence n α):
   Fin.tail (sequence_coerce heq ( dropN d dLt seq ))
   = sequence_coerce (by omega) (dropN d.succ (by omega) seq)
   := by
   apply funext; intro x
   simp [Fin.tail]
   replace ⟨ x , xLt ⟩ := x
   simp
   apply congr_arg
   rw [Fin.mk_eq_mk]
   omega


theorem ConsMid {α : Type}{n m : Nat}(d : Nat){dLt : d < n}{dLeq : d ≤ n}{mheq : n - d = m + 1}
    (seq : Sequence n α):
    Fin.cons (seq ⟨ d, dLt ⟩) (Fin.tail ( sequence_coerce mheq (dropN d dLeq seq) ))
    = sequence_coerce mheq (dropN d dLeq seq)
    := by
    apply funext
    intro x; replace ⟨ x , xLt ⟩ := x
    simp [Fin.cons]
    match x with
    | .zero => simp
    | .succ px => simp [Fin.tail]


theorem ConcatSplitCoerce { α : Type } {n cut m : Nat}{cutLn : cut ≤ n}(ceq : n - cut = m) (seq : Sequence n α):
  have ⟨ fst, snd ⟩ := (splitSeq seq cut cutLn)
  concatSeq fst ( sequence_coerce ceq snd )
  = sequence_coerce (by omega) seq
  := by simp [splitSeq, concatSeq]
        apply funext
        rw [Fin.forall_iff]
        intros i iLT
        simp [sequence_coerce]
        split
        case h.isTrue h => simp
        case h.isFalse h => congr; omega


theorem ConcatCoerce {α : Type}{m n p q: Nat}
   {h : m = p}{j : n = q}
   (sl : Sequence n α)(sr : Sequence m α):
   concatSeq (sequence_coerce j sl) (sequence_coerce h sr)
   = sequence_coerce (by omega) (concatSeq sl sr)
   := by
      apply funext; intro x; simp
      split
      · split
        · simp
        · rw [j] at *; contradiction
      · split
        · rw [j] at *; contradiction
        · congr; rw [j]


theorem ConcatSplit {α : Type}{n d : Nat}{dLt : d ≤ n}
     (seq : Sequence n α):
     concatSeq (takeN d dLt seq) (dropN d dLt seq) = sequence_coerce (by omega) seq
     := by
     apply funext
     intro x
     simp
     split
     · simp
     case h.isFalse h => congr; omega
