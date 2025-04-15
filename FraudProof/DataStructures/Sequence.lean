import Mathlib.Data.Fin.Tuple.Basic -- Fin.tail

-- import Mathlib.Data.Nat
import Init.PropLemmas
import Init.Data.List.TakeDrop
import Mathlib.Data.List.FinRange

----------------------------------------
-- * Sequences
-- Proof Carrying code.
abbrev Sequence (n : Nat) (α : Type) := { t : List α // t.length = n}

def sequence_lift {α : Type}(t : List α) : Sequence t.length α
 := ⟨ t, rfl ⟩

instance seq_b {α : Type}{n : Nat}[BEq α] : BEq (Sequence n α) where
  -- if their list are the same
  beq l r := l.1 == r.1

-- ** Basic API
-- Nil Sequence
@[simp]
def Sequence.nil {γ : Type} : Sequence 0 γ
 := ⟨ [] , by simp ⟩

lemma nil_equiv {α : Type}{t : Sequence 0 α}
   : t = .nil
   := by
   have ⟨ ls , lslen ⟩ := t
   simp
   cases ls with
   | nil => simp
   | cons _ _ => simp at lslen

@[simp]
def Sequence.single {α : Type} (a : α) : Sequence 1 α
 := .mk [a] $ by simp

@[simp]
def Sequence.cons {α : Type}{n : Nat}(a : α) : Sequence n α -> Sequence n.succ α
 := fun s => ⟨ a :: s.1 ,  by simp; exact s.2 ⟩


theorem not_nil_len {α : Type} (ls : List α)(len_nz : 0 < ls.length) : ¬ ls = .nil
  := by intro f; rw [f] at len_nz; simp at *

theorem seq_is_len {α : Type}{n : Nat} (s : Sequence n α) : s.1.length = n
  := s.2


-- Head
@[simp]
def Sequence.head {α : Type}{ n : Nat } ( seq : Sequence n.succ α) : α
  := List.head seq.1 (not_nil_len seq.1 (by rw [ seq.2 ]; simp))

@[simp]
def Sequence.head' {α : Type}{ n : Nat } ( seq : Sequence n α)(notZ : 0 < n) : α
 := List.head seq.1 (not_nil_len _ (by rw [seq.2]; exact notZ))

-- Last
-- @[simp]
def Sequence.tail {α : Type}{n : Nat} (seq : Sequence n.succ α) : Sequence n α
  :=  ⟨ List.tail seq.1 , by simp; rw [seq.2]; simp ⟩

theorem Sequence.lmm_destruct {α : Type}{n : Nat}(s : Sequence n.succ α) :
  s = .cons s.head s.tail
  := by
  revert s; cases n with
  | zero =>
    intro s; have ⟨ ls , ps ⟩ := s
    cases ls with
    | nil => simp at ps
    | cons hs tl => simp at ps; simp [Sequence.tail]
  | succ pn =>
    intro s; have ⟨ ls , ps ⟩ := s
    simp [Sequence.tail]


def Sequence.pmatch {α : Type}{n : Nat}( s : Sequence n α ) : Sequence 0 α ⊕ (α × Sequence n.pred α)
  := match n with
    | .zero => .inl .nil
    | .succ _ => .inr ( s.head, s.tail )

def Sequence.destruct {α : Type}{n : Nat}(s : Sequence n.succ α) : (α × Sequence n α)
  := ( s.head, s.tail )

def Sequence.foldr {α β : Type}{n : Nat}(f : α -> β -> β)(b : β)(sq : Sequence n α) : β
 := match n with
    | .zero => b
    | .succ _ => have ⟨ a , as ⟩ := sq.destruct; f a (as.foldr f b)

def Sequence.foldl {α β : Type}{n : Nat}(f : β -> α -> β)(b : β)(sq : Sequence n α) : β
 := match n with
    | .zero => b
    | .succ _ => sq.tail.foldl f ( f b sq.head )

--
def Sequence.tail_pred {α : Type}{n : Nat}(s : Sequence n α) : Sequence n.pred α
 := match n with
    | .zero => .nil
    | .succ _pn => s.tail

def Sequence.init {α : Type}{n : Nat}(seq : Sequence n.succ α) : Sequence n α
  := ⟨ List.take n seq.1 , by have ⟨ l , len ⟩ := seq; simp at *; omega⟩

-- def Sequence.init {α : Type}{n : Nat}(seq : Sequence n.succ α) : Sequence n α
--  := match n with
--    | .zero => .nil
--    | .succ _ => .cons seq.head $ seq.tail.init

----------------------------------------
-- ** Sequence coercions and eq
-- @[simp] -- I have defined it already hehe
def sequence_coerce {α : Type} {n m : Nat}( hEq : n = m )(s : Sequence n α) : Sequence m α
  := match n, m with
    | .zero , .zero => Sequence.nil
    | .succ _ , .succ _ => .cons s.head (sequence_coerce (by simp at hEq; assumption) s.tail)

-- Same list applies to coerce
theorem rfl_coerce {α : Type}( l r : List α )
   : l = r -> forall (n m : Nat)(lp : l.length = m)(rp : r.length = n) (heq : n = m),
              ⟨ l , lp ⟩ = sequence_coerce heq ⟨ r , rp ⟩
   := by
   intros eq n m lp rp heq
   subst_eqs
   induction l with
   | nil => simp [sequence_coerce]
   | cons x xs HInd =>
     simp [sequence_coerce]
     cases xs with
     | nil => simp [sequence_coerce]
     | cons y ys => simp [Sequence.tail]; rw [<- HInd]

theorem cons_seq_coerce {α : Type}{n m : Nat}{heq : n = m}(a : α) (seq : Sequence n α):
   .cons a (sequence_coerce heq seq)
   = sequence_coerce (by omega) (.cons a seq)
   := by
   apply rfl_coerce
   subst_eqs
   congr; symm; apply rfl_coerce; simp


lemma same_length {α : Type} {n m : Nat}(l : Sequence n α)(r : Sequence m α)
   : l.1 = r.1 -> n = m
   := by
   intro same_l; have ⟨ ls, lp ⟩ := l; have ⟨ rs, rp ⟩ := r
   simp at same_l; subst_eqs; rfl


-- Proof irrev equiv.
def beq_sequences {α : Type}[BEq α]{n : Nat} : BEq (Sequence n α) where
  beq sl sr := sl.1 == sr.1

def beq_sequences_poly {α : Type}[BEq α]{n m : Nat} (l : Sequence n α) (r : Sequence m α) : Bool
 := (n == m) && (l.1 == r.1)

-- def kyle_sequence_beq {n : Nat}{α : Type} [BEq α] (sl sr : Sequence n α) : Bool :=
--   Nat.all n (fun i iLt => sl ⟨ i , iLt ⟩ == sr ⟨ i , iLt ⟩)

-- -- Here the magic is happening at Decidable α  and the decidable_of_iff.
-- def kyle_decidable_seq {α : Type} [dec : DecidableEq α](n : Nat) : DecidableEq (Sequence n α)
--   := fun sl sr => decidable_of_iff (kyle_sequence_beq sl sr) <| by
--                       constructor
--                       case mp =>
--                         intro h
--                         apply funext
--                         simpa [kyle_sequence_beq, Nat.all_eq_finRange_all] using h
--                         -- intro x
--                         -- have xinRange := List.mem_finRange x
--                         -- apply h
--                       case mpr =>
--                         intro heq
--                         rw [heq]
--                         simp [kyle_sequence_beq, Nat.all_eq_finRange_all]
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
----------------------------------------


-- Last
@[simp]
def Sequence.last {α : Type}{n : Nat} (seq : Sequence n.succ α) : α
  := match n with
     | .zero => seq.head
     | .succ _pn => seq.tail.last

@[simp]
def lastSeq' {α : Type}{n m : Nat} (seq : Sequence n α)(ns : n = m + 1) : α
  := (sequence_coerce ns seq).last

-- def lastSeq'' {α : Type}{n : Nat} (seq : Sequence n α)(notZ : 0 < n) : α
--   := seq ⟨ n - 1, by omega ⟩
--
@[simp]
def Sequence.constant {α : Type} (n : Nat)(a : α) : Sequence n α
 := match n with
    | .zero => .nil
    | .succ pn => (Sequence.constant pn a).cons a

theorem constant_succ {α : Type}{n : Nat}{a : α}:
  Sequence.constant n.succ a = a :: Sequence.constant n a
  := by simp

@[simp]
def polyLenSeqEq {α : Type}[BEq α]{n m : Nat}(p : Sequence n α)(q : Sequence m α) : Bool
  := match n , m with
     | .zero , .zero => true
     | .succ _pn, .succ _mn =>
       if p.head == q.head
       then polyLenSeqEq p.tail q.tail
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
            exact @HInd pn p.tail q.tail rsEq

theorem seqEqLawRfl {α : Type}[BEq α][LawfulBEq α]{n : Nat}(p : Sequence n α)
  : polyLenSeqEq p p
  := by
   revert p
   induction n with
   | zero => intro _p; simp
   | succ pn HInd => intro p; simp; apply HInd

def zip_succ_int {α : Type}{n : Nat}
  (h : α) (seq : Sequence n.succ α) : Sequence n.succ (α × α)
  := match n with
    | .zero => .single ( h, seq.head)
    | .succ _ => Sequence.cons (h, seq.head) $ zip_succ_int seq.head seq.tail

def zip_succ {α : Type}{n : Nat}
  (seq : Sequence n.succ.succ α) : Sequence n.succ (α × α)
  := zip_succ_int seq.head seq.tail

-- Append
@[simp]
def Sequence.append {α : Type}{n m : Nat}(p : Sequence n α)(q : Sequence m α) : Sequence (n + m) α
 := ⟨ p.1.append q.1 , by simp; rw [p.2, q.2] ⟩

@[simp]
def Sequence.snoc {α : Type}{n : Nat}(seq : Sequence n α)(a : α) : Sequence n.succ α
  := seq.append (.single a)
  -- fun ⟨ x , _xLT ⟩ => if H : x < n then seq ⟨ x , H ⟩ else a

-- R Access
@[simp]
def Sequence.getI {α : Type}{n: Nat}(seq : Sequence n α)(i : Nat)(iLTn : i < n) : α
 := match i with
   | .zero => seq.head' iLTn
   | .succ pn => @getI _ n.pred seq.tail_pred pn (by rw [Nat.lt_pred_iff_succ_lt]; assumption)

@[simp]
def desc_Seq {n : Nat}{α : Type} (seq : Sequence n.succ α) : α × Sequence n α
 := (seq.head , seq.tail)

-- Map
@[simp]
def Sequence.map {α β : Type} {n : Nat} (f : α -> β) ( seq : Sequence n α ) : Sequence n β
  := ⟨ seq.1.map f, by simp; exact seq.2⟩

lemma map_tail {α β : Type}{n : Nat} (f : α -> β) ( seq : Sequence n.succ α ) :
   (seq.map f).tail = seq.tail.map f
   := by simp [Sequence.map, Sequence.tail]

@[simp]
def Sequence.zip_with {α β ε : Type}{n : Nat}
    (f : α -> β -> ε)
    (sl : Sequence n α)
    (sr : Sequence n β)
    : Sequence n ε
    := match n with
    | .zero => .nil
    | .succ _ => .cons (f sl.head sr.head) $ Sequence.zip_with f sl.tail sr.tail

def Sequence.nats' {n : Nat}(start : Nat): Sequence n Nat
 := match n with
   | .zero => .nil
   | .succ _ => .cons start $ Sequence.nats' start.succ

def Sequence.nats {n : Nat} : Sequence n Nat
 := Sequence.nats' 0

@[simp]
def Sequence.imap {α β : Type} {n : Nat} (f : Nat -> α -> β) ( seq : Sequence n α ) : Sequence n β
  := seq.zip_with (flip f) .nats

-- Reverse
-- @[simp]
def Sequence.reverse {α : Type} {n : Nat} (seq : Sequence n α) : Sequence n α
  := ⟨ seq.1.reverse , by simp; rw [seq.2] ⟩

-- theorem Fin.snoc_head {α : Type}{ n : Nat }
--    ( seq : Sequence n.succ α )(lt : α)
--    : (seq.snoc lt).head = seq.head
--    := sorry

-- Take
@[simp]
def Sequence.take {α : Type}{n : Nat}(m : Nat)(mLTn : m ≤ n)(s : Sequence n α) : Sequence m α
 := ⟨ List.take m s.1 , by simp; rwa [s.2] ⟩

-- Drop
@[simp]
def Sequence.drop {α : Type}{n : Nat}(m : Nat)(s : Sequence n α) : Sequence (n - m) α
 := ⟨ List.drop m s.1 , by simp; rw [s.2]⟩

-- SplitAt
def Sequence.split {α : Type}{n : Nat}(p : Sequence n α)(m : Nat)(mLTn : m ≤ n): Sequence m α × Sequence (n - m) α
  := ⟨ .take m mLTn p , .drop m p ⟩

-- Join
def Sequence.join {α : Type}{n : Nat}
  (f : α -> α -> α)
  (seq : Sequence (2*n) α)
  : Sequence n α
  := match n with
    | .zero => .nil
    | .succ _ =>
      .cons (f seq.head seq.tail.head) $ Sequence.join f (.tail $ .tail seq)

-- Power Nats
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
  := (seq.take n (by omega) , sequence_coerce (by omega) $ seq.drop n)

def half_split_pow {α : Type}{n : Nat}(seq : Sequence (2^n.succ) α)
  : Sequence (2^n) α × Sequence (2^n) α
  := (.take (2^n) (by have pg := @pow_gt_zero n; omega) seq
  , sequence_coerce (by have pg := @pow_gt_zero n;omega) $ .drop (2^n) seq)

def Sequence.consume_pow {α : Type}{lgn : Nat}
  (f : α -> α -> α)
  (seq : Sequence (2^lgn) α)
  : α
  := match lgn with
    | .zero => seq.head
    | .succ plgn => Sequence.consume_pow f
      $ Sequence.join f
      $ @sequence_coerce _ _ (2 * 2^plgn) (by simp; rw [Nat.pow_add]; simp;omega) seq

def Sequence.perfect_split {α : Type}{n : Nat}(seq : Sequence ((2^n.succ) - 1) α)
  : ( Sequence ((2^n) - 1) α × α × Sequence ((2^n) - 1) α)
  := have ( seql , hdseqr ) := seq.split ((2^n) - 1) (by simp; omega)
    ( seql
    , hdseqr.head' (by simp;have ps :=@pow_geq_one n; omega)
    , Sequence.tail (sequence_coerce (by rw [pp2]; have ps :=@pow_geq_one n; omega) hdseqr))


def sequence_forget {α : Type}{n : Nat} (seq : Sequence n α) : List α
  := seq.1

----------------------------------------
-- * Theorems and stuff
--
theorem split_seq_eq {α : Type}{n m : Nat}{ mLTn : m ≤ n }( seq : Sequence n α ):
  have ⟨ seql , seqr ⟩ := seq.split m mLTn
  seq = sequence_coerce (by omega) (seql.append seqr)
  := by
  have ⟨ ls, lp ⟩ := seq
  apply rfl_coerce
  simp

theorem ExtraCoerce {α : Type}{n : Nat}(req : n = n)(seq : Sequence n α)
        : seq = sequence_coerce req seq
        := by apply rfl_coerce; rfl

theorem coerce_trans {α : Type}{n m l : Nat}{fst : n = m}{snd : m = l}
      (seq : Sequence n α):
      sequence_coerce snd (sequence_coerce fst seq)
      = sequence_coerce (by omega) seq
      := by subst_eqs
            congr
            symm
            apply rfl_coerce
            simp

theorem coerce_eq_comm {α : Type}{n m : Nat}
        {heq : n = m}
        (seql : Sequence n α)(seqr : Sequence m α)
        : sequence_coerce heq seql = seqr
        -> seql = sequence_coerce (by rw [Eq.comm] at heq; assumption ) seqr
        := by intro H; rw [ <- H]; rw [ coerce_trans ]; apply rfl_coerce; simp

theorem coerce_eq_comm' {α : Type}{n m : Nat}
        {heq : m = n}
        (seql : Sequence n α)(seqr : Sequence m α)
        : seql = sequence_coerce heq seqr
        -> sequence_coerce (by omega) seql = seqr
        := by intro H; rw [H, coerce_trans]; symm; apply rfl_coerce; simp

theorem coerce_eq_coerce { α : Type }{n m l : Nat}
        {reql : n = l}{reqr : m = l}
        (seql : Sequence n α)(seqr : Sequence m α)
        : sequence_coerce reql seql = sequence_coerce reqr seqr
        -> sequence_coerce (by omega) seql = seqr
        := by intro H; apply coerce_eq_comm' at H
              rw [<- H]
              subst_eqs
              rw [coerce_trans]

theorem rfl_coerce_up {α : Type}{n m: Nat}{meq : n = m}(ls : List α){lp : ls.length = n}
  : ls = (sequence_coerce meq ⟨ ls , lp ⟩ )
  := by
  revert lp ls meq m
  induction n with
  | zero =>
    intros m meq ls lp
    unfold sequence_coerce
    subst_eqs
    simp; cases ls with
    | nil => rfl
    | cons => simp at lp
  | succ pn HInd =>
    intros m meq ls lp
    subst_eqs
    unfold sequence_coerce
    simp [Sequence.tail]
    have lrest := @HInd pn rfl (List.tail ls) (by simp; omega)
    rw [<- lrest]
    simp

theorem TailCoerDrop {α : Type}{n m : Nat}(d : Nat){heq : n - d = m + 1}(seq : Sequence n α):
   .tail (sequence_coerce heq ( .drop d seq ))
   = sequence_coerce (by omega) (.drop d.succ seq)
   := by
    simp [Sequence.tail]; apply rfl_coerce
    have ⟨ ls , lp ⟩ := seq
    simp
    subst_eqs
    rw [ <- List.tail_drop ]
    congr
    symm
    apply rfl_coerce_up

theorem TakeCoerce {α : Type}{n m k : Nat}{kLT : k ≤ n} (heq : k = m)  (seq : Sequence n α):
  sequence_coerce heq (Sequence.take k kLT seq)
  = Sequence.take m (by rw [<- heq]; assumption) seq
  := by subst_eqs; simp; rw [<- rfl_coerce ]; simp
