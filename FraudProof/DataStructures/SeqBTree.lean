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
        | .node a bl br => concatSeq (eqLength (Fin.snoc (infixSeq bl) a) (by simp; omega ) ) (infixSeq br)

def maybeSizeTree {α β : Type} : ABTree (Option α) β -> Nat
  := ABTree.sizeI  (fun x => match x with | none => 0 | some _ => 1) (fun _ => 1)

-- the problem here is that there may not be enough element in the sequence.
def seqToABTree {α : Type}{n : Nat} (seq : Sequence n α)(_pos : n > 0) : ABTree (Option α) α
  := _
