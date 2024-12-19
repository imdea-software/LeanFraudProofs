import FraudProof.DataStructures.Value
import FraudProof.DataStructures.MTree
import FraudProof.DataStructures.Hash
import FraudProof.DataStructures.Sequence

import Mathlib.Data.Sum.Basic

----------------------------------------
section ValHash
  variable { α ℍ : Type }
  def hashElem [Hash α ℍ][HashMagma ℍ] : BTree α ⊕ BTree α → PathElem ℍ:=
    let hashTree := ( MTree.hash ∘ hash_BTree )
    Sum.map  hashTree hashTree

  def propTree [m : Hash α ℍ][o : HashMagma ℍ] : BTree α  -> ABTree (α × ℍ) (ℍ × ℍ × ℍ)
  | .leaf v => .leaf ⟨ v , m.mhash v ⟩
  | .node bl br =>
    let abl := propTree bl
    let h1 := ABTree.getI' (fun e => e.2) (fun e => e.1) abl
    let abr := propTree br
    let h2 := ABTree.getI' (fun e => e.2) (fun e => e.1) abr
    .node ⟨ o.comb h1 h2 , h1 , h2 ⟩  abl abr

  theorem propTreeLeaf [m : Hash α ℍ][HashMagma ℍ]( t : BTree α )(v : α)(h : ℍ)
     : propTree t = .leaf ( v , h ) -> m.mhash v = h
     := by cases t with
           | leaf x => simp [propTree]; intros heq meq; rw [<- meq, heq]
           | node bl br => simp [propTree]

  def medTrees [m : Hash α ℍ][o : HashMagma ℍ] (t : BTree α) : ABTree (α × ℍ) ℍ
  := (@propTree _ _ m o t).map id (fun p => p.1)

  -- Accessing Indexed MMTrees
  structure NData (α β : Type)  where
    nodeI : β
    sL : Nat
    sR : Nat
    lL : Nat
    lR : Nat
    leftI : MMTree α β sL lL
    rightI : MMTree α β sR lR
    -- We also have proofs
    sbot : Nat
    sbotP : min sL sR = sbot
    ltop : Nat
    ltopP : max lL lR = ltop



  structure LData (α β : Type) where
    ldata : α
    leafI : β

  -- def IdxMMTreeI {α β : Type}{s l c : Nat}
  --   ( _cLeqs : c ≤ s )
  --   (d : MMTree α β s l)
  --   (skl : ISkeleton c)
  --   : (LData α β) ⊕ (NData α β)
  -- := match s , d with
  -- | 0  , .leaf v i => .inl ⟨ v , i ⟩
  -- | .succ pn , @MMTree.node _ _ sL sR lL lR sB lT i pB pT bl br =>
  --   match c with
  --   | 0 => .inr ⟨ i , l.getI , r.getI ⟩
  --   | .succ pc => match skl ⟨ 0 , by simp ⟩ with
  --     | .inl _ => IdxMMTreeI (by omega) l $ Fin.tail skl
  --     | .inr _ => IdxMMTreeI (by omega) r $ Fin.tail skl


  ----------------------------------------
  -- Tree Path to Hash Path
  @[simp]
  def treeTohashPath [Hash α ℍ][HashMagma ℍ]: TreePath α → Path ℍ :=
    List.map hashElem

  @[simp]
  lemma TreeLenEq [h : Hash α ℍ][o : HashMagma ℍ](path : TreePath α)
    : (@treeTohashPath _ _ h o path).length = path.length
    := by exact List.length_map _ _

  lemma RevTreeLenEq [h : Hash α ℍ][o : HashMagma ℍ]( path : TreePath α )
    : (@treeTohashPath _ _ h o path).reverse.length = path.length
    := by simp


  -- Theorems
  theorem VinTree
          [BEq α]
          [LawfulBEq α]
          [h : Hash α ℍ]
          [HashMagma ℍ]
          (v : α)
          (btree : BTree α)
          (path : TreePath α)
          (vInTree : valueInProof v btree = some path)
          : List.foldl opHash (h.mhash v) (List.map hashElem path)
            = (hash_BTree btree).hash :=
  by
    revert vInTree path
    induction btree with
    | leaf w =>
      intros path vInTree
      simp [valueInProof] at vInTree
      have pathE := vInTree.right
      rw [ pathE ]
      simp [hash_BTree, MTree.hash]
      have vwEq := vInTree.left
      congr
    | node bL bR HL HR =>
      intros path vInPath
      simp [valueInProof] at vInPath
      -- v is in Left or righ.
      cases vInL : valueInProof v bL with
      -- v is in bL
      | some ps =>
        simp [vInL] at vInPath
        have HLV := HL ps vInL
        simp [hash_BTree, comb_MTree]
        rw [ <- vInPath ]
        simp
        rw [ HLV ]
        unfold hashElem
        simp [opHash, MTree.hash]
      | none => -- v not in bL
          cases vInR : valueInProof v bR with
          | some ps =>
                simp [vInL, vInR] at vInPath
                have HLR := HR ps vInR
                rw [ <- vInPath ]
                simp
                rw [ HLR ]
                simp [ hashElem, opHash, MTree.hash, hash_BTree, comb_MTree]
          | none => -- impossible
                simp [vInL, vInR] at vInPath
end ValHash
----------------------------------------

def IndexABTreeI {α β : Type}{n : Nat} (path : ISkeleton n)(t : ABTree α β)
  : Option (α ⊕ (β × ABTree α β × ABTree α β))
  := match n , t with
    --
    | .zero , .leaf v => some $ .inl v
    | .zero , .node b bl br => some $ .inr ⟨ b , ⟨ bl , br ⟩ ⟩
    --
    | .succ _pn , .node _b bl br =>
       match headSeq path with
       | .inl _ => IndexABTreeI (Fin.tail path) bl
       | .inr _ => IndexABTreeI (Fin.tail path) br
    --
    | .succ _pn , .leaf _ => none

theorem indexRoot {α β : Type}(t : ABTree α β)(x : α)
 : IndexABTreeI nilSeq t = some (.inl x) -> t = .leaf x
 := by cases t with
   | leaf v => simp [IndexABTreeI]
   | node ix bl br => simp [IndexABTreeI]

theorem skipElem {α β : Type} {n : Nat}(path : ISkeleton n)(nInfo : β)(bl br : ABTree α β)
   (elem : α)
   (hIdx : IndexABTreeI (Fin.cons (.inl ()) path) (ABTree.node nInfo bl br) = some (Sum.inl elem))
   : IndexABTreeI path bl = some (.inl elem)
   := by simp [IndexABTreeI] at hIdx; assumption

theorem skipElemL {α β : Type} {n : Nat}(path : ISkeleton n.succ) (nInfo : β)(bl br : ABTree α β)
  (elem : α)
  (seqP : path 0 = .inl ())
  (hIdx : IndexABTreeI path (ABTree.node nInfo bl br) = some (Sum.inl elem))
  : IndexABTreeI (Fin.tail path) bl = some (.inl elem)
  := by simp [IndexABTreeI] at hIdx; rw [seqP] at hIdx; simp at *; assumption

theorem skipElemR {α β : Type} {n : Nat}(path : ISkeleton n.succ) (nInfo : β)(bl br : ABTree α β)
  (elem : α)
  (seqP : path 0 = .inr ())
  (hIdx : IndexABTreeI path (ABTree.node nInfo bl br) = some (Sum.inl elem))
  : IndexABTreeI (Fin.tail path) br = some (.inl elem)
  := by simp [IndexABTreeI] at hIdx; rw [seqP] at hIdx; simp at *; assumption

def BStrategies {α β γ : Type} {n : Nat}
  (inlA : α -> γ) (inlB : β -> γ)
  (path : ISkeleton n) (t : ABTree α β)
  -- Such that path goes to an element
  (elem : α)
  (hIdx : IndexABTreeI path t = some (.inl elem))
  : (Fin n.succ -> γ) × (Fin n -> PathElem γ)
  := match n , t with
     | .zero , .leaf _v => ⟨ Fin.cons (inlA elem) nilSeq , nilSeq ⟩
     | .succ _pn , .node iN bl br =>
       match H : headSeq path with
       | .inl _ =>
          let recCall := BStrategies inlA inlB (Fin.tail path) bl elem (by simp [IndexABTreeI] at *; rw [ H ] at hIdx; simp at hIdx; assumption)
          ⟨ Fin.snoc recCall.1 (inlB iN) , Fin.snoc recCall.2 (.inr (br.getI' inlA inlB)) ⟩
       | .inr _ =>
          let recCall := BStrategies inlA inlB (Fin.tail path) br elem (by simp [IndexABTreeI] at *; rw [ H ] at hIdx; simp at hIdx; assumption)
          ⟨ Fin.snoc recCall.1 (inlB iN) , Fin.snoc recCall.2 (.inl (bl.getI' inlA inlB)) ⟩


theorem spineHashProp {α ℍ : Type} {n : Nat}[hash : Hash α ℍ] [mag : HashMagma ℍ]
   (data : BTree α)(path : ISkeleton n)
   (elem : α)
   --
   (hIdx : IndexABTreeI path (@propTree _ _ hash mag data) = some (.inl ⟨ elem , hash.mhash elem ⟩))
   --
   : ABTree.getI' (fun e => e.2) (fun e => e.1) (@propTree _ _ hash mag data) =
     (BStrategies (fun e => e.2) (fun e => e.1) path (@propTree _ _ hash mag data) ⟨ elem , hash.mhash elem ⟩ hIdx).1 (Fin.last n)
   := by
    induction n with
    | zero => cases data with
              | leaf v =>
                     simp [propTree, IndexABTreeI] at hIdx; simp [propTree,BStrategies, ABTree.getI', nilSeq]
                     have ⟨ _eqVElem , rest ⟩ := hIdx
                     assumption
              | node bl br => simp [IndexABTreeI] at hIdx
    | succ pn HInd =>
      cases data with
      | leaf v => simp [IndexABTreeI] at hIdx
      | node bl br =>
        simp [BStrategies]
        split
        { case succ.node.h_1 HEq =>
          simp [propTree]
          congr
        }
        { case succ.node.h_2 HEq =>
          simp [propTree]
          congr
        }

theorem allGamesStrategies {α ℍ : Type}{n : Nat} [hash : Hash α ℍ] [mag : HashMagma ℍ]
  -- (inlA : α -> ℍ) (inlB : β -> ℍ)
  (data : BTree α)
  (path : ISkeleton n) -- (t : ABTree α β)
  -- Such that path goes to an element
  (elem : α)
  -- IndexTree path data = elem
  (hIdx : IndexABTreeI path (@propTree _ _ hash mag data) = some (.inl ⟨ elem , hash.mhash elem ⟩))
  : forall (m : Nat)(mLtn : m < n),
    have strs := BStrategies (fun e => e.2) (fun e => e.1) path (@propTree _ _ hash mag data) ⟨ elem , hash.mhash elem ⟩ hIdx
    strs.1 ⟨ m.succ , by omega ⟩ =
    opHash ( strs.1 ⟨ m , by omega ⟩ ) ( strs.2 ⟨ m , mLtn ⟩ )
  := by
  revert n path elem hIdx
  induction data with
  | leaf v =>
     intros n path elem hInd m mLTn
     cases n with
     | zero => simp at mLTn
     | succ pn => simp [IndexABTreeI] at hInd
  | node bl br BLInd BRInd =>
    intros n path elem hInd m mLTn
    -- simp [BStrategies]
    cases n with
    | zero => simp at mLTn
    | succ pn =>
      simp [BStrategies]
      split
      { case node.succ.h_1 heq =>
        clear BRInd
        simp [Fin.snoc]
        split
        { case isTrue H =>
          replace BLInd := @BLInd pn (Fin.tail path) elem (by simp [IndexABTreeI] at hInd; rw [heq] at hInd;simp at hInd;assumption) m H
          simp at BLInd
          assumption
        }
        { case isFalse H =>
          have heqn : m = pn := by omega
          simp [opHash]
          congr
          have sp := @spineHashProp _ _ _ hash mag bl (Fin.tail path) elem (by simp [IndexABTreeI] at hInd; rw [heq] at hInd;simp at hInd;assumption)
          simp [Fin.last] at sp
          rw [sp]
          apply congr_arg; apply Fin.eq_of_val_eq
          simp
          rw [heqn]
        }
      }
      { case node.succ.h_2 heq =>
        clear BLInd
        simp [Fin.snoc]
        split
        { case isTrue H =>
          replace BRInd := @BRInd pn (Fin.tail path) elem (by simp [IndexABTreeI] at hInd; rw [heq] at hInd;simp at hInd;assumption) m H
          simp at BRInd
          assumption
        }
        { case isFalse H =>
          have heqn : m = pn := by omega
          simp [opHash]
          congr
          -- current hash is fold path.
          have sp := @spineHashProp _ _ _ hash mag br (Fin.tail path) elem (by simp [IndexABTreeI] at hInd; rw [heq] at hInd;simp at hInd;assumption)
          rw [sp]
          apply congr_arg; apply Fin.eq_of_val_eq
          simp
          rw [heqn]
        }
      }

theorem elem0 { α β γ: Type }{n : Nat}
    {inlA : α -> γ} {inlN : β -> γ}
    (path : ISkeleton n)(t : ABTree α β)
    (e : α)( hIdx : IndexABTreeI path t = some (.inl e))
    --
    : (BStrategies inlA inlN path t e hIdx).1 0 = inlA e
    := by revert t e
          induction n with
          | zero => intros  t elem hIdx
                    cases t with
                      | leaf _v =>
                        simp [BStrategies]
                      | node _ _ _ => -- Empty case
                        simp [IndexABTreeI] at hIdx
          | succ _pn HInd =>
            intros t elem hIdx
            -- simp [BStrategies]
            cases t with
            | node b bl br =>
              simp [BStrategies]
              simp [IndexABTreeI] at hIdx
              split
              { case succ.node.h_1 hyp =>
                  simp at *
                  simp [Fin.snoc, Fin.castLT]
                  rw [hyp] at hIdx; simp at hIdx
                  have hI := HInd (Fin.tail path) bl elem hIdx
                  assumption
              }
              { case succ.node.h_2 hyp =>
                simp at *
                simp [Fin.snoc, Fin.castLT]
                rw [hyp] at hIdx; simp at hIdx
                have hI := HInd (Fin.tail path) br elem hIdx
                assumption
              }
            | leaf _v => simp [IndexABTreeI] at hIdx


@[simp]
def MBuildStrategies {α β γ : Type}{n : Nat}
  (inlA : α -> γ) (inlB : β -> γ)
  -- (inlN : β × γ × γ -> γ)
  (path : ISkeleton n) (t : ABTree α β)
  : Option ((Fin n.succ -> γ) × (Fin n -> PathElem γ))
 := match n , t with
  -- Element at point path is leading us.
  | .zero, pEnd => some ⟨ Fin.cons (pEnd.getI' inlA inlB) nilSeq , nilSeq ⟩
  -- Following the path
  | .succ _pn , .node i bl br =>
    match headSeq path with
     | .inl _ => (fun ⟨ sp , si ⟩ => ⟨ Fin.snoc sp (inlB i) , Fin.snoc si (.inl (bl.getI' inlA inlB))⟩)
       <$> MBuildStrategies inlA inlB  (Fin.tail path) bl
     | .inr _ => (fun ⟨ sp , si ⟩ => ⟨ Fin.snoc sp (inlB i) , Fin.snoc si (.inl (br.getI' inlA inlB))⟩)
     <$> MBuildStrategies inlA inlB  (Fin.tail path) br
  -- Skeleton path is longer than path in tree.
  | .succ _ , .leaf _ => none


def SpineCollect {α β γ : Type}{n : Nat}
   (injL : α -> γ)(injN : β -> γ)
   (t : ABTree α β)(p : ISkeleton n)
   : Option (Fin n.succ -> γ)
  := match n , t with
  -- Path leads to |pEnd|
  | 0 , pEnd => some $ Fin.cons (pEnd.getI' injL injN) nilSeq
  -- Following the path
  | .succ pn , .node i bl br =>
    (Fin.cons (injN i)) <$>
    match p ⟨ 0 , by simp ⟩ with
    | .inl _ => SpineCollect injL injN bl (Fin.tail p)
    | .inr _ => SpineCollect injL injN br (Fin.tail p)
  -- Skeleton path is longer than path in tree.
  | .succ _ , .leaf _ => none

def SibilingCollect {α β γ : Type}{n : Nat}
   (injL : α -> γ)(injN : β -> γ)
   (t : ABTree α β)(p : ISkeleton n)
   : Option (Fin n -> PathElem γ)
  := match n , t with
  -- Path finished
  | 0 , _ => some nilSeq
  -- Following the path
  | .succ pn , .node _i bl br =>
    match p ⟨ 0 , by simp ⟩ with
    | .inl _ => Fin.cons (.inl $ bl.getI' injL injN) <$> SibilingCollect injL injN bl (Fin.tail p)
    | .inr _ => Fin.cons (.inr $ bl.getI' injL injN) <$> SibilingCollect injL injN br (Fin.tail p)
  -- Skeleton path is longer than path in tree.
  | .succ _ , .leaf _ => none

def OBCollectI {α β γ : Type}{n : Nat}
    (inj : (β -> γ))
    (p : ISkeleton n)
    (t : ABTree α β)
  : Option ( (Fin n -> γ) × (α ⊕ (β × ABTree α β × ABTree α β)))
  := match n , t with
  | 0 , .leaf v => some $ ⟨ nilSeq , .inl v⟩
  | 0 , .node i bl br => some $ ⟨ nilSeq ,  .inr ⟨ i , bl , br ⟩ ⟩
  -- Following the path
  | .succ pn , .node i bl br =>
    (fun ⟨ p, res ⟩ => ⟨ Fin.cons (inj i) p , res ⟩) <$>
    match p ⟨ 0 , by simp ⟩ with
    | .inl _ => OBCollectI inj (Fin.tail p) bl
    | .inr _ => OBCollectI inj (Fin.tail p) br
  -- Skeleton path is longer than path in tree.
  | .succ _ , .leaf _ => none

def OBCollect {α β γ : Type} (inj : (β -> γ))
  : (p : Skeleton) -> ABTree α β
  -> Option ( (Fin p.length -> γ)
            × (α ⊕ (β × ABTree α β × ABTree α β)))
  -- Element at point path is leading us.
  | .nil , .leaf v => some $ ⟨ nilSeq , .inl v⟩
  | .nil , .node i bl br => some $ ⟨ nilSeq ,  .inr ⟨ i , bl , br ⟩ ⟩
  -- Following the path
  | .cons (.inl _) sks , .node i bl _ =>
    (fun ⟨ p , res ⟩ => ⟨ Fin.cons (inj i) p , res ⟩) <$> OBCollect inj sks bl
  | .cons (.inr _) sks , .node i _ br =>
    (fun ⟨ p , res ⟩ => ⟨ Fin.cons (inj i) p , res ⟩) <$> OBCollect inj sks br
  -- Skeleton path is longer than path in tree.
  | .cons _ _ , .leaf _ => none


-- Helper Function creating path from skeleton in a tree.
def IdxCollectABTree {α β γ : Type} (inj : (α -> γ) × (β -> γ))
  : (p : Skeleton) -> ABTree α β
  -> Option ( (Fin p.length -> (γ × γ))
            × (α ⊕ (β × ABTree α β × ABTree α β)))
  -- Element at point path is leading us.
  | .nil , .leaf v => some $ ⟨ nilSeq , .inl v⟩
  | .nil , .node i bl br => some $ ⟨ nilSeq ,  .inr ⟨ i , bl , br ⟩ ⟩
  -- Following the path
  | .cons (.inl _) sks , .node _i bl br =>
    (fun ⟨ p , res ⟩ => ⟨ Fin.cons ⟨ bl.getI' inj.1 inj.2 , br.getI' inj.1 inj.2 ⟩ p , res ⟩) <$> IdxCollectABTree inj sks bl
  | .cons (.inr _) sks , .node _i bl br =>
    (fun ⟨ p , res ⟩ => ⟨ Fin.cons ⟨ bl.getI' inj.1 inj.2 , br.getI' inj.1 inj.2 ⟩ p , res ⟩) <$> IdxCollectABTree inj sks br
  -- Skeleton path is longer than path in tree.
  | .cons _ _ , .leaf _ => none


----------------------------------------
-- Adding path to node?
def ABTree.InjPath' {α β : Type} (p : Skeleton) : ABTree α β -> ABTree (α × Skeleton) (β × Skeleton)
  | .leaf v => .leaf ⟨ v , p ⟩
  | .node b bl br => .node ⟨ b , p ⟩ ( ABTree.InjPath' (p ++ [ .inl () ]) bl) ( ABTree.InjPath' (p ++ [ .inr () ]) br)

def ABTree.InjPath {α β : Type} : ABTree α β -> ABTree (α × Skeleton) (β × Skeleton)
  := ABTree.InjPath' []

-- theorem ABTree.map t.InjPath Prod.1 Prod.1 = t
-- theorem ABTree.I t pos = some _ => ABTree.I (t.InjPath) pos = some (_ × pos)

-- Forgeting and then adding path
def ABTree.TSkeleton' {α β : Type} (t : ABTree α β) : ABTree (Unit × Skeleton) (Unit × Skeleton)
  := t.forget.InjPath

-- Adding Path and Forgetting
def ABTree.TSkeleton {α β : Type} : ABTree α β -> ABTree Skeleton Skeleton
  := ABTree.map (fun p => p.2) (fun p => p.2) ∘ ABTree.InjPath

def IndexBTreeI {α : Type}{n : Nat} (path : ISkeleton n)(t : BTree α) : Option (α ⊕ (BTree α × BTree α))
 := match n , t with
  -- Element at point path is leading us.
  | .zero , .leaf v => some $ .inl v
  | .zero , .node bl br => some $ .inr ⟨ bl , br ⟩
  -- Following the path
  | .succ _pn , .node bl br =>
    match headSeq path with
     | .inl _ => IndexBTreeI (Fin.tail path) bl
     | .inr _ => IndexBTreeI (Fin.tail path) br
  -- Skeleton path is longer than path in tree.
  | .succ _ , .leaf _ => none


def IndexBTree {α : Type} : Skeleton -> BTree α -> Option (α ⊕ (BTree α × BTree α))
  -- Element at point path is leading us.
  | .nil , .leaf v => some $ .inl v
  | .nil , .node bl br => some $ .inr ⟨ bl , br ⟩
  -- Following the path
  | .cons (.inl _) sks , .node bl _ => IndexBTree sks bl
  | .cons (.inr _) sks , .node _ br => IndexBTree sks br
  -- Skeleton path is longer than path in tree.
  | .cons _ _ , .leaf _ => none

def ABTree.getHash {α ℍ : Type} ( t : ABTree (α × ℍ) (ℍ × ℍ × ℍ)) :  ℍ
  := t.getI' (fun f => f.2) (fun f => f.1)

theorem getHashPropNode {α ℍ : Type}[Hash α ℍ][m : HashMagma ℍ](bl br : BTree α)
  : (propTree (bl.node br)).getHash = m.comb (propTree bl).getHash (propTree br).getHash
  := by simp [propTree,ABTree.getHash,ABTree.getI']

theorem sizeIBTree {α : Type}(skl : Skeleton) :
  forall ( t cl cr : BTree α ),
  IndexBTree skl t = some (.inr ⟨ cl , cr⟩)
  -> sizeOf cl < sizeOf t ∧ sizeOf cr < sizeOf t
  := by induction skl with
   | nil =>
      intros t cl cr a
      cases t with
      | leaf v =>
        simp [IndexBTree] at a
      | node kl kr =>
        simp [IndexBTree] at *
        have al := a.1
        have ar := a.2
        exact ⟨ by rw [al]; omega , by rw [ar]; omega ⟩
   | cons s sks HI =>
      intros t cl cr H
      cases t with
      -- Imp case
      | leaf _ => simp [IndexBTree] at *
      --
      | node kl kr =>
        cases s with
        | inl _ =>
          simp [IndexBTree] at H
          have indI := HI kl cl cr H
          simp; omega
        | inr _ =>
          simp [IndexBTree] at H
          have indI := HI kr cl cr H
          simp; omega

----------------------------------------

----------------------------------------
def sumP {α : Type}  : Sum α α → α := (Sum.elim id id)

-- PathComputation v p = List.drop 1 (ScanPath v p)
@[simp]
def ScanPath {ℍ : Type}[HashMagma ℍ] ( v : ℍ ) ( path : Path ℍ) : List ℍ
:= List.scanl opHash v path
