import FraudProof.DataStructures.Value
import FraudProof.DataStructures.MTree
import FraudProof.DataStructures.Hash

import Mathlib.Data.Sum.Basic
import Mathlib.Data.Fin.Tuple.Basic -- Fin.tail

section ValHash
  variable { α ℍ : Type }
  def hashElem [Hash α ℍ][HashMagma ℍ] : BTree α ⊕ BTree α → PathElem ℍ:=
    let hashTree := ( MTree.hash ∘ hash_BTree )
    Sum.map  hashTree hashTree


  def IndexBTree {α : Type} : Skeleton -> BTree α -> Option (α ⊕ (BTree α × BTree α))
  | .nil , .leaf v => some $ .inl v
  | .nil , .node bl br => some $ .inr ⟨ bl , br ⟩
  | .cons (.inl _) sks , .node bl _ => IndexBTree sks bl
  | .cons (.inr _) sks , .node _ br => IndexBTree sks br
  -- Skeleton path is longer than path in tree.
  | .cons _ _ , .leaf _ => none

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


  --- Computing intermediary trees.
  def medTrees [m : Hash α ℍ][o : HashMagma ℍ] : BTree α -> ABTree α ℍ
  | .leaf v => .leaf (m.mhash v) v
  | .node bl br =>
    let abl := medTrees bl
    let abr := medTrees br
    .node (o.comb abl.getI abr.getI) abl abr

  def medITrees [m : Hash α ℍ][o : HashMagma ℍ]{n : Nat} : ITree α n -> STree α ℍ n
  | .leaf v _ => .leaf v (m.mhash v)
  | .nodeL _ p bl br =>
    let abl := medITrees bl
    let abr := medITrees br
    .nodeL (o.comb abl.getI abr.getI) p abl abr
  | .nodeR _ p bl br =>
    let abl := medITrees bl
    let abr := medITrees br
    .nodeR (o.comb abl.getI abr.getI) p abl abr

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
      rw [ <- pathE ]
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

----------------------------------------
def sumP {α : Type}  : Sum α α → α := (Sum.elim id id)

-- PathComputation v p = List.drop 1 (ScanPath v p)
@[simp]
def ScanPath {ℍ : Type}[HashMagma ℍ] ( v : ℍ ) ( path : Path ℍ) : List ℍ
:= List.scanl opHash v path
