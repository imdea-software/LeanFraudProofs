import FraudProof.Value
import FraudProof.MTree
import FraudProof.Hash

import Mathlib.Data.Sum.Basic

def hashElem : BTree Value ⊕ BTree Value  → PathElem :=
  let hashTree := ( MTree.hash ∘ hash_BTree )
  Sum.map  hashTree hashTree

----------------------------------------
-- Tree Path to Hash Path
@[simp]
def treeTohashPath : TreePath Value  → Path :=
  List.map hashElem

@[simp]
lemma TreeLenEq (path : TreePath Value)
  : (treeTohashPath path).length = path.length
  := by exact List.length_map _ _

lemma RevTreeLenEq ( path : TreePath Value )
  : (treeTohashPath path).reverse.length = path.length
  := by simp

----------------------------------------


def sumP {α : Type}  : Sum α α → α := (Sum.elim id id)

-- PathComputation v p = List.drop 1 (ScanPath v p)
@[simp]
def ScanPath ( v : Hash ) ( path : Path ) : List Hash
:= List.scanl opHash v path


-- Theorems
theorem VinTree
        (v : Value)
        (btree : BTree Value)
        (path : TreePath Value)
        (vInTree : valueInProof v btree = some path)
        : List.foldl opHash (H v) (List.map hashElem path)
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
    rw [ vwEq ]
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
